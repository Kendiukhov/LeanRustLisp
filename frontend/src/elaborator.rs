use crate::surface::{Span, SurfaceTerm, SurfaceTermKind};
use kernel::ast::{DefId, FunctionKind, Level, MarkerId, Term, TypeMarker};
use kernel::checker::{
    check_elimination_restriction, compute_recursor_type, infer as infer_type, Context, Env,
    TypeError,
};
use kernel::ownership::{CaptureModes, UsageMode};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use thiserror::Error;

const CODE_ELAB_UNBOUND_VAR: &str = "F0200";
const CODE_ELAB_UNKNOWN_INDUCTIVE: &str = "F0201";
const CODE_ELAB_AMBIGUOUS_CTOR: &str = "F0202";
const CODE_ELAB_NOT_IMPLEMENTED: &str = "F0203";
const CODE_ELAB_TYPE_MISMATCH: &str = "F0205";
const CODE_ELAB_FUNCTION_KIND_MISMATCH: &str = "F0206";
const CODE_ELAB_FUNCTION_KIND_TOO_SMALL: &str = "F0207";
const CODE_ELAB_AMBIGUOUS_REF_LIFETIME: &str = "F0208";
const CODE_ELAB_IMPLICIT_NON_COPY_USE: &str = "F0209";
const CODE_ELAB_EVAL_IN_TYPE: &str = "F0210";
const CODE_ELAB_NONEXHAUSTIVE_MATCH: &str = "F0211";
const CODE_ELAB_DUPLICATE_MATCH_CASE: &str = "F0212";
const CODE_ELAB_UNKNOWN_MATCH_CASE: &str = "F0213";
const CODE_ELAB_UNIFICATION_ERROR: &str = "F0214";
const CODE_ELAB_OCCURS_CHECK: &str = "F0215";
const CODE_ELAB_SOLUTION_FREE_VARS: &str = "F0216";
const CODE_ELAB_UNSOLVED_CONSTRAINTS: &str = "F0217";
const CODE_ELAB_RECURSOR_NEEDS_MOTIVE: &str = "F0218";
const CODE_ELAB_UNKNOWN_TYPE_MARKER: &str = "F0219";
const CODE_ELAB_CONFLICTING_TYPE_MARKERS: &str = "F0220";
const CODE_ELAB_MISSING_IM_KIND: &str = "F0221";
const CODE_ELAB_AMBIGUOUS_NAME: &str = "F0222";

#[derive(Error, Debug)]
pub enum ElabError {
    #[error("Unbound variable: {0}")]
    UnboundVariable(String, Span),
    #[error("Unknown inductive type: {0}")]
    UnknownInductive(String, Span),
    #[error("Ambiguous constructor {name}; candidates: {candidates:?}")]
    AmbiguousConstructor {
        name: String,
        candidates: Vec<String>,
        span: Span,
    },
    #[error("Ambiguous name {name}; candidates: {candidates:?}")]
    AmbiguousName {
        name: String,
        candidates: Vec<String>,
        span: Span,
    },
    #[error("Elaboration not implemented for this term")]
    NotImplemented(Span),
    #[error("Type inference failed during elaboration: {0}")]
    InferenceError(kernel::checker::TypeError, Span),
    #[error("Type mismatch: expected {expected}, got {got}")]
    TypeMismatch {
        expected: String,
        got: String,
        span: Span,
    },
    #[error("Function kind mismatch: expected {expected:?}, got {got:?}")]
    FunctionKindMismatch {
        expected: FunctionKind,
        got: FunctionKind,
        span: Span,
    },
    #[error("Annotated function kind {annotated:?} is too small; requires {required:?}")]
    FunctionKindAnnotationTooSmall {
        annotated: FunctionKind,
        required: FunctionKind,
        span: Span,
    },
    #[error("Ambiguous lifetime in return type; add explicit Ref #[label] annotations")]
    AmbiguousRefLifetime { span: Span },
    #[error("Implicit binder of non-Copy type used in {mode} position at de Bruijn index {index}")]
    ImplicitNonCopyUse { index: usize, mode: &'static str },
    #[error("eval is not allowed in type position")]
    EvalInType(Span),
    #[error("Non-exhaustive match on {ind}: missing cases {missing:?}")]
    NonExhaustiveMatch {
        ind: String,
        missing: Vec<String>,
        span: Span,
    },
    #[error("Duplicate case {ctor} in match on {ind}")]
    DuplicateMatchCase {
        ind: String,
        ctor: String,
        span: Span,
    },
    #[error("Unknown constructor {ctor} in match on {ind}")]
    UnknownMatchCase {
        ind: String,
        ctor: String,
        span: Span,
    },
    #[error("Unification failed: {0} vs {1}")]
    UnificationError(String, String),
    #[error("Occurs check failed: tried to solve {0} with {1}")]
    OccursCheck(usize, String),
    #[error("Metavariable solution {0} contains free variables")]
    SolutionContainsFreeVariables(String),
    #[error("Unsolved constraints remaining: {0}")]
    UnsolvedConstraints(String),
    #[error("Recursor requires a motive to infer universe level")]
    RecursorNeedsMotive(Span),
    #[error("Unknown type marker: {0}")]
    UnknownTypeMarker(String, Span),
    #[error("Conflicting interior mutability markers: {0}")]
    ConflictingTypeMarkers(String, Span),
    #[error("Interior mutability marker requires one of: {0}")]
    MissingInteriorMutabilityKind(String, Span),
}

impl ElabError {
    pub fn diagnostic_code(&self) -> &'static str {
        match self {
            ElabError::UnboundVariable(_, _) => CODE_ELAB_UNBOUND_VAR,
            ElabError::UnknownInductive(_, _) => CODE_ELAB_UNKNOWN_INDUCTIVE,
            ElabError::AmbiguousConstructor { .. } => CODE_ELAB_AMBIGUOUS_CTOR,
            ElabError::AmbiguousName { .. } => CODE_ELAB_AMBIGUOUS_NAME,
            ElabError::NotImplemented(_) => CODE_ELAB_NOT_IMPLEMENTED,
            ElabError::InferenceError(err, _) => err.diagnostic_code(),
            ElabError::TypeMismatch { .. } => CODE_ELAB_TYPE_MISMATCH,
            ElabError::FunctionKindMismatch { .. } => CODE_ELAB_FUNCTION_KIND_MISMATCH,
            ElabError::FunctionKindAnnotationTooSmall { .. } => CODE_ELAB_FUNCTION_KIND_TOO_SMALL,
            ElabError::AmbiguousRefLifetime { .. } => CODE_ELAB_AMBIGUOUS_REF_LIFETIME,
            ElabError::ImplicitNonCopyUse { .. } => CODE_ELAB_IMPLICIT_NON_COPY_USE,
            ElabError::EvalInType(_) => CODE_ELAB_EVAL_IN_TYPE,
            ElabError::NonExhaustiveMatch { .. } => CODE_ELAB_NONEXHAUSTIVE_MATCH,
            ElabError::DuplicateMatchCase { .. } => CODE_ELAB_DUPLICATE_MATCH_CASE,
            ElabError::UnknownMatchCase { .. } => CODE_ELAB_UNKNOWN_MATCH_CASE,
            ElabError::UnificationError(_, _) => CODE_ELAB_UNIFICATION_ERROR,
            ElabError::OccursCheck(_, _) => CODE_ELAB_OCCURS_CHECK,
            ElabError::SolutionContainsFreeVariables(_) => CODE_ELAB_SOLUTION_FREE_VARS,
            ElabError::UnsolvedConstraints(_) => CODE_ELAB_UNSOLVED_CONSTRAINTS,
            ElabError::RecursorNeedsMotive(_) => CODE_ELAB_RECURSOR_NEEDS_MOTIVE,
            ElabError::UnknownTypeMarker(_, _) => CODE_ELAB_UNKNOWN_TYPE_MARKER,
            ElabError::ConflictingTypeMarkers(_, _) => CODE_ELAB_CONFLICTING_TYPE_MARKERS,
            ElabError::MissingInteriorMutabilityKind(_, _) => CODE_ELAB_MISSING_IM_KIND,
        }
    }

    pub fn span(&self) -> Option<Span> {
        let span = match self {
            ElabError::UnboundVariable(_, span)
            | ElabError::UnknownInductive(_, span)
            | ElabError::AmbiguousConstructor { span, .. }
            | ElabError::AmbiguousName { span, .. }
            | ElabError::NotImplemented(span)
            | ElabError::InferenceError(_, span)
            | ElabError::TypeMismatch { span, .. }
            | ElabError::FunctionKindMismatch { span, .. }
            | ElabError::FunctionKindAnnotationTooSmall { span, .. }
            | ElabError::AmbiguousRefLifetime { span }
            | ElabError::EvalInType(span)
            | ElabError::NonExhaustiveMatch { span, .. }
            | ElabError::DuplicateMatchCase { span, .. }
            | ElabError::UnknownMatchCase { span, .. }
            | ElabError::RecursorNeedsMotive(span)
            | ElabError::UnknownTypeMarker(_, span)
            | ElabError::ConflictingTypeMarkers(_, span)
            | ElabError::MissingInteriorMutabilityKind(_, span) => Some(*span),
            ElabError::ImplicitNonCopyUse { .. }
            | ElabError::UnificationError(_, _)
            | ElabError::OccursCheck(_, _)
            | ElabError::SolutionContainsFreeVariables(_)
            | ElabError::UnsolvedConstraints(_) => None,
        }?;

        if span.start == 0 && span.end == 0 && span.line == 0 && span.col == 0 {
            None
        } else {
            Some(span)
        }
    }
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Unification {
        t1: Rc<Term>,
        t2: Rc<Term>,
        span: Span,
        context: Vec<(String, Rc<Term>)>,
    },
}

#[derive(Debug, Clone)]
struct MetaContext {
    binders: Vec<(String, Rc<Term>)>,
}

impl MetaContext {
    fn len(&self) -> usize {
        self.binders.len()
    }
}

fn function_kind_rank(kind: FunctionKind) -> u8 {
    match kind {
        FunctionKind::Fn => 0,
        FunctionKind::FnMut => 1,
        FunctionKind::FnOnce => 2,
    }
}

fn function_kind_leq(lhs: FunctionKind, rhs: FunctionKind) -> bool {
    function_kind_rank(lhs) <= function_kind_rank(rhs)
}

fn function_kind_max(lhs: FunctionKind, rhs: FunctionKind) -> FunctionKind {
    if function_kind_rank(lhs) >= function_kind_rank(rhs) {
        lhs
    } else {
        rhs
    }
}

#[derive(Clone, Copy)]
struct CaptureContext {
    mode: UsageMode,
    depth: usize,
}

fn bump_captures(captures: &[CaptureContext]) -> Vec<CaptureContext> {
    captures
        .iter()
        .map(|capture| CaptureContext {
            mode: capture.mode,
            depth: capture.depth + 1,
        })
        .collect()
}

fn usage_mode_rank(mode: UsageMode) -> u8 {
    match mode {
        UsageMode::Observational => 0,
        UsageMode::MutBorrow => 1,
        UsageMode::Consuming => 2,
    }
}

fn usage_mode_min(a: UsageMode, b: UsageMode) -> UsageMode {
    if usage_mode_rank(a) <= usage_mode_rank(b) {
        a
    } else {
        b
    }
}

fn usage_mode_max(a: UsageMode, b: UsageMode) -> UsageMode {
    if usage_mode_rank(a) >= usage_mode_rank(b) {
        a
    } else {
        b
    }
}

fn usage_mode_for_kind(kind: FunctionKind) -> UsageMode {
    match kind {
        FunctionKind::Fn => UsageMode::Observational,
        FunctionKind::FnMut => UsageMode::MutBorrow,
        FunctionKind::FnOnce => UsageMode::Consuming,
    }
}

fn usage_mode_label(mode: UsageMode) -> &'static str {
    match mode {
        UsageMode::Observational => "observational",
        UsageMode::MutBorrow => "mutable borrow",
        UsageMode::Consuming => "consuming",
    }
}

fn implicit_noncopy_at(implicit_noncopy: &[bool], idx: usize) -> bool {
    if idx >= implicit_noncopy.len() {
        return false;
    }
    let stack_idx = implicit_noncopy.len() - 1 - idx;
    implicit_noncopy[stack_idx]
}

fn merge_capture_modes(into: &mut CaptureModes, from: CaptureModes) {
    for (idx, mode) in from {
        into.entry(idx)
            .and_modify(|existing| *existing = usage_mode_max(*existing, mode))
            .or_insert(mode);
    }
}

fn required_kind_from_capture_modes(modes: &CaptureModes) -> FunctionKind {
    let mut required = FunctionKind::Fn;
    for mode in modes.values() {
        required = match mode {
            UsageMode::Observational => required,
            UsageMode::MutBorrow => function_kind_max(required, FunctionKind::FnMut),
            UsageMode::Consuming => function_kind_max(required, FunctionKind::FnOnce),
        };
    }
    required
}

/// Result of attempting unification
#[derive(Debug)]
pub enum UnifyResult {
    /// Unification succeeded
    Success,
    /// Unification is stuck on unsolved metavariables - can be retried later
    Stuck(Rc<Term>, Rc<Term>),
    /// Unification definitively failed - types are incompatible
    Failed(Rc<Term>, Rc<Term>),
}

const MARKER_INTERIOR_MUTABLE: &str = "interior_mutable";
const MARKER_MAY_PANIC: &str = "may_panic_on_borrow_violation";
const MARKER_CONCURRENCY: &str = "concurrency_primitive";
const MARKER_ATOMIC: &str = "atomic_primitive";
const MARKER_INDEXABLE: &str = "indexable";

#[derive(Debug, Clone, Copy)]
struct MarkerRegistry {
    interior_mutable: DefId,
    may_panic: DefId,
    concurrency: DefId,
    atomic: DefId,
    indexable: DefId,
}

impl MarkerRegistry {
    fn new() -> Self {
        Self {
            interior_mutable: DefId::new(MARKER_INTERIOR_MUTABLE),
            may_panic: DefId::new(MARKER_MAY_PANIC),
            concurrency: DefId::new(MARKER_CONCURRENCY),
            atomic: DefId::new(MARKER_ATOMIC),
            indexable: DefId::new(MARKER_INDEXABLE),
        }
    }

    fn id_for(&self, marker: TypeMarker) -> MarkerId {
        match marker {
            TypeMarker::InteriorMutable => self.interior_mutable,
            TypeMarker::MayPanicOnBorrowViolation => self.may_panic,
            TypeMarker::ConcurrencyPrimitive => self.concurrency,
            TypeMarker::AtomicPrimitive => self.atomic,
            TypeMarker::Indexable => self.indexable,
        }
    }
}

fn marker_def_id(env: &Env, name: &str, span: Span) -> Result<DefId, ElabError> {
    if env.get_definition(name).is_none() {
        return Err(ElabError::UnknownTypeMarker(name.to_string(), span));
    }
    Ok(DefId::new(name))
}

fn push_marker_id(markers: &mut Vec<MarkerId>, marker: MarkerId) {
    if !markers.contains(&marker) {
        markers.push(marker);
    }
}

fn collect_app_spine(term: SurfaceTerm) -> (SurfaceTerm, Vec<(SurfaceTerm, bool)>) {
    let mut args = Vec::new();
    let mut head = term;
    loop {
        match head.kind {
            SurfaceTermKind::App(f, x, is_explicit) => {
                args.push((*x, is_explicit));
                head = *f;
            }
            _ => break,
        }
    }
    args.reverse();
    (head, args)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub u64);

pub struct Elaborator<'a> {
    env: &'a Env,
    locals: Vec<(String, Rc<Term>)>,
    in_type_context: bool,
    meta_counter: usize,
    meta_solutions: HashMap<usize, Rc<Term>>,
    meta_contexts: HashMap<usize, MetaContext>,
    constraints: Vec<Constraint>,
    next_term_id: u64,
    term_ids: HashMap<usize, TermId>,
    span_map: HashMap<TermId, Span>,
    capture_mode_map: HashMap<usize, CaptureModes>,
    elided_label_counter: usize,
    elided_labels: HashSet<String>,
    label_subst: HashMap<String, String>,
    current_module: Option<String>,
    opened_modules: Vec<String>,
    import_aliases: Vec<(String, String)>,
}

impl<'a> Elaborator<'a> {
    pub fn new(env: &'a Env) -> Self {
        Elaborator {
            env,
            locals: Vec::new(),
            in_type_context: false,
            meta_counter: 0,
            meta_solutions: HashMap::new(),
            meta_contexts: HashMap::new(),
            constraints: Vec::new(),
            next_term_id: 0,
            term_ids: HashMap::new(),
            span_map: HashMap::new(),
            capture_mode_map: HashMap::new(),
            elided_label_counter: 0,
            elided_labels: HashSet::new(),
            label_subst: HashMap::new(),
            current_module: None,
            opened_modules: Vec::new(),
            import_aliases: Vec::new(),
        }
    }

    pub fn set_name_resolution(
        &mut self,
        current_module: Option<String>,
        opened_modules: Vec<String>,
        import_aliases: Vec<(String, String)>,
    ) {
        self.current_module = current_module.filter(|module| !module.is_empty());

        let mut normalized_opened: Vec<String> = Vec::new();
        for module in opened_modules {
            if module.is_empty() || normalized_opened.contains(&module) {
                continue;
            }
            normalized_opened.push(module);
        }
        self.opened_modules = normalized_opened;

        let mut normalized_aliases: Vec<(String, String)> = Vec::new();
        for (alias, module) in import_aliases {
            if alias.is_empty() || module.is_empty() {
                continue;
            }
            if normalized_aliases
                .iter()
                .any(|(existing_alias, existing_module)| {
                    existing_alias == &alias && existing_module == &module
                })
            {
                continue;
            }
            normalized_aliases.push((alias, module));
        }
        self.import_aliases = normalized_aliases;
    }

    /// Backward-compatible helper used by older tests; equivalent to opening modules.
    pub fn set_import_scopes<I, S>(&mut self, scopes: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let opened_modules: Vec<String> = scopes
            .into_iter()
            .map(Into::into)
            .filter(|scope| !scope.is_empty() && scope != "classical")
            .collect();
        self.set_name_resolution(None, opened_modules, Vec::new());
    }

    pub fn span_map(&self) -> &HashMap<TermId, Span> {
        &self.span_map
    }

    pub fn term_id_map(&self) -> &HashMap<usize, TermId> {
        &self.term_ids
    }

    pub fn capture_mode_map(&self) -> &HashMap<usize, CaptureModes> {
        &self.capture_mode_map
    }

    fn extract_lifetime_label(term: &SurfaceTerm) -> Option<String> {
        match &term.kind {
            SurfaceTermKind::Index(base, index) => match (&base.kind, &index.kind) {
                (SurfaceTermKind::Var(base_name), SurfaceTermKind::Var(label))
                    if base_name == "#" =>
                {
                    Some(label.clone())
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn parse_ref_surface(term: &SurfaceTerm) -> Option<(Option<String>, SurfaceTerm)> {
        let (head, args) = collect_app_spine(term.clone());
        if let SurfaceTermKind::Var(name) = &head.kind {
            if name == "Ref" {
                if args.len() == 2 {
                    return Some((None, args[1].0.clone()));
                }
                if args.len() == 3 {
                    if let Some(label) = Self::extract_lifetime_label(&args[0].0) {
                        return Some((Some(label), args[2].0.clone()));
                    }
                }
            }
        }
        None
    }

    fn fresh_elided_label(&mut self) -> String {
        let label = format!("_elided{}", self.elided_label_counter);
        self.elided_label_counter += 1;
        self.elided_labels.insert(label.clone());
        label
    }

    fn is_elided_label(&self, label: &str) -> bool {
        self.elided_labels.contains(label)
    }

    fn normalize_label(&self, label: &str) -> String {
        let mut current = label.to_string();
        let mut seen = HashSet::new();
        while let Some(next) = self.label_subst.get(&current) {
            if !seen.insert(current.clone()) {
                break;
            }
            current = next.clone();
        }
        current
    }

    fn apply_label_subst(&mut self, term: &Rc<Term>) -> Rc<Term> {
        match &**term {
            Term::App(f, a, label) => {
                let new_f = self.apply_label_subst(f);
                let new_a = self.apply_label_subst(a);
                let new_label = label.as_ref().map(|l| self.normalize_label(l));
                let new_term = Rc::new(Term::App(new_f, new_a, new_label));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Lam(ty, body, info, kind) => {
                let new_term = Rc::new(Term::Lam(
                    self.apply_label_subst(ty),
                    self.apply_label_subst(body),
                    *info,
                    *kind,
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Pi(ty, body, info, kind) => {
                let new_term = Rc::new(Term::Pi(
                    self.apply_label_subst(ty),
                    self.apply_label_subst(body),
                    *info,
                    *kind,
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::LetE(ty, val, body) => {
                let new_term = Rc::new(Term::LetE(
                    self.apply_label_subst(ty),
                    self.apply_label_subst(val),
                    self.apply_label_subst(body),
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Fix(ty, body) => {
                let new_term = Rc::new(Term::Fix(
                    self.apply_label_subst(ty),
                    self.apply_label_subst(body),
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            _ => term.clone(),
        }
    }

    fn align_ref_labels(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) {
        match (&**t1, &**t2) {
            (Term::App(f1, a1, l1), Term::App(f2, a2, l2)) => {
                if let (Some(label1), Some(label2)) = (l1.as_ref(), l2.as_ref()) {
                    let n1 = self.normalize_label(label1);
                    let n2 = self.normalize_label(label2);
                    if n1 != n2 {
                        let n1_elided = self.is_elided_label(&n1);
                        let n2_elided = self.is_elided_label(&n2);
                        if n1_elided && !n2_elided {
                            self.label_subst.insert(n1.clone(), n2.clone());
                        } else if n2_elided && !n1_elided {
                            self.label_subst.insert(n2.clone(), n1.clone());
                        } else if n1_elided && n2_elided {
                            let target = if n1 <= n2 { n1.clone() } else { n2.clone() };
                            self.label_subst.insert(n1.clone(), target.clone());
                            self.label_subst.insert(n2.clone(), target);
                        }
                    }
                }
                self.align_ref_labels(f1, f2);
                self.align_ref_labels(a1, a2);
            }
            (Term::Lam(ty1, body1, _, _), Term::Lam(ty2, body2, _, _))
            | (Term::Pi(ty1, body1, _, _), Term::Pi(ty2, body2, _, _)) => {
                self.align_ref_labels(ty1, ty2);
                self.align_ref_labels(body1, body2);
            }
            (Term::LetE(ty1, val1, body1), Term::LetE(ty2, val2, body2)) => {
                self.align_ref_labels(ty1, ty2);
                self.align_ref_labels(val1, val2);
                self.align_ref_labels(body1, body2);
            }
            (Term::Fix(ty1, body1), Term::Fix(ty2, body2)) => {
                self.align_ref_labels(ty1, ty2);
                self.align_ref_labels(body1, body2);
            }
            _ => {}
        }
    }

    fn collect_ref_label_stats(
        &self,
        term: &SurfaceTerm,
        explicit_labels: &mut HashSet<String>,
        unlabeled_count: &mut usize,
    ) {
        if let Some((label, inner)) = Self::parse_ref_surface(term) {
            if let Some(label) = label {
                explicit_labels.insert(label);
            } else {
                *unlabeled_count += 1;
            }
            self.collect_ref_label_stats(&inner, explicit_labels, unlabeled_count);
            return;
        }

        match &term.kind {
            SurfaceTermKind::App(f, x, _) => {
                self.collect_ref_label_stats(f, explicit_labels, unlabeled_count);
                self.collect_ref_label_stats(x, explicit_labels, unlabeled_count);
            }
            SurfaceTermKind::Index(base, index) => {
                self.collect_ref_label_stats(base, explicit_labels, unlabeled_count);
                self.collect_ref_label_stats(index, explicit_labels, unlabeled_count);
            }
            SurfaceTermKind::Let(_, ty, val, body) => {
                self.collect_ref_label_stats(ty, explicit_labels, unlabeled_count);
                self.collect_ref_label_stats(val, explicit_labels, unlabeled_count);
                self.collect_ref_label_stats(body, explicit_labels, unlabeled_count);
            }
            SurfaceTermKind::Match(scrutinee, ret_type, cases) => {
                self.collect_ref_label_stats(scrutinee, explicit_labels, unlabeled_count);
                self.collect_ref_label_stats(ret_type, explicit_labels, unlabeled_count);
                for (_, _, body) in cases {
                    self.collect_ref_label_stats(body, explicit_labels, unlabeled_count);
                }
            }
            SurfaceTermKind::Eval(code, cap) => {
                self.collect_ref_label_stats(code, explicit_labels, unlabeled_count);
                self.collect_ref_label_stats(cap, explicit_labels, unlabeled_count);
            }
            SurfaceTermKind::Lam(_, _, _, _, _) | SurfaceTermKind::Pi(_, _, _, _, _) => {}
            SurfaceTermKind::Var(_)
            | SurfaceTermKind::Sort(_)
            | SurfaceTermKind::Ind(_)
            | SurfaceTermKind::Ctor(_, _)
            | SurfaceTermKind::Rec(_)
            | SurfaceTermKind::Fix(_, _, _)
            | SurfaceTermKind::Hole => {}
        }
    }

    fn ensure_return_refs_labeled(
        &self,
        term: &SurfaceTerm,
        distinct_arg_labels: usize,
    ) -> Result<(), ElabError> {
        if distinct_arg_labels == 1 {
            return Ok(());
        }

        if let Some((label, inner)) = Self::parse_ref_surface(term) {
            if label.is_none() {
                return Err(ElabError::AmbiguousRefLifetime { span: term.span });
            }
            return self.ensure_return_refs_labeled(&inner, distinct_arg_labels);
        }

        match &term.kind {
            SurfaceTermKind::App(f, x, _) => {
                self.ensure_return_refs_labeled(f, distinct_arg_labels)?;
                self.ensure_return_refs_labeled(x, distinct_arg_labels)
            }
            SurfaceTermKind::Index(base, index) => {
                self.ensure_return_refs_labeled(base, distinct_arg_labels)?;
                self.ensure_return_refs_labeled(index, distinct_arg_labels)
            }
            SurfaceTermKind::Let(_, ty, val, body) => {
                self.ensure_return_refs_labeled(ty, distinct_arg_labels)?;
                self.ensure_return_refs_labeled(val, distinct_arg_labels)?;
                self.ensure_return_refs_labeled(body, distinct_arg_labels)
            }
            SurfaceTermKind::Match(scrutinee, ret_type, cases) => {
                self.ensure_return_refs_labeled(scrutinee, distinct_arg_labels)?;
                self.ensure_return_refs_labeled(ret_type, distinct_arg_labels)?;
                for (_, _, body) in cases {
                    self.ensure_return_refs_labeled(body, distinct_arg_labels)?;
                }
                Ok(())
            }
            SurfaceTermKind::Eval(code, cap) => {
                self.ensure_return_refs_labeled(code, distinct_arg_labels)?;
                self.ensure_return_refs_labeled(cap, distinct_arg_labels)
            }
            SurfaceTermKind::Lam(_, _, _, _, _) | SurfaceTermKind::Pi(_, _, _, _, _) => Ok(()),
            SurfaceTermKind::Var(_)
            | SurfaceTermKind::Sort(_)
            | SurfaceTermKind::Ind(_)
            | SurfaceTermKind::Ctor(_, _)
            | SurfaceTermKind::Rec(_)
            | SurfaceTermKind::Fix(_, _, _)
            | SurfaceTermKind::Hole => Ok(()),
        }
    }

    fn validate_ref_lifetime_elision_for_pi(
        &self,
        dom: &SurfaceTerm,
        body: &SurfaceTerm,
    ) -> Result<(), ElabError> {
        let mut explicit_labels: HashSet<String> = HashSet::new();
        let mut unlabeled_count = 0usize;
        let mut current_dom = dom;
        let mut current_body = body;

        loop {
            self.collect_ref_label_stats(current_dom, &mut explicit_labels, &mut unlabeled_count);
            if let SurfaceTermKind::Pi(_, _, _, next_dom, next_body) = &current_body.kind {
                current_dom = next_dom;
                current_body = next_body;
            } else {
                break;
            }
        }

        let distinct_arg_labels = explicit_labels.len() + unlabeled_count;
        self.ensure_return_refs_labeled(current_body, distinct_arg_labels)
    }

    fn with_type_context<T>(
        &mut self,
        f: impl FnOnce(&mut Elaborator<'a>) -> Result<T, ElabError>,
    ) -> Result<T, ElabError> {
        let prev = self.in_type_context;
        self.in_type_context = true;
        let result = f(self);
        self.in_type_context = prev;
        result
    }

    pub fn infer_type(&mut self, term: SurfaceTerm) -> Result<(Rc<Term>, Rc<Term>), ElabError> {
        self.with_type_context(|elab| elab.infer(term))
    }

    fn term_key(term: &Rc<Term>) -> usize {
        Rc::as_ptr(term) as usize
    }

    fn term_id_for(&self, term: &Rc<Term>) -> Option<TermId> {
        self.term_ids.get(&Self::term_key(term)).copied()
    }

    fn intern_term_id(&mut self, term: &Rc<Term>) -> TermId {
        let key = Self::term_key(term);
        if let Some(existing) = self.term_ids.get(&key).copied() {
            return existing;
        }
        let id = TermId(self.next_term_id);
        self.next_term_id += 1;
        self.term_ids.insert(key, id);
        id
    }

    fn span_for_term(&self, term: &Rc<Term>) -> Option<Span> {
        let id = self.term_id_for(term)?;
        self.span_map.get(&id).copied()
    }

    fn record_span(&mut self, term: &Rc<Term>, span: Span) {
        let id = self.intern_term_id(term);
        self.span_map.insert(id, span);
    }

    fn record_capture_modes(&mut self, term: &Rc<Term>, modes: CaptureModes) {
        self.capture_mode_map.insert(Self::term_key(term), modes);
    }

    fn copy_span_if_any(&mut self, from: &Rc<Term>, to: &Rc<Term>) {
        if let Some(id) = self.term_id_for(from) {
            if self.span_map.contains_key(&id) {
                self.term_ids.entry(Self::term_key(to)).or_insert(id);
            }
        }
    }

    fn copy_capture_modes_if_any(&mut self, from: &Rc<Term>, to: &Rc<Term>) {
        if let Some(modes) = self.capture_mode_map.get(&Self::term_key(from)).cloned() {
            self.capture_mode_map
                .entry(Self::term_key(to))
                .or_insert(modes);
        }
    }

    fn copy_metadata_if_any(&mut self, from: &Rc<Term>, to: &Rc<Term>) {
        self.copy_span_if_any(from, to);
        self.copy_capture_modes_if_any(from, to);
    }

    fn attach_ref_label(&mut self, term: &Rc<Term>, label: String) -> Rc<Term> {
        match &**term {
            Term::App(f, a, _) => {
                let labeled = Rc::new(Term::App(f.clone(), a.clone(), Some(label)));
                self.copy_metadata_if_any(term, &labeled);
                labeled
            }
            _ => {
                debug_assert!(false, "expected application term for labeled Ref");
                term.clone()
            }
        }
    }

    fn defeq_transparency(&self) -> kernel::Transparency {
        kernel::Transparency::Reducible
    }

    fn whnf(&self, term: Rc<Term>) -> Result<Rc<Term>, ElabError> {
        let ctx = self.build_context();
        let span = self.span_for_term(&term).unwrap_or(Span {
            start: 0,
            end: 0,
            line: 0,
            col: 0,
        });
        kernel::checker::whnf_in_ctx(self.env, &ctx, term, self.defeq_transparency())
            .map_err(|e| ElabError::InferenceError(e, span))
    }

    fn is_def_eq_in_ctx(&self, t1: &Rc<Term>, t2: &Rc<Term>) -> Result<bool, ElabError> {
        let ctx = self.build_context();
        kernel::checker::is_def_eq_in_ctx(
            self.env,
            &ctx,
            t1.clone(),
            t2.clone(),
            self.defeq_transparency(),
        )
        .map_err(|e| {
            let span = self
                .span_for_term(t1)
                .or_else(|| self.span_for_term(t2))
                .unwrap_or(Span {
                    start: 0,
                    end: 0,
                    line: 0,
                    col: 0,
                });
            ElabError::InferenceError(e, span)
        })
    }

    fn module_matches_scope(ind_name: &str, scope: &str) -> bool {
        ind_name == scope || ind_name.starts_with(&format!("{}.", scope))
    }

    fn alias_targets(&self, alias: &str) -> Vec<String> {
        let mut targets = Vec::new();
        for (candidate_alias, module) in &self.import_aliases {
            if candidate_alias == alias && !targets.contains(module) {
                targets.push(module.clone());
            }
        }
        targets
    }

    fn rewrite_qualified_name(&self, name: &str, span: Span) -> Result<String, ElabError> {
        if let Some((head, tail)) = name.split_once('.') {
            let mut targets = self.alias_targets(head);
            if targets.len() == 1 {
                return Ok(format!("{}.{}", targets[0], tail));
            }
            if targets.len() > 1 {
                targets.sort();
                targets.dedup();
                let candidates = targets
                    .into_iter()
                    .map(|module| format!("{}.{}", module, tail))
                    .collect();
                return Err(ElabError::AmbiguousName {
                    name: name.to_string(),
                    candidates,
                    span,
                });
            }
        }
        Ok(name.to_string())
    }

    fn constructor_candidates_in_scope(
        &self,
        ctor_name: &str,
        scope: &str,
    ) -> Vec<kernel::checker::ConstructorRef> {
        let mut candidates: Vec<_> = self
            .env
            .constructor_candidates(ctor_name)
            .iter()
            .filter(|candidate| Self::module_matches_scope(&candidate.ind_name, scope))
            .cloned()
            .collect();
        candidates.sort_by(|lhs, rhs| {
            lhs.ind_name
                .cmp(&rhs.ind_name)
                .then(lhs.index.cmp(&rhs.index))
        });
        candidates
    }

    fn resolve_qualified_constructor(
        &self,
        qualified_name: &str,
        span: Span,
    ) -> Result<Option<Rc<Term>>, ElabError> {
        let (scope, ctor_name) = match qualified_name.rsplit_once('.') {
            Some(parts) => parts,
            None => return Ok(None),
        };

        let candidates = self.constructor_candidates_in_scope(ctor_name, scope);

        if candidates.is_empty() {
            return Ok(None);
        }

        if candidates.len() == 1 {
            let ctor = &candidates[0];
            return Ok(Some(Rc::new(Term::Ctor(
                ctor.ind_name.clone(),
                ctor.index,
                vec![],
            ))));
        }

        let mut full_names: Vec<String> = candidates
            .iter()
            .map(|candidate| format!("{}.{}", candidate.ind_name, ctor_name))
            .collect();
        full_names.sort();
        full_names.dedup();
        Err(ElabError::AmbiguousConstructor {
            name: qualified_name.to_string(),
            candidates: full_names,
            span,
        })
    }

    fn collect_module_candidates(&self, name: &str, module: &str) -> Vec<(String, Rc<Term>, bool)> {
        let mut candidates = Vec::new();
        let qualified = format!("{}.{}", module, name);

        if self.env.get_inductive(&qualified).is_some() {
            candidates.push((
                qualified.clone(),
                Rc::new(Term::Ind(qualified.clone(), vec![])),
                false,
            ));
        }

        if let Some(def) = self.env.get_definition(&qualified) {
            let is_constructor_alias = def
                .value
                .as_ref()
                .is_some_and(|value| matches!(&**value, Term::Ctor(_, _, _)));
            if !is_constructor_alias {
                candidates.push((
                    qualified.clone(),
                    Rc::new(Term::Const(qualified.clone(), vec![])),
                    false,
                ));
            }
        }

        for ctor in self.constructor_candidates_in_scope(name, module) {
            candidates.push((
                format!("{}.{}", ctor.ind_name, name),
                Rc::new(Term::Ctor(ctor.ind_name, ctor.index, vec![])),
                true,
            ));
        }

        candidates
    }

    fn dedup_candidates(
        &self,
        mut candidates: Vec<(String, Rc<Term>, bool)>,
    ) -> Vec<(String, Rc<Term>, bool)> {
        candidates.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0));
        candidates.dedup_by(|lhs, rhs| lhs.0 == rhs.0);
        candidates
    }

    fn resolve_candidates(
        &self,
        name: &str,
        span: Span,
        candidates: Vec<(String, Rc<Term>, bool)>,
    ) -> Result<Option<Rc<Term>>, ElabError> {
        let candidates = self.dedup_candidates(candidates);
        if candidates.is_empty() {
            return Ok(None);
        }
        if candidates.len() == 1 {
            return Ok(Some(candidates[0].1.clone()));
        }

        // Constructor collisions must fail closed, even if there are mixed candidates.
        // This preserves the "require qualification for ctor collisions" contract.
        let mut ctor_labels: Vec<String> = candidates
            .iter()
            .filter(|(_, _, is_ctor)| *is_ctor)
            .map(|(label, _, _)| label.clone())
            .collect();
        ctor_labels.sort();
        ctor_labels.dedup();
        if ctor_labels.len() > 1 {
            return Err(ElabError::AmbiguousConstructor {
                name: name.to_string(),
                candidates: ctor_labels,
                span,
            });
        }

        let mut labels: Vec<String> = candidates.into_iter().map(|(label, _, _)| label).collect();
        labels.sort();
        labels.dedup();

        Err(ElabError::AmbiguousName {
            name: name.to_string(),
            candidates: labels,
            span,
        })
    }

    fn prelude_candidates(&self, name: &str) -> Vec<(String, Rc<Term>, bool)> {
        let mut candidates = Vec::new();
        if self.env.get_inductive(name).is_some() {
            candidates.push((
                name.to_string(),
                Rc::new(Term::Ind(name.to_string(), vec![])),
                false,
            ));
        }
        if let Some(def) = self.env.get_definition(name) {
            let is_constructor_alias = def
                .value
                .as_ref()
                .is_some_and(|value| matches!(&**value, Term::Ctor(_, _, _)));
            if !is_constructor_alias {
                candidates.push((
                    name.to_string(),
                    Rc::new(Term::Const(name.to_string(), vec![])),
                    false,
                ));
            }
        }
        for ctor in self.env.constructor_candidates(name).iter() {
            if ctor.ind_name.contains('.') {
                continue;
            }
            candidates.push((
                format!("{}.{}", ctor.ind_name, name),
                Rc::new(Term::Ctor(ctor.ind_name.clone(), ctor.index, vec![])),
                true,
            ));
        }
        candidates
    }

    fn resolve_name(&self, name: &str, span: Span) -> Result<Option<Rc<Term>>, ElabError> {
        if name.contains('.') {
            let rewritten = self.rewrite_qualified_name(name, span)?;
            if self.env.get_inductive(&rewritten).is_some() {
                return Ok(Some(Rc::new(Term::Ind(rewritten, vec![]))));
            }
            if self.env.get_definition(&rewritten).is_some() {
                return Ok(Some(Rc::new(Term::Const(rewritten, vec![]))));
            }
            if let Some(ctor) = self.resolve_qualified_constructor(&rewritten, span)? {
                return Ok(Some(ctor));
            }
            return Ok(None);
        }

        for (i, (local_name, _)) in self.locals.iter().rev().enumerate() {
            if local_name == name {
                return Ok(Some(Rc::new(Term::Var(i))));
            }
        }

        if name == "Type" {
            return Ok(Some(Rc::new(Term::Sort(Level::Succ(Box::new(
                Level::Zero,
            ))))));
        }

        if let Some(module) = &self.current_module {
            if let Some(term) =
                self.resolve_candidates(name, span, self.collect_module_candidates(name, module))?
            {
                return Ok(Some(term));
            }
        }

        let mut opened_candidates = Vec::new();
        for module in &self.opened_modules {
            opened_candidates.extend(self.collect_module_candidates(name, module));
        }
        if let Some(term) = self.resolve_candidates(name, span, opened_candidates)? {
            return Ok(Some(term));
        }

        if let Some(term) = self.resolve_candidates(name, span, self.prelude_candidates(name))? {
            return Ok(Some(term));
        }

        Ok(None)
    }

    pub fn resolve_type_markers(
        &self,
        attrs: &[String],
        span: Span,
    ) -> Result<Vec<MarkerId>, ElabError> {
        if attrs.is_empty() {
            return Ok(Vec::new());
        }

        let registry = MarkerRegistry::new();
        let mut markers = Vec::new();
        let mut explicit_interior_mutable = false;
        let mut explicit_may_panic = false;
        let mut explicit_concurrency = false;
        let mut explicit_atomic = false;

        for attr in attrs {
            let attr_id = marker_def_id(self.env, attr, span)?;
            if attr_id == registry.interior_mutable {
                explicit_interior_mutable = true;
                push_marker_id(&mut markers, registry.id_for(TypeMarker::InteriorMutable));
            } else if attr_id == registry.may_panic {
                explicit_may_panic = true;
                push_marker_id(&mut markers, registry.id_for(TypeMarker::InteriorMutable));
                push_marker_id(
                    &mut markers,
                    registry.id_for(TypeMarker::MayPanicOnBorrowViolation),
                );
            } else if attr_id == registry.concurrency {
                explicit_concurrency = true;
                push_marker_id(&mut markers, registry.id_for(TypeMarker::InteriorMutable));
                push_marker_id(
                    &mut markers,
                    registry.id_for(TypeMarker::ConcurrencyPrimitive),
                );
            } else if attr_id == registry.atomic {
                explicit_atomic = true;
                push_marker_id(&mut markers, registry.id_for(TypeMarker::InteriorMutable));
                push_marker_id(
                    &mut markers,
                    registry.id_for(TypeMarker::ConcurrencyPrimitive),
                );
                push_marker_id(&mut markers, registry.id_for(TypeMarker::AtomicPrimitive));
            } else if attr_id == registry.indexable {
                push_marker_id(&mut markers, registry.id_for(TypeMarker::Indexable));
            } else {
                return Err(ElabError::UnknownTypeMarker(attr.clone(), span));
            }
        }

        if explicit_may_panic && (explicit_concurrency || explicit_atomic) {
            let mut conflicts = Vec::new();
            conflicts.push(MARKER_MAY_PANIC);
            if explicit_concurrency {
                conflicts.push(MARKER_CONCURRENCY);
            }
            if explicit_atomic {
                conflicts.push(MARKER_ATOMIC);
            }
            return Err(ElabError::ConflictingTypeMarkers(
                conflicts.join(", "),
                span,
            ));
        }

        if explicit_interior_mutable
            && !(explicit_may_panic || explicit_concurrency || explicit_atomic)
        {
            let expected = format!(
                "{} | {} | {}",
                MARKER_MAY_PANIC, MARKER_CONCURRENCY, MARKER_ATOMIC
            );
            return Err(ElabError::MissingInteriorMutabilityKind(expected, span));
        }

        Ok(markers)
    }

    fn build_context(&self) -> Context {
        let mut ctx = Context::new();
        for (_, ty) in &self.locals {
            ctx = ctx.push(ty.clone());
        }
        ctx
    }

    fn pretty_term(&self, term: &Rc<Term>) -> String {
        self.pretty_term_in_context(term, &self.locals)
    }

    fn pretty_term_in_context(&self, term: &Rc<Term>, locals: &[(String, Rc<Term>)]) -> String {
        let mut printer = CoreTermPrettyPrinter::new(self.env, locals);
        printer.pretty_term(term)
    }

    fn collect_core_app_spine(term: &Rc<Term>) -> (Rc<Term>, Vec<Rc<Term>>) {
        let mut args = Vec::new();
        let mut head = term.clone();
        while let Term::App(f, a, _) = &*head {
            args.push(a.clone());
            head = f.clone();
        }
        args.reverse();
        (head, args)
    }

    fn is_copy_type_in_ctx(&self, ctx: &Context, ty: &Rc<Term>) -> bool {
        kernel::checker::is_copy_type_in_ctx(self.env, ctx, ty).unwrap_or(false)
    }

    fn is_mut_ref_type(&self, ctx: &Context, ty: &Rc<Term>) -> bool {
        let ty_whnf =
            kernel::checker::whnf_in_ctx(self.env, ctx, ty.clone(), self.defeq_transparency());
        let ty_whnf = match ty_whnf {
            Ok(term) => term,
            Err(_) => return false,
        };
        let (head, args) = Self::collect_core_app_spine(&ty_whnf);
        match (&*head, args.as_slice()) {
            (Term::Const(name, _), [kind, _]) if name == "Ref" => {
                matches!(&**kind, Term::Const(k, _) if k == "Mut")
            }
            _ => false,
        }
    }

    fn function_pi_info_from_type(
        &self,
        ctx: &Context,
        ty: &Rc<Term>,
    ) -> Option<(Rc<Term>, kernel::ast::BinderInfo, FunctionKind)> {
        let ty_whnf =
            kernel::checker::whnf_in_ctx(self.env, ctx, ty.clone(), self.defeq_transparency())
                .ok()?;
        if let Term::Pi(arg_ty, _, info, kind) = &*ty_whnf {
            Some((arg_ty.clone(), *info, *kind))
        } else {
            None
        }
    }

    fn function_pi_info_from_term(
        &self,
        term: &Rc<Term>,
        ctx: &Context,
    ) -> Option<(Rc<Term>, kernel::ast::BinderInfo, FunctionKind)> {
        match &**term {
            Term::Lam(ty, _, info, kind) => Some((ty.clone(), *info, *kind)),
            Term::Var(idx) => ctx
                .get(*idx)
                .and_then(|ty| self.function_pi_info_from_type(ctx, &ty)),
            Term::Const(name, _) => self
                .env
                .get_definition(name)
                .and_then(|def| self.function_pi_info_from_type(ctx, &def.ty)),
            Term::Rec(ind, levels) => self
                .recursor_type(ind, levels)
                .ok()
                .and_then(|ty| self.function_pi_info_from_type(ctx, &ty)),
            _ => None,
        }
    }

    fn capture_modes_for_closure_body(
        &self,
        body: &Rc<Term>,
        ctx: &Context,
        outer_param_implicit_noncopy: bool,
    ) -> Result<CaptureModes, ElabError> {
        let implicit_noncopy = vec![outer_param_implicit_noncopy];
        self.collect_capture_modes_in_term(body, ctx, 1, UsageMode::Consuming, &implicit_noncopy)
    }

    fn analyze_closure_captures(
        &self,
        body: &Rc<Term>,
        ctx: &Context,
        outer_param_implicit_noncopy: bool,
    ) -> Result<(FunctionKind, CaptureModes), ElabError> {
        let capture_modes =
            self.capture_modes_for_closure_body(body, ctx, outer_param_implicit_noncopy)?;
        let required_kind = required_kind_from_capture_modes(&capture_modes);
        Ok((required_kind, capture_modes))
    }

    fn collect_capture_modes_in_term(
        &self,
        term: &Rc<Term>,
        ctx: &Context,
        capture_depth: usize,
        mode: UsageMode,
        implicit_noncopy: &[bool],
    ) -> Result<CaptureModes, ElabError> {
        match &**term {
            Term::Var(idx) => {
                if implicit_noncopy_at(implicit_noncopy, *idx) && mode != UsageMode::Observational {
                    return Err(ElabError::ImplicitNonCopyUse {
                        index: *idx,
                        mode: usage_mode_label(mode),
                    });
                }
                let mut modes = HashMap::new();
                if *idx >= capture_depth {
                    let mut capture_mode = mode;
                    if capture_mode == UsageMode::Consuming {
                        if let Some(ty) = ctx.get(*idx) {
                            if self.is_mut_ref_type(ctx, &ty) {
                                capture_mode = UsageMode::MutBorrow;
                            } else if self.is_copy_type_in_ctx(ctx, &ty) {
                                capture_mode = UsageMode::Observational;
                            }
                        }
                    }
                    let capture_idx = idx - capture_depth;
                    modes.insert(capture_idx, capture_mode);
                }
                Ok(modes)
            }
            Term::App(f, a, _) => {
                if mode != UsageMode::Observational {
                    let (head, args) = Self::collect_core_app_spine(term);
                    if let Term::Rec(ind_name, _levels) = &*head {
                        if let Some(decl) = self.env.get_inductive(ind_name) {
                            let num_params = decl.num_params;
                            let num_indices =
                                self.count_pi_args(&decl.ty).saturating_sub(num_params);
                            let num_ctors = decl.ctors.len();
                            let motive_pos = num_params;
                            let indices_start = motive_pos + 1 + num_ctors;
                            let indices_end = indices_start + num_indices;
                            let mut modes = HashMap::new();
                            for (idx, arg) in args.iter().enumerate() {
                                let arg_mode = if idx < num_params
                                    || idx == motive_pos
                                    || (idx >= indices_start && idx < indices_end)
                                {
                                    UsageMode::Observational
                                } else {
                                    UsageMode::Consuming
                                };
                                let arg_modes = self.collect_capture_modes_in_term(
                                    arg,
                                    ctx,
                                    capture_depth,
                                    arg_mode,
                                    implicit_noncopy,
                                )?;
                                merge_capture_modes(&mut modes, arg_modes);
                            }
                            return Ok(modes);
                        }
                    }
                }

                if mode == UsageMode::Observational {
                    let mut modes = self.collect_capture_modes_in_term(
                        f,
                        ctx,
                        capture_depth,
                        UsageMode::Observational,
                        implicit_noncopy,
                    )?;
                    let arg_modes = self.collect_capture_modes_in_term(
                        a,
                        ctx,
                        capture_depth,
                        UsageMode::Observational,
                        implicit_noncopy,
                    )?;
                    merge_capture_modes(&mut modes, arg_modes);
                    Ok(modes)
                } else {
                    let (arg_mode, f_mode) = match self.function_pi_info_from_term(f, ctx) {
                        Some((arg_ty, info, kind)) => {
                            let arg_mode = match info {
                                kernel::ast::BinderInfo::Implicit
                                | kernel::ast::BinderInfo::StrictImplicit => {
                                    if self.is_copy_type_in_ctx(ctx, &arg_ty) {
                                        UsageMode::Observational
                                    } else {
                                        UsageMode::Consuming
                                    }
                                }
                                kernel::ast::BinderInfo::Default => UsageMode::Consuming,
                            };
                            let f_mode = usage_mode_for_kind(kind);
                            (arg_mode, f_mode)
                        }
                        None => (UsageMode::Consuming, UsageMode::Consuming),
                    };
                    let f_eval_mode = match (&**f, f_mode) {
                        (Term::Var(_), UsageMode::Observational) => UsageMode::Observational,
                        (Term::Var(_), UsageMode::MutBorrow) => UsageMode::MutBorrow,
                        _ => UsageMode::Consuming,
                    };
                    let mut modes = self.collect_capture_modes_in_term(
                        f,
                        ctx,
                        capture_depth,
                        f_eval_mode,
                        implicit_noncopy,
                    )?;
                    let arg_modes = self.collect_capture_modes_in_term(
                        a,
                        ctx,
                        capture_depth,
                        arg_mode,
                        implicit_noncopy,
                    )?;
                    merge_capture_modes(&mut modes, arg_modes);
                    Ok(modes)
                }
            }
            Term::Lam(ty, body, info, _) => {
                let mut modes = self.collect_capture_modes_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                    implicit_noncopy,
                )?;
                let new_ctx = ctx.push(ty.clone());
                let is_implicit_noncopy = matches!(
                    info,
                    kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit
                ) && !self.is_copy_type_in_ctx(ctx, ty);
                let mut body_implicit_noncopy = implicit_noncopy.to_vec();
                body_implicit_noncopy.push(is_implicit_noncopy);
                let body_modes = self.collect_capture_modes_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                    &body_implicit_noncopy,
                )?;
                merge_capture_modes(&mut modes, body_modes);
                Ok(modes)
            }
            Term::Pi(ty, body, info, _) => {
                let mut modes = self.collect_capture_modes_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                    implicit_noncopy,
                )?;
                let new_ctx = ctx.push(ty.clone());
                let is_implicit_noncopy = matches!(
                    info,
                    kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit
                ) && !self.is_copy_type_in_ctx(ctx, ty);
                let mut body_implicit_noncopy = implicit_noncopy.to_vec();
                body_implicit_noncopy.push(is_implicit_noncopy);
                let body_modes = self.collect_capture_modes_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    UsageMode::Observational,
                    &body_implicit_noncopy,
                )?;
                merge_capture_modes(&mut modes, body_modes);
                Ok(modes)
            }
            Term::LetE(ty, val, body) => {
                let mut modes = self.collect_capture_modes_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                    implicit_noncopy,
                )?;
                let val_modes = self.collect_capture_modes_in_term(
                    val,
                    ctx,
                    capture_depth,
                    mode,
                    implicit_noncopy,
                )?;
                merge_capture_modes(&mut modes, val_modes);
                let new_ctx = ctx.push(ty.clone());
                let mut body_implicit_noncopy = implicit_noncopy.to_vec();
                body_implicit_noncopy.push(false);
                let body_modes = self.collect_capture_modes_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                    &body_implicit_noncopy,
                )?;
                merge_capture_modes(&mut modes, body_modes);
                Ok(modes)
            }
            Term::Fix(ty, body) => {
                let mut modes = self.collect_capture_modes_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                    implicit_noncopy,
                )?;
                let new_ctx = ctx.push(ty.clone());
                let mut body_implicit_noncopy = implicit_noncopy.to_vec();
                body_implicit_noncopy.push(false);
                let body_modes = self.collect_capture_modes_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                    &body_implicit_noncopy,
                )?;
                merge_capture_modes(&mut modes, body_modes);
                Ok(modes)
            }
            Term::Const(_, _)
            | Term::Sort(_)
            | Term::Ind(_, _)
            | Term::Ctor(_, _, _)
            | Term::Rec(_, _)
            | Term::Meta(_) => Ok(HashMap::new()),
        }
    }

    #[allow(dead_code)]
    fn infer_required_function_kind_in_term(
        &self,
        term: &Rc<Term>,
        ctx: &Context,
        capture_depth: usize,
        mode: UsageMode,
        captures: &[CaptureContext],
        implicit_noncopy: &[bool],
        outer_param_idx: Option<usize>,
    ) -> Result<FunctionKind, ElabError> {
        match &**term {
            Term::Var(idx) => {
                let mut capture_mode = None;
                for capture in captures {
                    if *idx >= capture.depth {
                        capture_mode = Some(match capture_mode {
                            Some(existing) => usage_mode_min(existing, capture.mode),
                            None => capture.mode,
                        });
                    }
                }
                let effective_mode = capture_mode.unwrap_or(mode);
                if implicit_noncopy_at(implicit_noncopy, *idx)
                    && effective_mode != UsageMode::Observational
                {
                    return Err(ElabError::ImplicitNonCopyUse {
                        index: *idx,
                        mode: usage_mode_label(effective_mode),
                    });
                }
                if outer_param_idx == Some(*idx) {
                    return Ok(FunctionKind::Fn);
                }
                if *idx >= capture_depth {
                    match effective_mode {
                        UsageMode::Observational => {}
                        UsageMode::MutBorrow => return Ok(FunctionKind::FnMut),
                        UsageMode::Consuming => {
                            if let Some(ty) = ctx.get(*idx) {
                                if self.is_mut_ref_type(ctx, &ty) {
                                    return Ok(FunctionKind::FnMut);
                                }
                                if !self.is_copy_type_in_ctx(ctx, &ty) {
                                    return Ok(FunctionKind::FnOnce);
                                }
                            } else {
                                return Ok(FunctionKind::FnOnce);
                            }
                        }
                    }
                }
                Ok(FunctionKind::Fn)
            }
            Term::App(f, a, _) => {
                if mode != UsageMode::Observational {
                    let (head, args) = Self::collect_core_app_spine(term);
                    if let Term::Rec(ind_name, _levels) = &*head {
                        if let Some(decl) = self.env.get_inductive(ind_name) {
                            let num_params = decl.num_params;
                            let num_indices =
                                self.count_pi_args(&decl.ty).saturating_sub(num_params);
                            let num_ctors = decl.ctors.len();
                            let motive_pos = num_params;
                            let indices_start = motive_pos + 1 + num_ctors;
                            let indices_end = indices_start + num_indices;
                            let mut required_kind = FunctionKind::Fn;
                            for (idx, arg) in args.iter().enumerate() {
                                let arg_mode = if idx < num_params
                                    || idx == motive_pos
                                    || (idx >= indices_start && idx < indices_end)
                                {
                                    UsageMode::Observational
                                } else {
                                    UsageMode::Consuming
                                };
                                let arg_kind = self.infer_required_function_kind_in_term(
                                    arg,
                                    ctx,
                                    capture_depth,
                                    arg_mode,
                                    captures,
                                    implicit_noncopy,
                                    outer_param_idx,
                                )?;
                                required_kind = function_kind_max(required_kind, arg_kind);
                                if required_kind == FunctionKind::FnOnce {
                                    return Ok(required_kind);
                                }
                            }
                            return Ok(required_kind);
                        }
                    }
                }
                if mode == UsageMode::Observational {
                    let needs_f = self.infer_required_function_kind_in_term(
                        f,
                        ctx,
                        capture_depth,
                        mode,
                        captures,
                        implicit_noncopy,
                        outer_param_idx,
                    )?;
                    let needs_a = self.infer_required_function_kind_in_term(
                        a,
                        ctx,
                        capture_depth,
                        mode,
                        captures,
                        implicit_noncopy,
                        outer_param_idx,
                    )?;
                    Ok(function_kind_max(needs_f, needs_a))
                } else {
                    let (arg_mode, f_mode) = match self.function_pi_info_from_term(f, ctx) {
                        Some((arg_ty, info, kind)) => {
                            let arg_mode = match info {
                                kernel::ast::BinderInfo::Implicit
                                | kernel::ast::BinderInfo::StrictImplicit => {
                                    if self.is_copy_type_in_ctx(ctx, &arg_ty) {
                                        UsageMode::Observational
                                    } else {
                                        UsageMode::Consuming
                                    }
                                }
                                kernel::ast::BinderInfo::Default => UsageMode::Consuming,
                            };
                            let f_mode = usage_mode_for_kind(kind);
                            (arg_mode, f_mode)
                        }
                        None => (UsageMode::Consuming, UsageMode::Consuming),
                    };
                    let f_eval_mode = match (&**f, f_mode) {
                        (Term::Var(_), UsageMode::Observational) => UsageMode::Observational,
                        (Term::Var(_), UsageMode::MutBorrow) => UsageMode::MutBorrow,
                        _ => UsageMode::Consuming,
                    };
                    let needs_f = self.infer_required_function_kind_in_term(
                        f,
                        ctx,
                        capture_depth,
                        f_eval_mode,
                        captures,
                        implicit_noncopy,
                        outer_param_idx,
                    )?;
                    let needs_a = self.infer_required_function_kind_in_term(
                        a,
                        ctx,
                        capture_depth,
                        arg_mode,
                        captures,
                        implicit_noncopy,
                        outer_param_idx,
                    )?;
                    Ok(function_kind_max(needs_f, needs_a))
                }
            }
            Term::Lam(ty, body, info, kind) => {
                let needs_ty = self.infer_required_function_kind_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                    captures,
                    implicit_noncopy,
                    outer_param_idx,
                )?;
                let new_ctx = ctx.push(ty.clone());
                let is_implicit_noncopy = matches!(
                    info,
                    kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit
                ) && !self.is_copy_type_in_ctx(ctx, ty);
                let mut body_captures = bump_captures(captures);
                body_captures.push(CaptureContext {
                    mode: usage_mode_for_kind(*kind),
                    depth: 1,
                });
                let mut body_implicit_noncopy = implicit_noncopy.to_vec();
                body_implicit_noncopy.push(is_implicit_noncopy);
                let body_outer_param_idx = outer_param_idx.map(|idx| idx + 1);
                let needs_body = self.infer_required_function_kind_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                    &body_captures,
                    &body_implicit_noncopy,
                    body_outer_param_idx,
                )?;
                Ok(function_kind_max(needs_ty, needs_body))
            }
            Term::Pi(ty, body, info, _) => {
                let needs_ty = self.infer_required_function_kind_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                    captures,
                    implicit_noncopy,
                    outer_param_idx,
                )?;
                let new_ctx = ctx.push(ty.clone());
                let is_implicit_noncopy = matches!(
                    info,
                    kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit
                ) && !self.is_copy_type_in_ctx(ctx, ty);
                let body_captures = bump_captures(captures);
                let mut body_implicit_noncopy = implicit_noncopy.to_vec();
                body_implicit_noncopy.push(is_implicit_noncopy);
                let body_outer_param_idx = outer_param_idx.map(|idx| idx + 1);
                let needs_body = self.infer_required_function_kind_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    UsageMode::Observational,
                    &body_captures,
                    &body_implicit_noncopy,
                    body_outer_param_idx,
                )?;
                Ok(function_kind_max(needs_ty, needs_body))
            }
            Term::LetE(ty, val, body) => {
                let needs_ty = self.infer_required_function_kind_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                    captures,
                    implicit_noncopy,
                    outer_param_idx,
                )?;
                let needs_val = self.infer_required_function_kind_in_term(
                    val,
                    ctx,
                    capture_depth,
                    mode,
                    captures,
                    implicit_noncopy,
                    outer_param_idx,
                )?;
                let new_ctx = ctx.push(ty.clone());
                let body_captures = bump_captures(captures);
                let mut body_implicit_noncopy = implicit_noncopy.to_vec();
                body_implicit_noncopy.push(false);
                let body_outer_param_idx = outer_param_idx.map(|idx| idx + 1);
                let needs_body = self.infer_required_function_kind_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                    &body_captures,
                    &body_implicit_noncopy,
                    body_outer_param_idx,
                )?;
                Ok(function_kind_max(
                    needs_ty,
                    function_kind_max(needs_val, needs_body),
                ))
            }
            Term::Fix(ty, body) => {
                let needs_ty = self.infer_required_function_kind_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                    captures,
                    implicit_noncopy,
                    outer_param_idx,
                )?;
                let new_ctx = ctx.push(ty.clone());
                let body_captures = bump_captures(captures);
                let mut body_implicit_noncopy = implicit_noncopy.to_vec();
                body_implicit_noncopy.push(false);
                let body_outer_param_idx = outer_param_idx.map(|idx| idx + 1);
                let needs_body = self.infer_required_function_kind_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                    &body_captures,
                    &body_implicit_noncopy,
                    body_outer_param_idx,
                )?;
                Ok(function_kind_max(needs_ty, needs_body))
            }
            Term::Const(_, _)
            | Term::Sort(_)
            | Term::Ind(_, _)
            | Term::Ctor(_, _, _)
            | Term::Rec(_, _)
            | Term::Meta(_) => Ok(FunctionKind::Fn),
        }
    }

    #[allow(dead_code)]
    fn infer_required_function_kind(
        &self,
        body: &Rc<Term>,
        ctx: &Context,
        outer_param_implicit_noncopy: bool,
    ) -> Result<FunctionKind, ElabError> {
        let (required_kind, _) =
            self.analyze_closure_captures(body, ctx, outer_param_implicit_noncopy)?;
        Ok(required_kind)
    }

    fn coerce_fn_to_kind(
        &mut self,
        term: Rc<Term>,
        arg_ty: Rc<Term>,
        info: kernel::ast::BinderInfo,
        kind: FunctionKind,
    ) -> Rc<Term> {
        if let Term::Lam(_, body, lam_info, _) = &*term {
            if *lam_info == info {
                let coerced = Rc::new(Term::Lam(arg_ty, body.clone(), info, kind));
                self.copy_metadata_if_any(&term, &coerced);
                return coerced;
            }
        }
        let shifted_term = term.shift(0, 1);
        let arg = Term::var(0);
        let body = Term::app(shifted_term, arg);
        let coerced = Term::lam_with_kind(arg_ty, body, info, kind);
        self.copy_metadata_if_any(&term, &coerced);
        coerced
    }

    fn try_coerce_fn_to_kind(
        &mut self,
        term: Rc<Term>,
        inferred_type: Rc<Term>,
        expected_type: Rc<Term>,
        span: Span,
    ) -> Result<Option<(Rc<Term>, Rc<Term>)>, ElabError> {
        let inferred_whnf = self.whnf(inferred_type.clone())?;
        let expected_whnf = self.whnf(expected_type.clone())?;
        match (&*inferred_whnf, &*expected_whnf) {
            (
                Term::Pi(arg_ty, ret_ty, info, got_kind),
                Term::Pi(exp_arg_ty, exp_ret_ty, exp_info, exp_kind),
            ) => {
                if *got_kind == *exp_kind || !function_kind_leq(*got_kind, *exp_kind) {
                    return Ok(None);
                }
                if info != exp_info {
                    return Ok(None);
                }
                self.unify_with_span(arg_ty, exp_arg_ty, span)?;
                self.unify_with_span(ret_ty, exp_ret_ty, span)?;
                let coerced =
                    self.coerce_fn_to_kind(term, exp_arg_ty.clone(), *exp_info, *exp_kind);
                let ctx = self.build_context();
                let coerced_ctx = ctx.push(exp_arg_ty.clone());
                let outer_param_implicit_noncopy = matches!(
                    exp_info,
                    kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit
                ) && !self.is_copy_type_in_ctx(&ctx, exp_arg_ty);
                if let Term::Lam(_, body, _, _) = &*coerced {
                    let (_, capture_modes) = self.analyze_closure_captures(
                        body,
                        &coerced_ctx,
                        outer_param_implicit_noncopy,
                    )?;
                    self.record_capture_modes(&coerced, capture_modes);
                }
                Ok(Some((coerced, expected_type)))
            }
            _ => Ok(None),
        }
    }

    fn recursor_type(&self, ind_name: &str, levels: &[Level]) -> Result<Rc<Term>, ElabError> {
        let decl = self.env.get_inductive(ind_name).ok_or_else(|| {
            ElabError::UnknownInductive(
                ind_name.to_string(),
                Span {
                    start: 0,
                    end: 0,
                    line: 0,
                    col: 0,
                },
            )
        })?;
        Ok(compute_recursor_type(decl, levels))
    }

    fn build_recursor_levels(
        &self,
        decl: &kernel::ast::InductiveDecl,
        motive_level: Level,
    ) -> Vec<Level> {
        let mut levels: Vec<Level> = decl
            .univ_params
            .iter()
            .map(|name| Level::Param(name.clone()))
            .collect();
        levels.push(motive_level);
        levels
    }

    fn extract_result_sort_level(&self, ty: Rc<Term>, span: Span) -> Result<Level, ElabError> {
        let mut current = self.whnf(ty)?;
        loop {
            match &*current {
                Term::Pi(_, body, _, _) => {
                    current = self.whnf(body.clone())?;
                }
                Term::Sort(level) => return Ok(level.clone()),
                _ => {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: self.pretty_term(&current),
                        span,
                    });
                }
            }
        }
    }

    fn apply_pi_type(
        &self,
        ty: Rc<Term>,
        arg: &Rc<Term>,
        span: Span,
    ) -> Result<Rc<Term>, ElabError> {
        let ty_whnf = self.whnf(ty)?;
        if let Term::Pi(_, body, _, _) = &*ty_whnf {
            Ok(body.subst(0, arg))
        } else {
            Err(ElabError::InferenceError(
                TypeError::ExpectedFunction(ty_whnf),
                span,
            ))
        }
    }

    fn infer_app_spine(
        &mut self,
        head: SurfaceTerm,
        args: Vec<(SurfaceTerm, bool)>,
        span: Span,
    ) -> Result<(Rc<Term>, Rc<Term>), ElabError> {
        if let SurfaceTermKind::Rec(ind_name) = &head.kind {
            self.infer_rec_application(ind_name.clone(), args, span)
        } else {
            let (mut f_elab, mut f_ty) = self.infer(head)?;

            for (arg, is_explicit) in args {
                let mut f_ty_whnf = self.whnf(f_ty.clone())?;

                // Insert implicit arguments
                loop {
                    match &*f_ty_whnf {
                        Term::Pi(_, ret_ty, info, _) => match info {
                            kernel::ast::BinderInfo::Implicit
                            | kernel::ast::BinderInfo::StrictImplicit => {
                                if is_explicit {
                                    let meta_id = self.meta_counter;
                                    self.meta_counter += 1;
                                    let meta_term = Rc::new(Term::Meta(meta_id));
                                    self.meta_contexts.insert(
                                        meta_id,
                                        MetaContext {
                                            binders: self.locals.clone(),
                                        },
                                    );

                                    f_elab = Term::app(f_elab, meta_term.clone());
                                    f_ty = ret_ty.subst(0, &meta_term);
                                    f_ty_whnf = self.whnf(f_ty.clone())?;
                                } else {
                                    break;
                                }
                            }
                            kernel::ast::BinderInfo::Default => {
                                if !is_explicit {
                                    return Err(ElabError::TypeMismatch {
                                        expected: "Implicit binder".to_string(),
                                        got: "Explicit argument".to_string(),
                                        span,
                                    });
                                }
                                break;
                            }
                        },
                        _ => break,
                    }
                }

                if let Term::Pi(arg_ty, ret_ty, _, _) = &*f_ty_whnf {
                    let x_elab = self.check(arg, &arg_ty)?;
                    f_elab = Term::app(f_elab, x_elab.clone());
                    f_ty = ret_ty.subst(0, &x_elab);
                } else {
                    return Err(ElabError::InferenceError(
                        TypeError::ExpectedFunction(f_ty_whnf),
                        span,
                    ));
                }
            }

            Ok((f_elab, f_ty))
        }
    }

    pub fn infer(&mut self, term: SurfaceTerm) -> Result<(Rc<Term>, Rc<Term>), ElabError> {
        let span = term.span;
        let kind = term.kind;
        let result = match kind {
            SurfaceTermKind::Var(name) => {
                let elab_term = self
                    .resolve_name(&name, span)?
                    .ok_or(ElabError::UnboundVariable(name, span))?;
                let ctx = self.build_context();
                let ty = infer_type(self.env, &ctx, elab_term.clone())
                    .map_err(|e| ElabError::InferenceError(e, span))?;
                Ok((elab_term, ty))
            }
            SurfaceTermKind::Sort(l) => {
                let term = Rc::new(Term::Sort(l.clone()));
                let ty = Rc::new(Term::Sort(Level::Succ(Box::new(l))));
                Ok((term, ty))
            }
            SurfaceTermKind::Index(base, index) => {
                let base_term = *base;
                let index_term = *index;
                let (_base_elab, base_ty) = self.infer(base_term.clone())?;
                let base_ty_whnf = self.whnf(base_ty)?;
                let (ind_name, _) =
                    self.extract_inductive_info(&base_ty_whnf).ok_or_else(|| {
                        ElabError::TypeMismatch {
                            expected: "indexable container".to_string(),
                            got: self.pretty_term(&base_ty_whnf),
                            span,
                        }
                    })?;

                let index_fn = match ind_name.as_str() {
                    "VecDyn" => "index_vec_dyn",
                    "Slice" => "index_slice",
                    "Array" => "index_array",
                    _ => {
                        return Err(ElabError::TypeMismatch {
                            expected: "indexable container".to_string(),
                            got: self.pretty_term(&base_ty_whnf),
                            span,
                        })
                    }
                };

                let index_head = SurfaceTerm {
                    kind: SurfaceTermKind::Var(index_fn.to_string()),
                    span,
                };
                let app1 = SurfaceTerm {
                    kind: SurfaceTermKind::App(Box::new(index_head), Box::new(base_term), true),
                    span,
                };
                let app2 = SurfaceTerm {
                    kind: SurfaceTermKind::App(Box::new(app1), Box::new(index_term), true),
                    span,
                };
                self.infer(app2)
            }
            SurfaceTermKind::App(f, x, is_explicit) => {
                let term = SurfaceTerm {
                    kind: SurfaceTermKind::App(f, x, is_explicit),
                    span,
                };
                let (head, args) = collect_app_spine(term);
                if let SurfaceTermKind::Var(name) = &head.kind {
                    if name == "Ref" && args.len() == 3 {
                        if let Some(label) = Self::extract_lifetime_label(&args[0].0) {
                            let args_without_label = args[1..].to_vec();
                            let (core_term, core_ty) =
                                self.infer_app_spine(head.clone(), args_without_label, span)?;
                            let labeled_term = self.attach_ref_label(&core_term, label);
                            return Ok((labeled_term, core_ty));
                        }
                    }
                    if name == "Ref" && args.len() == 2 {
                        let (core_term, core_ty) =
                            self.infer_app_spine(head.clone(), args.clone(), span)?;
                        let label = self.fresh_elided_label();
                        let labeled_term = self.attach_ref_label(&core_term, label);
                        return Ok((labeled_term, core_ty));
                    }
                }
                self.infer_app_spine(head, args, span)
            }
            SurfaceTermKind::Pi(name, binder_info, kind_opt, ty, body) => {
                self.validate_ref_lifetime_elision_for_pi(&ty, &body)?;
                // Infer the domain type and check it's a Sort
                let (ty_elab, ty_ty) = self.infer_type(*ty)?;
                let ty_ty_whnf = self.whnf(ty_ty)?;
                if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: self.pretty_term(&ty_ty_whnf),
                        span,
                    });
                }

                self.locals.push((name, ty_elab.clone()));
                let (body_elab, _body_ty) = self.infer_type(*body)?;
                self.locals.pop();

                let pi_kind = kind_opt.unwrap_or(FunctionKind::Fn);
                let pi_term = Rc::new(Term::Pi(ty_elab, body_elab, binder_info, pi_kind));
                let ty_ty = infer_type(self.env, &self.build_context(), pi_term.clone())
                    .map_err(|e| ElabError::InferenceError(e, span))?;

                Ok((pi_term, ty_ty))
            }
            SurfaceTermKind::Lam(name, binder_info, kind_opt, ty, body) => {
                // Infer the type annotation and check it's a Sort
                let (ty_elab, ty_ty) = self.infer_type(*ty)?;
                let ty_ty_whnf = self.whnf(ty_ty)?;
                if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: self.pretty_term(&ty_ty_whnf),
                        span,
                    });
                }
                self.locals.push((name.clone(), ty_elab.clone()));
                let (body_elab, body_ty) = self.infer(*body)?;
                let ctx = self.build_context();
                let outer_param_implicit_noncopy = matches!(
                    binder_info,
                    kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit
                ) && !self.is_copy_type_in_ctx(&ctx, &ty_elab);
                let (required_kind, capture_modes) =
                    self.analyze_closure_captures(&body_elab, &ctx, outer_param_implicit_noncopy)?;
                self.locals.pop();

                if let Some(annotated) = kind_opt {
                    if !function_kind_leq(required_kind, annotated) {
                        return Err(ElabError::FunctionKindAnnotationTooSmall {
                            annotated,
                            required: required_kind,
                            span,
                        });
                    }
                }
                let lam_kind = kind_opt.unwrap_or(required_kind);

                let lam_term =
                    Rc::new(Term::Lam(ty_elab.clone(), body_elab, binder_info, lam_kind));
                self.record_capture_modes(&lam_term, capture_modes);
                let lam_ty = Rc::new(Term::Pi(ty_elab, body_ty, binder_info, lam_kind));
                Ok((lam_term, lam_ty))
            }
            SurfaceTermKind::Let(name, ty, val, body) => {
                // Infer the type annotation and check it's a Sort
                let (ty_elab, ty_ty) = self.infer_type(*ty)?;
                let ty_ty_whnf = self.whnf(ty_ty)?;
                if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: self.pretty_term(&ty_ty_whnf),
                        span,
                    });
                }
                let val_elab = self.check(*val, &ty_elab)?;

                self.locals.push((name, ty_elab.clone()));
                let (body_elab, body_ty) = self.infer(*body)?;
                self.locals.pop();

                let let_term = Rc::new(Term::LetE(ty_elab, val_elab, body_elab));
                Ok((let_term, body_ty))
            }
            SurfaceTermKind::Hole => {
                let meta_id = self.meta_counter;
                self.meta_counter += 1;
                let meta_term = Rc::new(Term::Meta(meta_id));
                self.meta_contexts.insert(
                    meta_id,
                    MetaContext {
                        binders: self.locals.clone(),
                    },
                );

                let type_meta_id = self.meta_counter;
                self.meta_counter += 1;
                let type_meta_term = Rc::new(Term::Meta(type_meta_id));
                self.meta_contexts.insert(
                    type_meta_id,
                    MetaContext {
                        binders: self.locals.clone(),
                    },
                );

                Ok((meta_term, type_meta_term))
            }
            SurfaceTermKind::Ind(name) => {
                let decl = self
                    .env
                    .get_inductive(&name)
                    .ok_or_else(|| ElabError::UnknownInductive(name.clone(), span))?;
                let ind_term = Rc::new(Term::Ind(name, vec![]));
                let ty = decl.ty.clone();
                Ok((ind_term, ty))
            }
            SurfaceTermKind::Ctor(ind_name, idx) => {
                let decl = self
                    .env
                    .get_inductive(&ind_name)
                    .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?;
                let ctor = decl
                    .ctors
                    .get(idx)
                    .ok_or_else(|| ElabError::NotImplemented(span))?;
                let ctor_term = Rc::new(Term::Ctor(ind_name, idx, vec![]));
                let ty = ctor.ty.clone();
                Ok((ctor_term, ty))
            }
            SurfaceTermKind::Rec(ind_name) => {
                let _ = self
                    .env
                    .get_inductive(&ind_name)
                    .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?;
                Err(ElabError::RecursorNeedsMotive(span))
            }
            SurfaceTermKind::Match(scrutinee, ret_type, cases) => {
                self.elaborate_match(*scrutinee, *ret_type, cases, span)
            }
            SurfaceTermKind::Eval(code, cap) => {
                if self.in_type_context {
                    return Err(ElabError::EvalInType(span));
                }
                let eval_term = SurfaceTerm {
                    kind: SurfaceTermKind::Var("eval".to_string()),
                    span,
                };
                let app1 = SurfaceTerm {
                    kind: SurfaceTermKind::App(Box::new(eval_term), code, true),
                    span,
                };
                let app2 = SurfaceTerm {
                    kind: SurfaceTermKind::App(Box::new(app1), cap, true),
                    span,
                };
                self.infer(app2)
            }
            SurfaceTermKind::Fix(name, ty, body) => {
                // Infer the type annotation and check it's a Sort
                let (ty_elab, ty_ty) = self.infer_type(*ty)?;
                let ty_ty_whnf = self.whnf(ty_ty)?;
                if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: self.pretty_term(&ty_ty_whnf),
                        span,
                    });
                }

                // Fix f:T. body. body should have type T under f:T.
                self.locals.push((name, ty_elab.clone()));
                let body_elab = self.check(*body, &ty_elab)?;
                let ctx = self.build_context();
                let (_, capture_modes) = self.analyze_closure_captures(&body_elab, &ctx, false)?;
                self.locals.pop();

                let fix_term = Rc::new(Term::Fix(ty_elab.clone(), body_elab));
                self.record_capture_modes(&fix_term, capture_modes);
                Ok((fix_term, ty_elab))
            }
        };
        result.map(|(term, ty)| {
            self.record_span(&term, span);
            (term, ty)
        })
    }

    fn infer_rec_application(
        &mut self,
        ind_name: String,
        args: Vec<(SurfaceTerm, bool)>,
        span: Span,
    ) -> Result<(Rc<Term>, Rc<Term>), ElabError> {
        let decl = self
            .env
            .get_inductive(&ind_name)
            .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?;

        let num_params = decl.num_params;
        if args.len() <= num_params {
            return Err(ElabError::RecursorNeedsMotive(span));
        }

        // Infer the motive argument to determine the universe level.
        let (motive_term, motive_ty) = self.infer_type(args[num_params].0.clone())?;
        let motive_level = self.extract_result_sort_level(motive_ty.clone(), span)?;
        let levels = self.build_recursor_levels(decl, motive_level.clone());

        check_elimination_restriction(self.env, &ind_name, &levels)
            .map_err(|e| ElabError::InferenceError(e, span))?;

        let mut f_elab = Rc::new(Term::Rec(ind_name.clone(), levels.clone()));
        let mut f_ty = self.recursor_type(&ind_name, &levels)?;

        for (idx, (arg, is_explicit)) in args.into_iter().enumerate() {
            let mut f_ty_whnf = self.whnf(f_ty.clone())?;

            // Insert implicit arguments
            loop {
                match &*f_ty_whnf {
                    Term::Pi(_, ret_ty, info, _) => match info {
                        kernel::ast::BinderInfo::Implicit
                        | kernel::ast::BinderInfo::StrictImplicit => {
                            if is_explicit {
                                let meta_id = self.meta_counter;
                                self.meta_counter += 1;
                                let meta_term = Rc::new(Term::Meta(meta_id));
                                self.meta_contexts.insert(
                                    meta_id,
                                    MetaContext {
                                        binders: self.locals.clone(),
                                    },
                                );

                                f_elab = Term::app(f_elab, meta_term.clone());
                                f_ty = ret_ty.subst(0, &meta_term);
                                f_ty_whnf = self.whnf(f_ty.clone())?;
                            } else {
                                break;
                            }
                        }
                        kernel::ast::BinderInfo::Default => {
                            if !is_explicit {
                                return Err(ElabError::TypeMismatch {
                                    expected: "Implicit binder".to_string(),
                                    got: "Explicit argument".to_string(),
                                    span,
                                });
                            }
                            break;
                        }
                    },
                    _ => break,
                }
            }

            if let Term::Pi(arg_ty, ret_ty, _, _) = &*f_ty_whnf {
                let x_elab = if idx == num_params {
                    self.unify_with_span(&motive_ty, &arg_ty, span)?;
                    motive_term.clone()
                } else {
                    self.check(arg, &arg_ty)?
                };
                f_elab = Term::app(f_elab, x_elab.clone());
                f_ty = ret_ty.subst(0, &x_elab);
            } else {
                return Err(ElabError::InferenceError(
                    TypeError::ExpectedFunction(f_ty_whnf),
                    span,
                ));
            }
        }

        Ok((f_elab, f_ty))
    }

    pub fn check(
        &mut self,
        term: SurfaceTerm,
        expected_type: &Rc<Term>,
    ) -> Result<Rc<Term>, ElabError> {
        let span = term.span;
        let kind = term.kind;
        let result = match (kind.clone(), &**expected_type) {
            (
                SurfaceTermKind::Lam(name, binder_info, kind_opt, ty, body),
                Term::Pi(expected_arg_ty, expected_ret_ty, expected_info, expected_kind),
            ) => {
                if binder_info == kernel::ast::BinderInfo::Default
                    && *expected_info == kernel::ast::BinderInfo::Implicit
                {
                    // Insert implicit lambda
                    let implicit_name = format!("_imp_{}", self.locals.len());
                    self.locals.push((implicit_name, expected_arg_ty.clone()));
                    // Recursively check the SAME term against the body type
                    // We reconstruct the Lam term because we don't have ownership of the original text separate from destructuring
                    let inner = self.check(
                        SurfaceTerm {
                            kind: SurfaceTermKind::Lam(name, binder_info, kind_opt, ty, body),
                            span,
                        },
                        expected_ret_ty,
                    )?;
                    let ctx = self.build_context();
                    let outer_param_implicit_noncopy = matches!(
                        expected_info,
                        kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit
                    ) && !self
                        .is_copy_type_in_ctx(&ctx, expected_arg_ty);
                    let (_, capture_modes) =
                        self.analyze_closure_captures(&inner, &ctx, outer_param_implicit_noncopy)?;
                    self.locals.pop();
                    let lam_term = Rc::new(Term::Lam(
                        expected_arg_ty.clone(),
                        inner,
                        *expected_info,
                        *expected_kind,
                    ));
                    self.record_capture_modes(&lam_term, capture_modes);
                    Ok(lam_term)
                } else {
                    // Standard checking - verify the type annotation is a Sort (any level)
                    let (ty_elab, ty_ty) = self.infer_type(*ty)?;
                    let ty_ty_whnf = self.whnf(ty_ty)?;
                    if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                        return Err(ElabError::TypeMismatch {
                            expected: "Sort".to_string(),
                            got: self.pretty_term(&ty_ty_whnf),
                            span,
                        });
                    }
                    // Unify the provided type with the expected argument type
                    self.unify_with_span(&ty_elab, expected_arg_ty, span)?;

                    self.locals.push((name.clone(), expected_arg_ty.clone()));
                    let body_elab = self.check(*body, expected_ret_ty)?;
                    let ctx = self.build_context();
                    let outer_param_implicit_noncopy = matches!(
                        binder_info,
                        kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit
                    ) && !self
                        .is_copy_type_in_ctx(&ctx, expected_arg_ty);
                    let (required_kind, capture_modes) = self.analyze_closure_captures(
                        &body_elab,
                        &ctx,
                        outer_param_implicit_noncopy,
                    )?;
                    self.locals.pop();

                    if let Some(annotated) = kind_opt {
                        if !function_kind_leq(required_kind, annotated) {
                            return Err(ElabError::FunctionKindAnnotationTooSmall {
                                annotated,
                                required: required_kind,
                                span,
                            });
                        }
                    }

                    let lam_kind = kind_opt.unwrap_or(required_kind);
                    if !function_kind_leq(lam_kind, *expected_kind) {
                        return Err(ElabError::FunctionKindMismatch {
                            expected: *expected_kind,
                            got: lam_kind,
                            span,
                        });
                    }

                    let lam_term = Rc::new(Term::Lam(
                        expected_arg_ty.clone(),
                        body_elab,
                        binder_info,
                        lam_kind,
                    ));
                    self.record_capture_modes(&lam_term, capture_modes);

                    if lam_kind != *expected_kind && function_kind_leq(lam_kind, *expected_kind) {
                        let coerced = self.coerce_fn_to_kind(
                            lam_term,
                            expected_arg_ty.clone(),
                            *expected_info,
                            *expected_kind,
                        );
                        let ctx = self.build_context();
                        let coerced_ctx = ctx.push(expected_arg_ty.clone());
                        let coerced_outer_param_implicit_noncopy = matches!(
                            expected_info,
                            kernel::ast::BinderInfo::Implicit
                                | kernel::ast::BinderInfo::StrictImplicit
                        ) && !self
                            .is_copy_type_in_ctx(&ctx, expected_arg_ty);
                        if let Term::Lam(_, body, _, _) = &*coerced {
                            let (_, capture_modes) = self.analyze_closure_captures(
                                body,
                                &coerced_ctx,
                                coerced_outer_param_implicit_noncopy,
                            )?;
                            self.record_capture_modes(&coerced, capture_modes);
                        }
                        Ok(coerced)
                    } else {
                        Ok(lam_term)
                    }
                }
            }
            _ => {
                let (mut elab_term, mut inferred_type) = self.infer(SurfaceTerm { kind, span })?;

                // Insert implicit arguments if inferred type has leading implicit Pis
                // This handles cases like checking `nil` against `List Nat`
                let mut inferred_whnf = self.whnf(inferred_type.clone())?;
                loop {
                    match &*inferred_whnf {
                        Term::Pi(_, ret_ty, info, _)
                            if *info == kernel::ast::BinderInfo::Implicit
                                || *info == kernel::ast::BinderInfo::StrictImplicit =>
                        {
                            // Insert a meta for this implicit argument
                            let meta_id = self.meta_counter;
                            self.meta_counter += 1;
                            let meta_term = Rc::new(Term::Meta(meta_id));
                            self.meta_contexts.insert(
                                meta_id,
                                MetaContext {
                                    binders: self.locals.clone(),
                                },
                            );

                            elab_term = Term::app(elab_term, meta_term.clone());
                            inferred_type = ret_ty.subst(0, &meta_term);
                            inferred_whnf = self.whnf(inferred_type.clone())?;
                        }
                        _ => break,
                    }
                }

                let inferred_kind = self.whnf(inferred_type.clone())?;
                let expected_kind = self.whnf(expected_type.clone())?;
                if let (Term::Pi(_, _, _, got_kind), Term::Pi(_, _, _, exp_kind)) =
                    (&*inferred_kind, &*expected_kind)
                {
                    if function_kind_leq(*got_kind, *exp_kind) && *got_kind != *exp_kind {
                        if let Some((coerced_term, coerced_type)) = self.try_coerce_fn_to_kind(
                            elab_term.clone(),
                            inferred_type.clone(),
                            expected_type.clone(),
                            span,
                        )? {
                            elab_term = coerced_term;
                            inferred_type = coerced_type;
                        }
                    } else if !function_kind_leq(*got_kind, *exp_kind) {
                        return Err(ElabError::FunctionKindMismatch {
                            expected: *exp_kind,
                            got: *got_kind,
                            span,
                        });
                    }
                }

                self.unify_with_span(&inferred_type, expected_type, span)?;
                Ok(elab_term)
            }
        };
        result.map(|term| {
            self.record_span(&term, span);
            term
        })
    }

    /// Elaborate a match expression to a recursor application
    fn elaborate_match(
        &mut self,
        scrutinee: SurfaceTerm,
        ret_type: SurfaceTerm,
        cases: Vec<(String, Vec<String>, SurfaceTerm)>,
        span: Span,
    ) -> Result<(Rc<Term>, Rc<Term>), ElabError> {
        // Infer the scrutinee type to get the inductive name
        let (scrut_elab, scrut_ty) = self.infer(scrutinee)?;

        // Extract the inductive name and args from the scrutinee type
        let scrut_ty_whnf = self.whnf(scrut_ty.clone())?;
        let (ind_name, ind_args) =
            self.extract_inductive_info(&scrut_ty_whnf)
                .ok_or_else(|| ElabError::TypeMismatch {
                    expected: "inductive type".to_string(),
                    got: self.pretty_term(&scrut_ty_whnf),
                    span,
                })?;

        // Get the inductive declaration
        let decl = self
            .env
            .get_inductive(&ind_name)
            .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?
            .clone();

        // Validate match cases: no unknown constructors, no duplicates, and exhaustive coverage.
        let ctor_names: HashSet<String> = decl.ctors.iter().map(|ctor| ctor.name.clone()).collect();
        let mut seen_cases: HashSet<String> = HashSet::new();
        for (case_name, _, _) in &cases {
            if !ctor_names.contains(case_name) {
                return Err(ElabError::UnknownMatchCase {
                    ind: ind_name.clone(),
                    ctor: case_name.clone(),
                    span,
                });
            }
            if !seen_cases.insert(case_name.clone()) {
                return Err(ElabError::DuplicateMatchCase {
                    ind: ind_name.clone(),
                    ctor: case_name.clone(),
                    span,
                });
            }
        }

        let mut missing = Vec::new();
        for ctor in &decl.ctors {
            if !seen_cases.contains(&ctor.name) {
                missing.push(ctor.name.clone());
            }
        }
        if !missing.is_empty() {
            return Err(ElabError::NonExhaustiveMatch {
                ind: ind_name.clone(),
                missing,
                span,
            });
        }

        // Elaborate the return type (motive body) and ensure it is a type
        let (ret_type_elab, ret_type_ty) = self.infer_type(ret_type)?;
        let ret_type_ty_whnf = self.whnf(ret_type_ty)?;
        if !matches!(&*ret_type_ty_whnf, Term::Sort(_)) {
            return Err(ElabError::TypeMismatch {
                expected: "Sort".to_string(),
                got: self.pretty_term(&ret_type_ty_whnf),
                span,
            });
        }

        // Split params/indices from scrutinee type arguments
        let num_params = decl.num_params;
        let (param_args, index_args) = if ind_args.len() >= num_params {
            (
                ind_args[..num_params].to_vec(),
                ind_args[num_params..].to_vec(),
            )
        } else {
            return Err(ElabError::TypeMismatch {
                expected: format!("{} parameters", num_params),
                got: format!("{}", ind_args.len()),
                span,
            });
        };

        // Instantiate index binder types using parameters
        let mut index_types = Vec::new();
        let mut current = self.instantiate_params(decl.ty.clone(), &param_args);
        while let Term::Pi(dom, body, _, _) = &*current {
            index_types.push(dom.clone());
            current = body.clone();
        }

        // Build major type: Ind params indices (with index vars)
        let mut major_ty = Rc::new(Term::Ind(ind_name.clone(), vec![]));
        for param in &param_args {
            major_ty = Term::app(major_ty, param.shift(0, index_types.len()));
        }
        for i in 0..index_types.len() {
            let idx = index_types.len() - 1 - i;
            major_ty = Term::app(major_ty, Rc::new(Term::Var(idx)));
        }

        // Build motive as lambdas over indices then major.
        // We attach capture/span metadata here because this motive is synthesized
        // and may still capture surrounding locals in dependent matches.
        let index_count = index_types.len();
        let mut motive_binders = Vec::with_capacity(index_count + 1);
        for (idx, ty) in index_types.iter().enumerate() {
            motive_binders.push((
                format!("_match_idx{}", idx),
                ty.clone(),
                kernel::ast::BinderInfo::Default,
                FunctionKind::Fn,
            ));
        }
        motive_binders.push((
            "_match_major".to_string(),
            major_ty.clone(),
            kernel::ast::BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let motive =
            self.wrap_synthesized_lambdas(&motive_binders, ret_type_elab.shift(0, index_count + 1), span)?;

        // Determine universe level from motive type
        let motive_ty = infer_type(self.env, &self.build_context(), motive.clone())
            .map_err(|e| ElabError::InferenceError(e, span))?;
        let motive_level = self.extract_result_sort_level(motive_ty, span)?;
        let levels = self.build_recursor_levels(&decl, motive_level.clone());

        check_elimination_restriction(self.env, &ind_name, &levels)
            .map_err(|e| ElabError::InferenceError(e, span))?;

        // Start building the recursor application: Ind.rec [params] motive
        let rec_term = Rc::new(Term::Rec(ind_name.clone(), levels.clone()));
        let mut result = rec_term;

        // Apply parameters first
        for arg in &param_args {
            result = Term::app(result, arg.clone());
        }

        // Apply motive
        result = Term::app(result, motive.clone());

        // Compute expected minor premise types from recursor type
        let mut rec_ty = self.recursor_type(&ind_name, &levels)?;
        for arg in &param_args {
            rec_ty = self.apply_pi_type(rec_ty, arg, span)?;
        }
        rec_ty = self.apply_pi_type(rec_ty, &motive, span)?;

        // Elaborate each case and apply as a minor premise
        for ctor in decl.ctors.iter() {
            let current_whnf = self.whnf(rec_ty.clone())?;
            let minor_ty = if let Term::Pi(dom, _, _, _) = &*current_whnf {
                dom.clone()
            } else {
                return Err(ElabError::InferenceError(
                    TypeError::ExpectedFunction(current_whnf),
                    span,
                ));
            };

            let case = cases.iter().find(|(name, _, _)| name == &ctor.name);
            let case_elab = match case {
                Some((_, bindings, body)) => {
                    let ctor_inst = self.instantiate_params(ctor.ty.clone(), &param_args);
                    let ctor_arg_count = self.count_pi_args(&ctor_inst);
                    let recursive_args = self.find_recursive_args(&ctor_inst, &ind_name);
                    let expected_binders = ctor_arg_count + recursive_args.len();
                    let (binders, result_ty) =
                        self.split_minor_premise(&minor_ty, expected_binders);
                    self.elaborate_case(bindings, body, &binders, &result_ty, span)?
                }
                None => {
                    // Missing case - this is an error in a proper implementation
                    // For now, we use a hole (metavariable)
                    let meta_id = self.meta_counter;
                    self.meta_counter += 1;
                    let meta = Rc::new(Term::Meta(meta_id));
                    self.meta_contexts.insert(
                        meta_id,
                        MetaContext {
                            binders: self.locals.clone(),
                        },
                    );
                    meta
                }
            };

            result = Term::app(result, case_elab.clone());
            rec_ty = self.apply_pi_type(rec_ty, &case_elab, span)?;
        }

        // Apply indices (if any), then scrutinee
        for arg in &index_args {
            result = Term::app(result, arg.clone());
        }
        result = Term::app(result, scrut_elab.clone());

        // The result type is motive applied to indices and scrutinee
        let mut result_ty = motive.clone();
        for arg in &index_args {
            result_ty = Term::app(result_ty, arg.clone());
        }
        result_ty = Term::app(result_ty, scrut_elab.clone());

        Ok((result, result_ty))
    }

    /// Extract the inductive type name and arguments from a type
    fn extract_inductive_info(&self, ty: &Rc<Term>) -> Option<(String, Vec<Rc<Term>>)> {
        match &**ty {
            Term::Ind(name, _) => Some((name.clone(), Vec::new())),
            Term::App(f, a, _) => {
                let (name, mut args) = self.extract_inductive_info(f)?;
                args.push(a.clone());
                Some((name, args))
            }
            _ => None,
        }
    }

    /// Instantiate parameters in a constructor type
    fn instantiate_params(&self, mut ty: Rc<Term>, params: &[Rc<Term>]) -> Rc<Term> {
        for param in params {
            if let Term::Pi(_, body, _, _) = &*ty {
                ty = body.subst(0, param);
            } else {
                break;
            }
        }
        ty
    }

    /// Elaborate a single case branch against an expected minor premise type.
    fn wrap_synthesized_lambdas(
        &mut self,
        binders: &[(String, Rc<Term>, kernel::ast::BinderInfo, FunctionKind)],
        body: Rc<Term>,
        span: Span,
    ) -> Result<Rc<Term>, ElabError> {
        let base_locals = self.locals.len();
        for (name, ty, _, _) in binders.iter() {
            self.locals.push((name.clone(), ty.clone()));
        }

        let wrapped = (|| -> Result<Rc<Term>, ElabError> {
            let mut result = body;
            for (_name, ty, info, kind) in binders.iter().rev() {
                let ctx = self.build_context();
                let (_, capture_modes) = self.analyze_closure_captures(&result, &ctx, false)?;
                self.locals.pop();
                let lam = Rc::new(Term::Lam(ty.clone(), result, *info, *kind));
                self.record_capture_modes(&lam, capture_modes);
                self.record_span(&lam, span);
                result = lam;
            }
            Ok(result)
        })();

        self.locals.truncate(base_locals);
        wrapped
    }

    /// Elaborate a single case branch against an expected minor premise type.
    fn elaborate_case(
        &mut self,
        bindings: &[String],
        body: &SurfaceTerm,
        binders: &[(Rc<Term>, kernel::ast::BinderInfo, FunctionKind)],
        result_ty: &Rc<Term>,
        span: Span,
    ) -> Result<Rc<Term>, ElabError> {
        let explicit_arg_count = binders
            .iter()
            .filter(|(_, info, _)| *info == kernel::ast::BinderInfo::Default)
            .count();

        let padded_bindings: Vec<String> = if bindings.len() < explicit_arg_count {
            let mut b = bindings.to_vec();
            for i in bindings.len()..explicit_arg_count {
                b.push(format!("_arg{}", i));
            }
            b
        } else {
            bindings[..explicit_arg_count.min(bindings.len())].to_vec()
        };

        let mut binder_names = Vec::with_capacity(binders.len());
        let mut binding_idx = 0;
        for (i, (arg_ty, info, _)) in binders.iter().enumerate() {
            let name = if *info == kernel::ast::BinderInfo::Default {
                let n = padded_bindings
                    .get(binding_idx)
                    .cloned()
                    .unwrap_or_else(|| format!("_explicit{}", i));
                binding_idx += 1;
                n
            } else {
                format!("_implicit{}", i)
            };
            self.locals.push((name.clone(), arg_ty.clone()));
            binder_names.push(name);
        }

        let result_ty = self.whnf(result_ty.clone())?;
        let body_elab = self.check(body.clone(), &result_ty)?;

        for _ in 0..binders.len() {
            self.locals.pop();
        }

        let binder_specs: Vec<(String, Rc<Term>, kernel::ast::BinderInfo, FunctionKind)> = binders
            .iter()
            .zip(binder_names.iter())
            .map(|((arg_ty, info, kind), name)| (name.clone(), arg_ty.clone(), *info, *kind))
            .collect();

        self.wrap_synthesized_lambdas(&binder_specs, body_elab, span)
    }

    fn split_minor_premise(
        &self,
        minor_ty: &Rc<Term>,
        expected_binders: usize,
    ) -> (
        Vec<(Rc<Term>, kernel::ast::BinderInfo, FunctionKind)>,
        Rc<Term>,
    ) {
        let mut binders: Vec<(Rc<Term>, kernel::ast::BinderInfo, FunctionKind)> = Vec::new();
        let mut current = minor_ty.clone();
        while binders.len() < expected_binders {
            if let Term::Pi(arg_ty, body_ty, info, kind) = &*current {
                binders.push((arg_ty.clone(), *info, *kind));
                current = body_ty.clone();
            } else {
                break;
            }
        }
        (binders, current)
    }

    /// Count the number of Pi arguments in a type
    fn count_pi_args(&self, ty: &Rc<Term>) -> usize {
        match &**ty {
            Term::Pi(_, body, _, _) => 1 + self.count_pi_args(body),
            _ => 0,
        }
    }

    /// Find indices of recursive arguments (arguments whose type is the inductive type)
    fn find_recursive_args(&self, ty: &Rc<Term>, ind_name: &str) -> Vec<usize> {
        let mut result = Vec::new();
        let mut current = ty;
        let mut idx = 0;

        while let Term::Pi(arg_ty, body, _, _) = &**current {
            if self.type_refers_to_ind(arg_ty, ind_name) {
                result.push(idx);
            }
            current = body;
            idx += 1;
        }

        result
    }

    /// Check if a type refers to an inductive type
    fn type_refers_to_ind(&self, ty: &Rc<Term>, ind_name: &str) -> bool {
        match &**ty {
            Term::Ind(name, _) => name == ind_name,
            Term::App(f, _, _) => self.type_refers_to_ind(f, ind_name),
            _ => false,
        }
    }

    /// Extract argument types from a Pi type
    #[allow(dead_code)]
    fn extract_pi_arg_types(&self, ty: &Rc<Term>) -> Vec<Rc<Term>> {
        let mut result = Vec::new();
        let mut current = ty;

        while let Term::Pi(arg_ty, body, _, _) = &**current {
            result.push(arg_ty.clone());
            current = body;
        }

        result
    }

    /// Extract EXPLICIT argument types from a Pi type (skipping implicits)
    /// Also returns the count of implicit args that were skipped
    #[allow(dead_code)]
    fn extract_explicit_pi_arg_types(&self, ty: &Rc<Term>) -> (Vec<Rc<Term>>, usize) {
        let mut result = Vec::new();
        let mut current = ty;
        let mut implicit_count = 0;

        while let Term::Pi(arg_ty, body, info, _) = &**current {
            match info {
                kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit => {
                    implicit_count += 1;
                }
                kernel::ast::BinderInfo::Default => {
                    result.push(arg_ty.clone());
                }
            }
            current = body;
        }

        (result, implicit_count)
    }

    /// Count only explicit Pi arguments
    #[allow(dead_code)]
    fn count_explicit_pi_args(&self, ty: &Rc<Term>) -> usize {
        let mut count = 0;
        let mut current = ty;

        while let Term::Pi(_, body, info, _) = &**current {
            if *info == kernel::ast::BinderInfo::Default {
                count += 1;
            }
            current = body;
        }

        count
    }

    /// Attempt to unify two terms, with proper span tracking for error messages.
    /// If unification is stuck on metavariables, the constraint is postponed.
    fn unify_with_span(
        &mut self,
        t1: &Rc<Term>,
        t2: &Rc<Term>,
        span: Span,
    ) -> Result<(), ElabError> {
        match self.unify_core(t1, t2) {
            UnifyResult::Success => Ok(()),
            UnifyResult::Stuck(t1_stuck, t2_stuck) => {
                // Postpone the constraint with proper span
                self.constraints.push(Constraint::Unification {
                    t1: t1_stuck,
                    t2: t2_stuck,
                    span,
                    context: self.locals.clone(),
                });
                Ok(())
            }
            UnifyResult::Failed(t1_fail, t2_fail) => Err(ElabError::UnificationError(
                self.pretty_term(&t1_fail),
                self.pretty_term(&t2_fail),
            )),
        }
    }

    /// Legacy unify without span - uses a default span.
    /// Prefer `unify_with_span` when span is available.
    #[allow(dead_code)]
    fn unify(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> Result<(), ElabError> {
        // Use a sentinel span to indicate "no span available"
        let default_span = Span {
            start: 0,
            end: 0,
            line: 0,
            col: 0,
        };
        self.unify_with_span(t1, t2, default_span)
    }

    /// Core unification logic that returns a detailed result.
    /// - Success: terms are definitionally equal or unification succeeded
    /// - Stuck: unification blocked on unsolved metavariables
    /// - Failed: terms are definitively incompatible
    fn unify_core(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> UnifyResult {
        // First resolve metas, then check definitional equality
        let ctx_len = self.locals.len();
        let t1 = self.resolve_metas_in_ctx(t1, ctx_len);
        let t2 = self.resolve_metas_in_ctx(t2, ctx_len);

        // Align elided Ref labels with explicit ones before defeq
        self.align_ref_labels(&t1, &t2);
        let t1 = self.apply_label_subst(&t1);
        let t2 = self.apply_label_subst(&t2);

        // Check definitional equality on resolved terms
        match self.is_def_eq_in_ctx(&t1, &t2) {
            Ok(true) => return UnifyResult::Success,
            Ok(false) => {}
            Err(_) => return UnifyResult::Failed(t1.clone(), t2.clone()),
        }

        match (&*t1, &*t2) {
            // Same metavariable
            (Term::Meta(id1), Term::Meta(id2)) if id1 == id2 => UnifyResult::Success,

            // Metavariable on one side - try to solve it
            (Term::Meta(id), term) | (term, Term::Meta(id)) => {
                let meta_ctx_len = match self.meta_contexts.get(id) {
                    Some(ctx) => ctx.len(),
                    None => return UnifyResult::Failed(t1.clone(), t2.clone()),
                };
                match self.solve_meta(*id, Rc::new(term.clone()), ctx_len, meta_ctx_len) {
                    Ok(()) => UnifyResult::Success,
                    Err(_) => {
                        // Occurs check or scope error - this is stuck, not failed
                        // because we might solve other metas first
                        UnifyResult::Stuck(t1.clone(), t2.clone())
                    }
                }
            }

            // Structural cases - recurse
            (Term::App(f1, a1, l1), Term::App(f2, a2, l2)) => {
                if l1 != l2 {
                    return UnifyResult::Failed(t1.clone(), t2.clone());
                }
                match self.unify_core(f1, f2) {
                    UnifyResult::Success => self.unify_core(a1, a2),
                    UnifyResult::Stuck(_, _) => UnifyResult::Stuck(t1.clone(), t2.clone()),
                    UnifyResult::Failed(_, _) => UnifyResult::Failed(t1.clone(), t2.clone()),
                }
            }
            (Term::Pi(ty1, b1, _, k1), Term::Pi(ty2, b2, _, k2)) => {
                if k1 != k2 {
                    return UnifyResult::Failed(t1.clone(), t2.clone());
                }
                match self.unify_core(ty1, ty2) {
                    UnifyResult::Success => self.unify_core(b1, b2),
                    UnifyResult::Stuck(_, _) => UnifyResult::Stuck(t1.clone(), t2.clone()),
                    UnifyResult::Failed(_, _) => UnifyResult::Failed(t1.clone(), t2.clone()),
                }
            }
            (Term::Lam(ty1, b1, _, k1), Term::Lam(ty2, b2, _, k2)) => {
                if k1 != k2 {
                    return UnifyResult::Failed(t1.clone(), t2.clone());
                }
                match self.unify_core(ty1, ty2) {
                    UnifyResult::Success => self.unify_core(b1, b2),
                    UnifyResult::Stuck(_, _) => UnifyResult::Stuck(t1.clone(), t2.clone()),
                    UnifyResult::Failed(_, _) => UnifyResult::Failed(t1.clone(), t2.clone()),
                }
            }

            // Check if either side contains unsolved metas - if so, it's stuck
            _ => {
                if self.contains_any_meta(&t1) || self.contains_any_meta(&t2) {
                    UnifyResult::Stuck(t1.clone(), t2.clone())
                } else {
                    // No metas, types are just incompatible
                    UnifyResult::Failed(t1.clone(), t2.clone())
                }
            }
        }
    }

    /// Solve all postponed constraints using fixed-point iteration.
    /// Returns an error immediately if any constraint definitively fails.
    /// Returns an error at the end if constraints remain stuck (unsolvable).
    pub fn solve_constraints(&mut self) -> Result<(), ElabError> {
        let mut progress = true;
        while progress {
            progress = false;
            let mut remaining_constraints = Vec::new();
            let constraints = std::mem::take(&mut self.constraints);

            for constraint in constraints {
                match constraint {
                    Constraint::Unification {
                        t1,
                        t2,
                        span,
                        context,
                    } => {
                        let saved_locals = std::mem::replace(&mut self.locals, context.clone());
                        let unify_result = self.unify_core(&t1, &t2);
                        self.locals = saved_locals;

                        match unify_result {
                            UnifyResult::Success => {
                                // Constraint solved! We made progress.
                                progress = true;
                            }
                            UnifyResult::Stuck(t1_stuck, t2_stuck) => {
                                // Still stuck - keep it for another iteration
                                // Use the resolved terms for better error messages
                                remaining_constraints.push(Constraint::Unification {
                                    t1: t1_stuck,
                                    t2: t2_stuck,
                                    span,
                                    context,
                                });
                            }
                            UnifyResult::Failed(t1_fail, t2_fail) => {
                                // Definitively failed - report error immediately with span
                                return Err(ElabError::TypeMismatch {
                                    expected: self.pretty_term_in_context(&t1_fail, &context),
                                    got: self.pretty_term_in_context(&t2_fail, &context),
                                    span,
                                });
                            }
                        }
                    }
                }
            }
            self.constraints = remaining_constraints;
        }

        // If constraints remain, they are stuck (blocked on unsolved metas)
        if !self.constraints.is_empty() {
            let msg = self
                .constraints
                .iter()
                .map(|c| match c {
                    Constraint::Unification {
                        t1,
                        t2,
                        span,
                        context,
                    } => format!(
                        "Cannot unify {} with {} at line {}:{}",
                        self.pretty_term_in_context(t1, context),
                        self.pretty_term_in_context(t2, context),
                        span.line,
                        span.col
                    ),
                })
                .collect::<Vec<_>>()
                .join("; ");
            return Err(ElabError::UnsolvedConstraints(msg));
        }
        Ok(())
    }

    /// Attempt unification, postponing if stuck. Uses span for error reporting.
    #[allow(dead_code)]
    fn unify_postponed(&mut self, t1: Rc<Term>, t2: Rc<Term>, span: Span) -> Result<(), ElabError> {
        match self.unify_core(&t1, &t2) {
            UnifyResult::Success => Ok(()),
            UnifyResult::Stuck(t1_stuck, t2_stuck) => {
                // Postpone with proper span
                self.constraints.push(Constraint::Unification {
                    t1: t1_stuck,
                    t2: t2_stuck,
                    span,
                    context: self.locals.clone(),
                });
                Ok(())
            }
            UnifyResult::Failed(t1_fail, t2_fail) => Err(ElabError::UnificationError(
                self.pretty_term(&t1_fail),
                self.pretty_term(&t2_fail),
            )),
        }
    }

    fn solve_meta(
        &mut self,
        id: usize,
        term: Rc<Term>,
        current_ctx_len: usize,
        meta_ctx_len: usize,
    ) -> Result<(), ElabError> {
        if self.contains_meta(&term, id) {
            return Err(ElabError::OccursCheck(id, self.pretty_term(&term)));
        }
        let adapted = self.adapt_term_to_ctx(term.clone(), current_ctx_len, meta_ctx_len)?;
        self.meta_solutions.insert(id, adapted);
        Ok(())
    }

    fn adapt_term_to_ctx(
        &self,
        term: Rc<Term>,
        current_len: usize,
        target_len: usize,
    ) -> Result<Rc<Term>, ElabError> {
        if current_len == target_len {
            return Ok(term);
        }
        if current_len > target_len {
            let drop = current_len - target_len;
            self.prune_term(&term, drop, 0)
        } else {
            Ok(term.shift(0, target_len - current_len))
        }
    }

    fn prune_term(
        &self,
        term: &Rc<Term>,
        drop: usize,
        depth: usize,
    ) -> Result<Rc<Term>, ElabError> {
        match &**term {
            Term::Var(idx) => {
                if *idx < depth {
                    Ok(Rc::new(Term::Var(*idx)))
                } else if *idx < depth + drop {
                    Err(ElabError::SolutionContainsFreeVariables(
                        self.pretty_term(term),
                    ))
                } else {
                    Ok(Rc::new(Term::Var(idx - drop)))
                }
            }
            Term::Sort(l) => Ok(Rc::new(Term::Sort(l.clone()))),
            Term::Const(n, ls) => Ok(Rc::new(Term::Const(n.clone(), ls.clone()))),
            Term::App(f, a, label) => Ok(Rc::new(Term::App(
                self.prune_term(f, drop, depth)?,
                self.prune_term(a, drop, depth)?,
                label.clone(),
            ))),
            Term::Lam(ty, body, info, kind) => Ok(Rc::new(Term::Lam(
                self.prune_term(ty, drop, depth)?,
                self.prune_term(body, drop, depth + 1)?,
                *info,
                *kind,
            ))),
            Term::Pi(ty, body, info, kind) => Ok(Rc::new(Term::Pi(
                self.prune_term(ty, drop, depth)?,
                self.prune_term(body, drop, depth + 1)?,
                *info,
                *kind,
            ))),
            Term::LetE(ty, val, body) => Ok(Rc::new(Term::LetE(
                self.prune_term(ty, drop, depth)?,
                self.prune_term(val, drop, depth)?,
                self.prune_term(body, drop, depth + 1)?,
            ))),
            Term::Ind(n, ls) => Ok(Rc::new(Term::Ind(n.clone(), ls.clone()))),
            Term::Ctor(n, idx, ls) => Ok(Rc::new(Term::Ctor(n.clone(), *idx, ls.clone()))),
            Term::Rec(n, ls) => Ok(Rc::new(Term::Rec(n.clone(), ls.clone()))),
            Term::Fix(ty, body) => Ok(Rc::new(Term::Fix(
                self.prune_term(ty, drop, depth)?,
                self.prune_term(body, drop, depth + 1)?,
            ))),
            Term::Meta(id) => Ok(Rc::new(Term::Meta(*id))),
        }
    }

    fn contains_meta(&self, term: &Rc<Term>, meta_id: usize) -> bool {
        match &**term {
            Term::Meta(id) => *id == meta_id,
            Term::App(f, a, _) => self.contains_meta(f, meta_id) || self.contains_meta(a, meta_id),
            Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) | Term::Fix(ty, body) => {
                self.contains_meta(ty, meta_id) || self.contains_meta(body, meta_id)
            }
            Term::LetE(ty, val, body) => {
                self.contains_meta(ty, meta_id)
                    || self.contains_meta(val, meta_id)
                    || self.contains_meta(body, meta_id)
            }
            _ => false,
        }
    }

    fn contains_any_meta(&self, term: &Rc<Term>) -> bool {
        match &**term {
            Term::Meta(_) => true,
            Term::App(f, a, _) => self.contains_any_meta(f) || self.contains_any_meta(a),
            Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) | Term::Fix(ty, body) => {
                self.contains_any_meta(ty) || self.contains_any_meta(body)
            }
            Term::LetE(ty, val, body) => {
                self.contains_any_meta(ty)
                    || self.contains_any_meta(val)
                    || self.contains_any_meta(body)
            }
            _ => false,
        }
    }

    fn resolve_metas_in_ctx(&self, term: &Rc<Term>, ctx_len: usize) -> Rc<Term> {
        match &**term {
            Term::Meta(id) => {
                if let Some(solution) = self.meta_solutions.get(id) {
                    let meta_ctx_len = self.meta_contexts.get(id).map(|c| c.len()).unwrap_or(0);
                    self.adapt_term_to_ctx(solution.clone(), meta_ctx_len, ctx_len)
                        .unwrap_or_else(|_| term.clone())
                } else {
                    term.clone()
                }
            }
            _ => term.clone(),
        }
    }

    pub fn instantiate_metas(&mut self, term: &Rc<Term>) -> Rc<Term> {
        let zonked = self.zonk_with_ctx(term, self.locals.len());
        self.apply_label_subst(&zonked)
    }

    fn zonk_with_ctx(&mut self, term: &Rc<Term>, ctx_len: usize) -> Rc<Term> {
        match &**term {
            Term::Meta(id) => {
                if let Some(solution) = self.meta_solutions.get(id) {
                    let meta_ctx_len = self.meta_contexts.get(id).map(|c| c.len()).unwrap_or(0);
                    if let Ok(adapted) =
                        self.adapt_term_to_ctx(solution.clone(), meta_ctx_len, ctx_len)
                    {
                        let zonked = self.zonk_with_ctx(&adapted, ctx_len);
                        self.copy_metadata_if_any(term, &zonked);
                        return zonked;
                    }
                }
                term.clone()
            }
            Term::App(f, a, label) => {
                let new_term = Rc::new(Term::App(
                    self.zonk_with_ctx(f, ctx_len),
                    self.zonk_with_ctx(a, ctx_len),
                    label.clone(),
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Lam(ty, body, i, kind) => {
                let new_term = Rc::new(Term::Lam(
                    self.zonk_with_ctx(ty, ctx_len),
                    self.zonk_with_ctx(body, ctx_len + 1),
                    *i,
                    *kind,
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Pi(ty, body, i, kind) => {
                let new_term = Rc::new(Term::Pi(
                    self.zonk_with_ctx(ty, ctx_len),
                    self.zonk_with_ctx(body, ctx_len + 1),
                    *i,
                    *kind,
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::LetE(ty, val, body) => {
                let new_term = Rc::new(Term::LetE(
                    self.zonk_with_ctx(ty, ctx_len),
                    self.zonk_with_ctx(val, ctx_len),
                    self.zonk_with_ctx(body, ctx_len + 1),
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Ind(n, args) => {
                let new_term = Rc::new(Term::Ind(n.clone(), args.clone()));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Ctor(n, i, args) => {
                let new_term = Rc::new(Term::Ctor(n.clone(), *i, args.clone()));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Const(n, args) => {
                let new_term = Rc::new(Term::Const(n.clone(), args.clone()));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Fix(ty, body) => {
                let new_term = Rc::new(Term::Fix(
                    self.zonk_with_ctx(ty, ctx_len),
                    self.zonk_with_ctx(body, ctx_len + 1),
                ));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Sort(l) => {
                let new_term = Rc::new(Term::Sort(l.clone()));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Var(idx) => {
                let new_term = Rc::new(Term::Var(*idx));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
            Term::Rec(n, ls) => {
                let new_term = Rc::new(Term::Rec(n.clone(), ls.clone()));
                self.copy_metadata_if_any(term, &new_term);
                new_term
            }
        }
    }
}

struct CoreTermPrettyPrinter<'a> {
    env: &'a Env,
    context: Vec<String>,
    used_names: HashSet<String>,
}

impl<'a> CoreTermPrettyPrinter<'a> {
    fn new(env: &'a Env, locals: &[(String, Rc<Term>)]) -> Self {
        let mut context = Vec::with_capacity(locals.len());
        let mut used_names = HashSet::new();
        for (name, _) in locals {
            context.push(name.clone());
            used_names.insert(name.clone());
        }
        Self {
            env,
            context,
            used_names,
        }
    }

    fn pretty_term(&mut self, term: &Rc<Term>) -> String {
        match &**term {
            Term::Var(idx) => self.pretty_var(*idx),
            Term::Sort(level) => self.pretty_sort(level),
            Term::Const(name, levels) => self.pretty_name_with_levels(name, levels),
            Term::Ind(name, levels) => self.pretty_name_with_levels(name, levels),
            Term::Ctor(ind_name, idx, levels) => self.pretty_ctor(ind_name, *idx, levels),
            Term::Rec(ind_name, levels) => self.pretty_rec(ind_name, levels),
            Term::App(_, _, _) => self.pretty_app(term),
            Term::Lam(ty, body, info, kind) => {
                self.pretty_binder_term("lam", ty, body, *info, *kind)
            }
            Term::Pi(ty, body, info, kind) => self.pretty_binder_term("pi", ty, body, *info, *kind),
            Term::LetE(ty, val, body) => self.pretty_let(ty, val, body),
            Term::Fix(ty, body) => self.pretty_fix(ty, body),
            Term::Meta(id) => format!("?m{}", id),
        }
    }

    fn pretty_var(&self, idx: usize) -> String {
        if idx < self.context.len() {
            let name_idx = self.context.len() - 1 - idx;
            self.context[name_idx].clone()
        } else {
            format!("#{}", idx)
        }
    }

    fn pretty_sort(&self, level: &Level) -> String {
        match level {
            Level::Zero => "Prop".to_string(),
            Level::Succ(inner) => {
                let inner_str = self.level_to_string(inner);
                if inner_str == "0" {
                    "Type".to_string()
                } else if Self::level_needs_parens(inner) {
                    format!("Type ({})", inner_str)
                } else {
                    format!("Type {}", inner_str)
                }
            }
            _ => format!("Sort {}", self.level_to_string(level)),
        }
    }

    fn level_to_string(&self, level: &Level) -> String {
        if let Some(n) = Self::level_to_nat(level) {
            return n.to_string();
        }
        match level {
            Level::Zero => "0".to_string(),
            Level::Param(name) => name.clone(),
            Level::Succ(inner) => {
                let inner_str = self.level_to_string(inner);
                if Self::level_needs_parens(inner) {
                    format!("({})+1", inner_str)
                } else {
                    format!("{}+1", inner_str)
                }
            }
            Level::Max(a, b) => format!(
                "max({},{})",
                self.level_to_string(a),
                self.level_to_string(b)
            ),
            Level::IMax(a, b) => format!(
                "imax({},{})",
                self.level_to_string(a),
                self.level_to_string(b)
            ),
        }
    }

    fn level_to_nat(level: &Level) -> Option<u64> {
        match level {
            Level::Zero => Some(0),
            Level::Succ(inner) => Self::level_to_nat(inner).map(|n| n + 1),
            _ => None,
        }
    }

    fn level_needs_parens(level: &Level) -> bool {
        matches!(level, Level::Max(_, _) | Level::IMax(_, _))
    }

    fn pretty_name_with_levels(&self, name: &str, levels: &[Level]) -> String {
        let suffix = self.levels_suffix(levels);
        if suffix.is_empty() {
            name.to_string()
        } else {
            format!("{}{}", name, suffix)
        }
    }

    fn levels_suffix(&self, levels: &[Level]) -> String {
        if levels.is_empty() {
            return String::new();
        }
        let parts: Vec<String> = levels.iter().map(|lvl| self.level_to_string(lvl)).collect();
        format!(".{{{}}}", parts.join(","))
    }

    fn pretty_ctor(&self, ind_name: &str, idx: usize, levels: &[Level]) -> String {
        let suffix = self.levels_suffix(levels);
        if let Some(decl) = self.env.get_inductive(ind_name) {
            if let Some(ctor) = decl.ctors.get(idx) {
                return format!("{}.{}{}", ind_name, ctor.name, suffix);
            }
        }
        format!("{}.ctor{}{}", ind_name, idx, suffix)
    }

    fn pretty_rec(&self, ind_name: &str, levels: &[Level]) -> String {
        let suffix = self.levels_suffix(levels);
        if suffix.is_empty() {
            format!("rec.{}", ind_name)
        } else {
            format!("rec.{}{}", ind_name, suffix)
        }
    }

    fn pretty_app(&mut self, term: &Rc<Term>) -> String {
        let (head, args) = self.collect_app_spine(term);
        let head_str = self.pretty_term(&head);
        let mut pieces = Vec::with_capacity(1 + args.len() * 2);
        pieces.push(head_str);

        if self.is_ref_head(&head) && args.len() == 2 {
            if let Some(label) = args[1].label.as_ref() {
                pieces.push(format!("#[{}]", label));
                pieces.push(self.pretty_term(&args[0].term));
                pieces.push(self.pretty_term(&args[1].term));
                return format!("({})", pieces.join(" "));
            }
        }

        for arg in args {
            if let Some(label) = arg.label {
                pieces.push(format!("#[{}]", label));
            }
            pieces.push(self.pretty_term(&arg.term));
        }

        format!("({})", pieces.join(" "))
    }

    fn is_ref_head(&self, head: &Rc<Term>) -> bool {
        matches!(&**head, Term::Const(name, _) if name == "Ref")
    }

    fn collect_app_spine(&self, term: &Rc<Term>) -> (Rc<Term>, Vec<AppArg>) {
        let mut args = Vec::new();
        let mut head = term.clone();
        while let Term::App(f, a, label) = &*head {
            args.push(AppArg {
                term: a.clone(),
                label: label.clone(),
            });
            head = f.clone();
        }
        args.reverse();
        (head, args)
    }

    fn pretty_binder_term(
        &mut self,
        keyword: &str,
        ty: &Rc<Term>,
        body: &Rc<Term>,
        info: kernel::ast::BinderInfo,
        kind: FunctionKind,
    ) -> String {
        let name = self.fresh_name("x");
        let binder = self.format_binder(&name, info);
        let ty_str = self.pretty_term(ty);
        self.context.push(name);
        let body_str = self.pretty_term(body);
        self.context.pop();

        let mut pieces = Vec::new();
        pieces.push(keyword.to_string());
        if let Some(kind_token) = Self::kind_token(kind) {
            pieces.push(kind_token.to_string());
        }
        pieces.push(binder);
        pieces.push(ty_str);
        pieces.push(body_str);
        format!("({})", pieces.join(" "))
    }

    fn pretty_let(&mut self, ty: &Rc<Term>, val: &Rc<Term>, body: &Rc<Term>) -> String {
        let name = self.fresh_name("x");
        let ty_str = self.pretty_term(ty);
        let val_str = self.pretty_term(val);
        self.context.push(name.clone());
        let body_str = self.pretty_term(body);
        self.context.pop();
        format!("(let {} {} {} {})", name, ty_str, val_str, body_str)
    }

    fn pretty_fix(&mut self, ty: &Rc<Term>, body: &Rc<Term>) -> String {
        let name = self.fresh_name("f");
        let ty_str = self.pretty_term(ty);
        self.context.push(name.clone());
        let body_str = self.pretty_term(body);
        self.context.pop();
        format!("(fix {} {} {})", name, ty_str, body_str)
    }

    fn format_binder(&self, name: &str, info: kernel::ast::BinderInfo) -> String {
        match info {
            kernel::ast::BinderInfo::Default => name.to_string(),
            kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit => {
                format!("{{{}}}", name)
            }
        }
    }

    fn kind_token(kind: FunctionKind) -> Option<&'static str> {
        match kind {
            FunctionKind::Fn => None,
            FunctionKind::FnMut => Some("#[mut]"),
            FunctionKind::FnOnce => Some("#[once]"),
        }
    }

    fn fresh_name(&mut self, hint: &str) -> String {
        let base = if hint.is_empty() { "x" } else { hint };
        if !self.used_names.contains(base) {
            let name = base.to_string();
            self.used_names.insert(name.clone());
            return name;
        }
        let mut idx = 0;
        loop {
            let candidate = format!("{}{}", base, idx);
            if !self.used_names.contains(&candidate) {
                self.used_names.insert(candidate.clone());
                return candidate;
            }
            idx += 1;
        }
    }
}

struct AppArg {
    term: Rc<Term>,
    label: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::ast::BinderInfo;

    fn zero_span() -> Span {
        Span {
            start: 0,
            end: 0,
            line: 0,
            col: 0,
        }
    }

    #[test]
    fn meta_solution_prunes_extra_context() {
        let env = Env::new();
        let mut elab = Elaborator::new(&env);
        let ty = Rc::new(Term::Sort(Level::Zero));

        elab.locals.push(("a".to_string(), ty.clone()));
        let meta_id = elab.meta_counter;
        elab.meta_counter += 1;
        elab.meta_contexts.insert(
            meta_id,
            MetaContext {
                binders: elab.locals.clone(),
            },
        );

        elab.locals.push(("x".to_string(), ty.clone()));

        let meta_ctx_len = elab.meta_contexts.get(&meta_id).unwrap().len();
        let res = elab.solve_meta(
            meta_id,
            Rc::new(Term::Var(1)),
            elab.locals.len(),
            meta_ctx_len,
        );
        assert!(res.is_ok(), "Expected meta solving to succeed with pruning");

        let solved = elab
            .meta_solutions
            .get(&meta_id)
            .expect("Missing meta solution");
        assert!(matches!(&**solved, Term::Var(0)));
    }

    #[test]
    fn coerce_fn_to_fnonce_wraps_lambda() {
        let env = Env::new();
        let mut elab = Elaborator::new(&env);
        let arg_ty = Rc::new(Term::Sort(Level::Zero));
        let ret_ty = arg_ty.clone();

        let inferred_ty = Term::pi_with_kind(
            arg_ty.clone(),
            ret_ty.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        );
        let expected_ty = Term::pi_with_kind(
            arg_ty.clone(),
            ret_ty.clone(),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        );

        let term = Term::lam_with_kind(arg_ty, Term::var(0), BinderInfo::Default, FunctionKind::Fn);

        let res = elab
            .try_coerce_fn_to_kind(term, inferred_ty, expected_ty.clone(), zero_span())
            .expect("coercion should not error");
        let (coerced, coerced_ty) = res.expect("expected coercion to succeed");

        assert_eq!(coerced_ty, expected_ty);
        match &*coerced {
            Term::Lam(_, body, _, FunctionKind::FnOnce) => {
                assert!(
                    matches!(&**body, Term::Var(0) | Term::App(_, _, _)),
                    "coerced lambda should preserve the original callable body"
                );
            }
            other => panic!("expected FnOnce lambda, got {:?}", other),
        }
    }

    #[test]
    fn coerce_fn_to_fnmut_wraps_lambda() {
        let env = Env::new();
        let mut elab = Elaborator::new(&env);
        let arg_ty = Rc::new(Term::Sort(Level::Zero));
        let ret_ty = arg_ty.clone();

        let inferred_ty = Term::pi_with_kind(
            arg_ty.clone(),
            ret_ty.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        );
        let expected_ty = Term::pi_with_kind(
            arg_ty.clone(),
            ret_ty.clone(),
            BinderInfo::Default,
            FunctionKind::FnMut,
        );

        let term = Term::lam_with_kind(arg_ty, Term::var(0), BinderInfo::Default, FunctionKind::Fn);

        let res = elab
            .try_coerce_fn_to_kind(term, inferred_ty, expected_ty.clone(), zero_span())
            .expect("coercion should not error");
        let (coerced, coerced_ty) = res.expect("expected coercion to succeed");

        assert_eq!(coerced_ty, expected_ty);
        match &*coerced {
            Term::Lam(_, body, _, FunctionKind::FnMut) => {
                assert!(
                    matches!(&**body, Term::Var(0) | Term::App(_, _, _)),
                    "coerced lambda should preserve the original callable body"
                );
            }
            other => panic!("expected FnMut lambda, got {:?}", other),
        }
    }

    #[test]
    fn coerce_fnmut_to_fnonce_wraps_lambda() {
        let env = Env::new();
        let mut elab = Elaborator::new(&env);
        let arg_ty = Rc::new(Term::Sort(Level::Zero));
        let ret_ty = arg_ty.clone();

        let inferred_ty = Term::pi_with_kind(
            arg_ty.clone(),
            ret_ty.clone(),
            BinderInfo::Default,
            FunctionKind::FnMut,
        );
        let expected_ty = Term::pi_with_kind(
            arg_ty.clone(),
            ret_ty.clone(),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        );

        let term = Term::lam_with_kind(
            arg_ty,
            Term::var(0),
            BinderInfo::Default,
            FunctionKind::FnMut,
        );

        let res = elab
            .try_coerce_fn_to_kind(term, inferred_ty, expected_ty.clone(), zero_span())
            .expect("coercion should not error");
        let (coerced, coerced_ty) = res.expect("expected coercion to succeed");

        assert_eq!(coerced_ty, expected_ty);
        match &*coerced {
            Term::Lam(_, body, _, FunctionKind::FnOnce) => {
                assert!(
                    matches!(&**body, Term::Var(0) | Term::App(_, _, _)),
                    "coerced lambda should preserve the original callable body"
                );
            }
            other => panic!("expected FnOnce lambda, got {:?}", other),
        }
    }

    #[test]
    fn coerce_fn_to_fnonce_rejects_binder_info_mismatch() {
        let env = Env::new();
        let mut elab = Elaborator::new(&env);
        let arg_ty = Rc::new(Term::Sort(Level::Zero));
        let ret_ty = arg_ty.clone();

        let inferred_ty = Term::pi_with_kind(
            arg_ty.clone(),
            ret_ty.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        );
        let expected_ty = Term::pi_with_kind(
            arg_ty.clone(),
            ret_ty.clone(),
            BinderInfo::Implicit,
            FunctionKind::FnOnce,
        );

        let term = Term::lam_with_kind(arg_ty, Term::var(0), BinderInfo::Default, FunctionKind::Fn);

        let res = elab
            .try_coerce_fn_to_kind(term, inferred_ty, expected_ty, zero_span())
            .expect("coercion check should not error");
        assert!(
            res.is_none(),
            "expected binder info mismatch to skip coercion"
        );
    }

    #[test]
    fn split_minor_premise_respects_expected_binders() {
        let env = Env::new();
        let elab = Elaborator::new(&env);
        let arg_ty = Rc::new(Term::Sort(Level::Zero));
        let minor = Term::pi_with_kind(
            arg_ty.clone(),
            Term::pi_with_kind(
                arg_ty.clone(),
                arg_ty.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            ),
            BinderInfo::Implicit,
            FunctionKind::Fn,
        );

        let (binders, rest) = elab.split_minor_premise(&minor, 1);
        assert_eq!(binders.len(), 1);
        assert_eq!(binders[0].1, BinderInfo::Implicit);
        assert!(matches!(&*rest, Term::Pi(_, _, _, _)));

        let (binders_all, rest_all) = elab.split_minor_premise(&minor, 3);
        assert_eq!(binders_all.len(), 2);
        assert!(matches!(&*rest_all, Term::Sort(_)));
    }
}
