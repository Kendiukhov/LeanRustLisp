use crate::errors::{MirSpan, MirSpanMap, SourceSpan};
use crate::types::{AdtId, CtorId, DefId, IMKind, IdRegistry, MirType, Mutability, Region};
use crate::*;
use kernel::ast::{BorrowWrapperMarker, FunctionKind, Level, MarkerId, Term, TypeMarker};
use kernel::checker::{
    compute_recursor_type, infer, is_prop_like_with_transparency, whnf_in_ctx, Builtin, Context,
    Env, PropTransparencyContext, TypeError,
};
use kernel::ownership::{CaptureModes, ClosureId, DefCaptureModeMap, UsageMode};
use kernel::Transparency;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct LoweringError {
    message: String,
    span: Option<SourceSpan>,
}

impl LoweringError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: None,
        }
    }

    fn with_span(message: impl Into<String>, span: Option<SourceSpan>) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }

    pub fn span(&self) -> Option<SourceSpan> {
        self.span
    }
}

impl fmt::Display for LoweringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for LoweringError {}

type LoweringResult<T> = Result<T, LoweringError>;
type FunctionSignature = (FunctionKind, Vec<Region>, Vec<MirType>, Box<MirType>);

pub type StableTermId = u64;

/// Source spans of elaborated terms, keyed by term address (`Rc::as_ptr`).
///
/// An address identifies a term only while that term is alive: once it is freed, a term
/// allocated later (e.g. by MIR lowering) may get the same address and would inherit a stale
/// span. `pinned_terms` keeps the keyed terms alive for as long as the map exists.
#[derive(Debug, Clone, Default)]
pub struct TermSpanMap {
    spans_by_term_id: HashMap<StableTermId, SourceSpan>,
    term_ids_by_ptr: HashMap<usize, StableTermId>,
    pinned_terms: Vec<Rc<Term>>,
}

impl TermSpanMap {
    pub fn new(
        spans_by_term_id: HashMap<StableTermId, SourceSpan>,
        term_ids_by_ptr: HashMap<usize, StableTermId>,
    ) -> Self {
        Self {
            spans_by_term_id,
            term_ids_by_ptr,
            pinned_terms: Vec::new(),
        }
    }

    /// Keeps `terms` (the terms whose addresses are keys of this map) alive with the map.
    pub fn with_pinned_terms(mut self, terms: Vec<Rc<Term>>) -> Self {
        self.pinned_terms = terms;
        self
    }

    pub fn span_for_term(&self, term: &Rc<Term>) -> Option<SourceSpan> {
        let ptr = Rc::as_ptr(term) as usize;
        let term_id = self.term_ids_by_ptr.get(&ptr)?;
        self.spans_by_term_id.get(term_id).copied()
    }
}

pub struct LoweringContext<'a> {
    pub body: Body,
    pub current_block: BasicBlock,
    pub debruijn_map: Vec<Local>,
    borrowed_capture_locals: std::collections::HashSet<Local>,
    pub kernel_env: &'a Env,
    pub ids: &'a IdRegistry,
    pub checker_ctx: Context,                   // For type inference
    pub derived_bodies: Rc<RefCell<Vec<Body>>>, // Store lowered lambda bodies
    pub derived_span_tables: Rc<RefCell<Vec<MirSpanMap>>>,
    pub span_table: MirSpanMap,
    term_span_map: Option<Rc<TermSpanMap>>,
    capture_mode_map: Option<Rc<DefCaptureModeMap>>,
    closure_id_map: Option<Rc<HashMap<usize, ClosureId>>>,
    def_name: Option<String>,
    current_span: Option<SourceSpan>,
    next_region: usize,
    /// Set by `lower_rec` just before lowering the minor premise of a constructor with a
    /// recursive field; consumed by the next `Term::Lam` lowered. Such a minor is passed to
    /// every recursive call and then called, so it must be duplicable: function values it
    /// only calls (Fn, i.e. read) are captured by shared reference instead of being moved
    /// into its environment, which makes the closure `Copy` (Rust's rule: a closure is
    /// Copy when every capture is Copy or a shared reference). The minor never escapes the
    /// recursor application, so the borrow cannot dangle (NLL checks it like any loan).
    borrow_fn_captures_in_next_closure: bool,
    /// Locals of this body into which a closure with a non-Copy capture has been written.
    /// A local written by several closures (the arms of an inline `match`) is Copy only if
    /// every one of them is: one capture-free arm must not make the local holding another
    /// arm's consuming closure duplicable.
    non_copy_closure_locals: HashSet<Local>,
    /// Locals of this body made Copy because a closure with only Copy captures was written
    /// into them (see `non_copy_closure_locals`).
    copy_closure_locals: HashSet<Local>,
}

struct CapturePlan {
    outer_indices: Vec<usize>,
    operands: Vec<Operand>,
    term_types: Vec<Rc<Term>>,
    mir_types: Vec<MirType>,
    is_copy: Vec<bool>,
    borrowed: Vec<bool>,
}

#[derive(Clone, Copy)]
enum LifetimePosition {
    Arg,
    Return,
}

#[derive(Default)]
struct RegionParamAssigner {
    params: Vec<Region>,
    by_label: HashMap<String, Region>,
    arg_labels: HashSet<String>,
    anon_counter: usize,
}

impl RegionParamAssigner {
    fn fresh_label(&mut self) -> String {
        let label = format!("_r{}", self.anon_counter);
        self.anon_counter += 1;
        label
    }

    fn region_for_label(
        &mut self,
        label: String,
        position: LifetimePosition,
        fresh: impl FnOnce() -> Region,
    ) -> Region {
        if let Some(existing) = self.by_label.get(&label) {
            if matches!(position, LifetimePosition::Arg) {
                self.arg_labels.insert(label);
            }
            return *existing;
        }

        let region = fresh();
        self.by_label.insert(label.clone(), region);
        self.params.push(region);
        if matches!(position, LifetimePosition::Arg) {
            self.arg_labels.insert(label);
        }
        region
    }

    fn region_for_ref(
        &mut self,
        label: Option<&str>,
        position: LifetimePosition,
        fresh: impl FnOnce() -> Region,
    ) -> Region {
        if let Some(label) = label {
            return self.region_for_label(label.to_string(), position, fresh);
        }

        match position {
            LifetimePosition::Arg => {
                let label = self.fresh_label();
                self.region_for_label(label, position, fresh)
            }
            LifetimePosition::Return => {
                if self.arg_labels.len() == 1 {
                    let label = self
                        .arg_labels
                        .iter()
                        .next()
                        .cloned()
                        .unwrap_or_else(|| self.fresh_label());
                    self.region_for_label(label, position, fresh)
                } else {
                    let label = self.fresh_label();
                    self.region_for_label(label, position, fresh)
                }
            }
        }
    }

    fn params(&self) -> &[Region] {
        &self.params
    }
}

#[derive(Default, Clone)]
struct TypeParamScope {
    binders: Vec<Option<usize>>,
    next_param: usize,
}

impl TypeParamScope {
    fn push(&mut self, is_type_param: bool) {
        if is_type_param {
            let idx = self.next_param;
            self.next_param += 1;
            self.binders.push(Some(idx));
        } else {
            self.binders.push(None);
        }
    }

    fn pop(&mut self) {
        self.binders.pop();
    }

    fn param_for_var(&self, idx: usize) -> Option<usize> {
        let depth = self.binders.len();
        if idx >= depth {
            return None;
        }
        self.binders[depth - 1 - idx]
    }
}

fn collect_free_vars(term: &Rc<Term>, depth: usize, acc: &mut HashSet<usize>) {
    match &**term {
        Term::Var(idx) => {
            if *idx >= depth {
                acc.insert(*idx - depth);
            }
        }
        Term::App(f, a, _) => {
            collect_free_vars(f, depth, acc);
            collect_free_vars(a, depth, acc);
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            collect_free_vars(ty, depth, acc);
            collect_free_vars(body, depth + 1, acc);
        }
        Term::LetE(ty, val, body) => {
            collect_free_vars(ty, depth, acc);
            collect_free_vars(val, depth, acc);
            collect_free_vars(body, depth + 1, acc);
        }
        Term::Fix(ty, body) => {
            collect_free_vars(ty, depth, acc);
            collect_free_vars(body, depth + 1, acc);
        }
        Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => {}
    }
}

/// Whether `motive` is syntactically constant: a λ-chain over the `binders` indices and major
/// premise whose body mentions none of them (`(match e T ...)` elaborates to such a motive).
fn motive_is_constant(motive: &Rc<Term>, binders: usize) -> bool {
    let mut body = motive.clone();
    for _ in 0..binders {
        let inner = match &*body {
            Term::Lam(_, inner, _, _) => inner.clone(),
            _ => return false,
        };
        body = inner;
    }
    let mut free = HashSet::new();
    collect_free_vars(&body, 0, &mut free);
    !free.iter().any(|idx| *idx < binders)
}

/// Whether two MIR types are different known first-order types (`Unit`, `Bool`, `Nat` or
/// inductive types with different heads): a value of one can never be used at the other, so an
/// alternative of a large elimination whose type is one, lowered into a destination of the
/// other, is never taken (see `LoweringContext::lower_alternative_body`).
fn known_type_heads_differ(a: &MirType, b: &MirType) -> bool {
    let first_order = |ty: &MirType| {
        matches!(
            ty,
            MirType::Unit | MirType::Bool | MirType::Nat | MirType::Adt(..)
        )
    };
    match (a, b) {
        (MirType::Adt(x, _), MirType::Adt(y, _)) => x != y,
        _ => {
            first_order(a)
                && first_order(b)
                && std::mem::discriminant(a) != std::mem::discriminant(b)
        }
    }
}

fn usage_mode_for_kind(kind: FunctionKind) -> UsageMode {
    match kind {
        FunctionKind::Fn => UsageMode::Observational,
        FunctionKind::FnMut => UsageMode::MutBorrow,
        FunctionKind::FnOnce => UsageMode::Consuming,
    }
}

fn usage_mode_rank(mode: UsageMode) -> u8 {
    match mode {
        UsageMode::Observational => 0,
        UsageMode::MutBorrow => 1,
        UsageMode::Consuming => 2,
    }
}

struct SpanRestore<'a> {
    ctx: *mut LoweringContext<'a>,
    prev: Option<SourceSpan>,
}

impl<'a> Drop for SpanRestore<'a> {
    fn drop(&mut self) {
        // Safety: SpanRestore never outlives the LoweringContext that created it.
        unsafe {
            (*self.ctx).current_span = self.prev;
        }
    }
}

impl<'a> LoweringContext<'a> {
    pub fn new(
        args: Vec<(String, Rc<Term>)>,
        ret_ty: Rc<Term>,
        kernel_env: &'a kernel::checker::Env,
        ids: &'a IdRegistry,
    ) -> LoweringResult<Self> {
        Self::new_with_metadata(args, ret_ty, kernel_env, ids, None, None, None)
    }

    pub fn new_with_spans(
        args: Vec<(String, Rc<Term>)>,
        ret_ty: Rc<Term>,
        kernel_env: &'a kernel::checker::Env,
        ids: &'a IdRegistry,
        term_span_map: Option<Rc<TermSpanMap>>,
    ) -> LoweringResult<Self> {
        Self::new_with_metadata(args, ret_ty, kernel_env, ids, term_span_map, None, None)
    }

    pub fn new_with_metadata(
        args: Vec<(String, Rc<Term>)>,
        ret_ty: Rc<Term>,
        kernel_env: &'a kernel::checker::Env,
        ids: &'a IdRegistry,
        term_span_map: Option<Rc<TermSpanMap>>,
        def_name: Option<String>,
        capture_mode_map: Option<Rc<DefCaptureModeMap>>,
    ) -> LoweringResult<Self> {
        let mut body = Body::new(args.len());
        body.adt_layouts = ids.adt_layouts().clone();
        // Create entry block
        let entry_idx = body.basic_blocks.len();
        body.basic_blocks.push(BasicBlockData {
            statements: Vec::new(),
            terminator: None,
        });

        let mut ctx = LoweringContext {
            body,
            current_block: BasicBlock(entry_idx as u32),
            debruijn_map: Vec::new(),
            borrowed_capture_locals: std::collections::HashSet::new(),
            kernel_env,
            ids,
            checker_ctx: Context::new(), // Init empty
            derived_bodies: Rc::new(RefCell::new(Vec::new())),
            derived_span_tables: Rc::new(RefCell::new(Vec::new())),
            span_table: HashMap::new(),
            term_span_map,
            capture_mode_map,
            closure_id_map: None,
            def_name,
            current_span: None,
            next_region: 1,
            borrow_fn_captures_in_next_closure: false,
            non_copy_closure_locals: HashSet::new(),
            copy_closure_locals: HashSet::new(),
        };

        // Push Return Place _0 with correct type
        ctx.push_local(ret_ty, Some("_0".to_string()))?;

        for (name, ty) in args {
            let local = ctx.push_local(ty, Some(name))?;
            ctx.debruijn_map.push(local);
        }

        Ok(ctx)
    }

    pub fn lower_type(&mut self, term: &Rc<Term>) -> LoweringResult<MirType> {
        let mut scope = self.type_param_scope_from_ctx()?;
        self.lower_type_general_with_scope(term, &mut scope)
    }

    fn lower_type_general(&mut self, term: &Rc<Term>) -> LoweringResult<MirType> {
        let mut scope = self.type_param_scope_from_ctx()?;
        self.lower_type_general_with_scope(term, &mut scope)
    }

    fn lower_type_general_with_scope(
        &mut self,
        term: &Rc<Term>,
        scope: &mut TypeParamScope,
    ) -> LoweringResult<MirType> {
        let term_norm = whnf_in_ctx(
            self.kernel_env,
            &self.checker_ctx,
            term.clone(),
            Transparency::Reducible,
        )
        .map_err(|err| {
            self.lowering_error(format!(
                "Failed to normalize type during MIR lowering: {}",
                err
            ))
        })?;

        if let Some(mir_ty) = self.lower_borrow_shape_general(&term_norm, scope)? {
            return Ok(mir_ty);
        }

        match &*term_norm {
            Term::Sort(_) => Ok(MirType::Unit), // Types are erased
            Term::Var(idx) => Ok(scope
                .param_for_var(*idx)
                .map(MirType::Param)
                .unwrap_or(MirType::Unit)),
            Term::Ind(name, _) => self.lower_inductive_type_general(name, &[], scope),
            Term::App(_, _, _) => {
                let (head, args) = collect_app_spine(&term_norm);
                if let Term::Ind(name, _) = &*head {
                    self.lower_inductive_type_general(name, &args, scope)
                } else {
                    // Generic application or dependent type -> Opaque
                    Ok(MirType::Opaque {
                        reason: opaque_reason(&term_norm),
                    })
                }
            }
            Term::Pi(_, _, _, _) => self.lower_fn_type_with_scope(&term_norm, scope),
            _ => Ok(MirType::Opaque {
                reason: opaque_reason(&term_norm),
            }),
        }
    }

    fn lower_fn_type(&mut self, term: &Rc<Term>) -> LoweringResult<MirType> {
        let mut assigner = RegionParamAssigner::default();
        let mut scope = self.type_param_scope_from_ctx()?;
        self.lower_fn_type_with_interner_scoped(term, &mut assigner, &mut scope)
    }

    fn lower_fn_type_with_scope(
        &mut self,
        term: &Rc<Term>,
        scope: &mut TypeParamScope,
    ) -> LoweringResult<MirType> {
        let mut assigner = RegionParamAssigner::default();
        self.lower_fn_type_with_interner_scoped(term, &mut assigner, scope)
    }

    #[allow(dead_code)]
    fn lower_fn_type_with_interner(
        &mut self,
        term: &Rc<Term>,
        assigner: &mut RegionParamAssigner,
    ) -> LoweringResult<MirType> {
        let mut scope = self.type_param_scope_from_ctx()?;
        self.lower_fn_type_with_interner_scoped(term, assigner, &mut scope)
    }

    fn lower_fn_type_with_interner_scoped(
        &mut self,
        term: &Rc<Term>,
        assigner: &mut RegionParamAssigner,
        scope: &mut TypeParamScope,
    ) -> LoweringResult<MirType> {
        match &**term {
            Term::Pi(dom, cod, _, kind) => {
                let dom_is_type_param = self.is_type_param_binder(dom)?;
                let arg =
                    self.lower_type_in_fn_with_scope(dom, assigner, LifetimePosition::Arg, scope)?;
                scope.push(dom_is_type_param);
                let ret = match &**cod {
                    Term::Pi(_, _, _, _) => {
                        self.lower_fn_type_with_interner_scoped(cod, assigner, scope)?
                    }
                    _ => self.lower_type_in_fn_with_scope(
                        cod,
                        assigner,
                        LifetimePosition::Return,
                        scope,
                    )?,
                };
                scope.pop();
                let region_params = assigner.params().to_vec();
                Ok(MirType::Fn(*kind, region_params, vec![arg], Box::new(ret)))
            }
            _ => self.lower_type_in_fn_with_scope(term, assigner, LifetimePosition::Return, scope),
        }
    }

    #[allow(dead_code)]
    fn lower_type_in_fn(
        &mut self,
        term: &Rc<Term>,
        assigner: &mut RegionParamAssigner,
        position: LifetimePosition,
    ) -> LoweringResult<MirType> {
        let mut scope = self.type_param_scope_from_ctx()?;
        self.lower_type_in_fn_with_scope(term, assigner, position, &mut scope)
    }

    fn lower_type_in_fn_with_scope(
        &mut self,
        term: &Rc<Term>,
        assigner: &mut RegionParamAssigner,
        position: LifetimePosition,
        scope: &mut TypeParamScope,
    ) -> LoweringResult<MirType> {
        let term_norm = whnf_in_ctx(
            self.kernel_env,
            &self.checker_ctx,
            term.clone(),
            Transparency::Reducible,
        )
        .map_err(|err| {
            self.lowering_error(format!(
                "Failed to normalize function type during MIR lowering: {}",
                err
            ))
        })?;

        if let Some(mir_ty) =
            self.lower_borrow_shape_in_fn(&term_norm, assigner, position, scope)?
        {
            return Ok(mir_ty);
        }

        match &*term_norm {
            Term::Sort(_) => Ok(MirType::Unit), // Types are erased
            Term::Var(idx) => Ok(scope
                .param_for_var(*idx)
                .map(MirType::Param)
                .unwrap_or(MirType::Unit)),
            Term::Ind(name, _) => {
                self.lower_inductive_type_in_fn(name, &[], assigner, position, scope)
            }
            Term::App(_, _, _) => {
                let (head, args) = collect_app_spine(&term_norm);
                if let Term::Ind(name, _) = &*head {
                    self.lower_inductive_type_in_fn(name, &args, assigner, position, scope)
                } else {
                    // Generic application or dependent type -> Opaque
                    Ok(MirType::Opaque {
                        reason: opaque_reason(&term_norm),
                    })
                }
            }
            Term::Pi(_, _, _, _) => self.lower_fn_type_with_scope(&term_norm, scope),
            _ => Ok(MirType::Opaque {
                reason: opaque_reason(&term_norm),
            }),
        }
    }

    fn is_type_param_binder(&self, dom: &Rc<Term>) -> LoweringResult<bool> {
        let dom_norm = whnf_in_ctx(
            self.kernel_env,
            &self.checker_ctx,
            dom.clone(),
            Transparency::Reducible,
        )
        .map_err(|err| {
            self.lowering_error(format!(
                "Failed to normalize binder type during MIR lowering: {}",
                err
            ))
        })?;
        Ok(matches!(&*dom_norm, Term::Sort(_)))
    }

    fn type_param_scope_from_ctx(&self) -> LoweringResult<TypeParamScope> {
        let mut scope = TypeParamScope::default();
        let len = self.checker_ctx.len();
        for idx in (0..len).rev() {
            if let Some(ty) = self.checker_ctx.get(idx) {
                scope.push(self.is_type_param_binder(&ty)?);
            }
        }
        Ok(scope)
    }

    fn substitute_params_offset(ty: &MirType, offset: usize, params: &[MirType]) -> MirType {
        match ty {
            MirType::Param(idx) if *idx >= offset => {
                let rel = idx - offset;
                params.get(rel).cloned().unwrap_or(MirType::Param(*idx))
            }
            MirType::Adt(id, args) => MirType::Adt(
                id.clone(),
                args.iter()
                    .map(|arg| Self::substitute_params_offset(arg, offset, params))
                    .collect(),
            ),
            MirType::Ref(region, inner, mutability) => MirType::Ref(
                *region,
                Box::new(Self::substitute_params_offset(inner, offset, params)),
                *mutability,
            ),
            MirType::Fn(kind, region_params, args, ret) => MirType::Fn(
                *kind,
                region_params.clone(),
                args.iter()
                    .map(|arg| Self::substitute_params_offset(arg, offset, params))
                    .collect(),
                Box::new(Self::substitute_params_offset(ret, offset, params)),
            ),
            MirType::FnItem(def_id, kind, region_params, args, ret) => MirType::FnItem(
                *def_id,
                *kind,
                region_params.clone(),
                args.iter()
                    .map(|arg| Self::substitute_params_offset(arg, offset, params))
                    .collect(),
                Box::new(Self::substitute_params_offset(ret, offset, params)),
            ),
            MirType::Closure(kind, self_region, region_params, args, ret) => MirType::Closure(
                *kind,
                *self_region,
                region_params.clone(),
                args.iter()
                    .map(|arg| Self::substitute_params_offset(arg, offset, params))
                    .collect(),
                Box::new(Self::substitute_params_offset(ret, offset, params)),
            ),
            MirType::RawPtr(inner, mutability) => MirType::RawPtr(
                Box::new(Self::substitute_params_offset(inner, offset, params)),
                *mutability,
            ),
            MirType::InteriorMutable(inner, kind) => MirType::InteriorMutable(
                Box::new(Self::substitute_params_offset(inner, offset, params)),
                *kind,
            ),
            MirType::Opaque { reason } => MirType::Opaque {
                reason: reason.clone(),
            },
            other => other.clone(),
        }
    }

    fn specialize_pi_type_with_args_and_last(
        &mut self,
        ty: Rc<Term>,
        args: &[Rc<Term>],
    ) -> LoweringResult<Option<MirType>> {
        let mut current = ty;
        let mut assigner = RegionParamAssigner::default();
        let mut scope = self.type_param_scope_from_ctx()?;
        let outer_param_offset = scope.next_param;
        let mut arg_types = Vec::new();
        let mut arg_kinds = Vec::new();
        let mut param_subst = Vec::new();

        for arg in args {
            let term_norm = whnf_in_ctx(
                self.kernel_env,
                &self.checker_ctx,
                current.clone(),
                Transparency::Reducible,
            )
            .map_err(|err| {
                self.lowering_error(format!(
                    "Failed to normalize recursive application type during MIR lowering: {}",
                    err
                ))
            })?;
            let Term::Pi(dom, body, _info, kind) = &*term_norm else {
                return Ok(None);
            };

            if self.is_type_param_binder(dom)? {
                let mut arg_scope = self.type_param_scope_from_ctx()?;
                param_subst.push(self.lower_type_general_with_scope(arg, &mut arg_scope)?);
            }
            let dom_mir = self.lower_type_in_fn_with_scope(
                dom,
                &mut assigner,
                LifetimePosition::Arg,
                &mut scope,
            )?;
            arg_types.push(dom_mir);
            arg_kinds.push(*kind);
            current = body.subst(0, arg);
        }

        let term_norm = whnf_in_ctx(
            self.kernel_env,
            &self.checker_ctx,
            current.clone(),
            Transparency::Reducible,
        )
        .map_err(|err| {
            self.lowering_error(format!(
                "Failed to normalize recursive result type during MIR lowering: {}",
                err
            ))
        })?;
        let Term::Pi(dom, body, _info, kind) = &*term_norm else {
            return Ok(None);
        };

        let dom_mir = self.lower_type_in_fn_with_scope(
            dom,
            &mut assigner,
            LifetimePosition::Arg,
            &mut scope,
        )?;
        arg_types.push(dom_mir);
        arg_kinds.push(*kind);

        let dom_is_type_param = self.is_type_param_binder(dom)?;
        scope.push(dom_is_type_param);
        let ret_mir = self.lower_type_in_fn_with_scope(
            body,
            &mut assigner,
            LifetimePosition::Return,
            &mut scope,
        )?;
        scope.pop();

        let region_params = assigner.params().to_vec();
        let mut result = ret_mir;
        for (kind, arg_ty) in arg_kinds.into_iter().rev().zip(arg_types.into_iter().rev()) {
            result = MirType::Fn(kind, region_params.clone(), vec![arg_ty], Box::new(result));
        }
        if !param_subst.is_empty() {
            result = Self::substitute_params_offset(&result, outer_param_offset, &param_subst);
        }
        Ok(Some(result))
    }

    fn lower_borrow_shape_general(
        &mut self,
        term_norm: &Rc<Term>,
        scope: &mut TypeParamScope,
    ) -> LoweringResult<Option<MirType>> {
        if let Some((kind, inner, _label)) = self.parse_ref_type(term_norm) {
            let inner_ty = self.lower_type_general_with_scope(&inner, scope)?;
            let region = self.fresh_region();
            return Ok(Some(MirType::Ref(region, Box::new(inner_ty), kind.into())));
        }
        if let Some((kind, inner)) = self.parse_interior_mutability_type(term_norm)? {
            let inner_ty = self.lower_type_general_with_scope(&inner, scope)?;
            return Ok(Some(MirType::InteriorMutable(Box::new(inner_ty), kind)));
        }

        if let Some((name, marker, unfolded)) = self.unfold_marked_borrow_wrapper(term_norm)? {
            if let Some(expected) = ref_kind_for_borrow_wrapper(marker) {
                match self.parse_ref_type(&unfolded) {
                    Some((kind, inner, _label)) if kind == expected => {
                        let inner_ty = self.lower_type_general_with_scope(&inner, scope)?;
                        let region = self.fresh_region();
                        return Ok(Some(MirType::Ref(region, Box::new(inner_ty), kind.into())));
                    }
                    Some((kind, _, _)) => {
                        return Err(self.lowering_error(format!(
                            "Borrow-wrapper marker on '{}' expects {:?}, but unfolded to {:?}",
                            name, expected, kind
                        )));
                    }
                    None => {
                        return Err(self.lowering_error(format!(
                            "Borrow-wrapper marker on '{}' expects Ref shape, but unfolded term is not Ref",
                            name
                        )));
                    }
                }
            }
            if let Some(expected) = interior_mutability_for_borrow_wrapper(marker) {
                match self.parse_interior_mutability_type(&unfolded)? {
                    Some((kind, inner)) if kind == expected => {
                        let inner_ty = self.lower_type_general_with_scope(&inner, scope)?;
                        return Ok(Some(MirType::InteriorMutable(Box::new(inner_ty), kind)));
                    }
                    Some((kind, _)) => {
                        return Err(self.lowering_error(format!(
                            "Borrow-wrapper marker on '{}' expects {:?}, but unfolded to {:?}",
                            name, expected, kind
                        )));
                    }
                    None => {
                        return Err(self.lowering_error(format!(
                            "Borrow-wrapper marker on '{}' expects interior mutability shape, but unfolded term is not interior mutable",
                            name
                        )));
                    }
                }
            }
        }

        Ok(None)
    }

    fn lower_borrow_shape_in_fn(
        &mut self,
        term_norm: &Rc<Term>,
        assigner: &mut RegionParamAssigner,
        position: LifetimePosition,
        scope: &mut TypeParamScope,
    ) -> LoweringResult<Option<MirType>> {
        if let Some((kind, inner, label)) = self.parse_ref_type(term_norm) {
            let inner_ty = self.lower_type_in_fn_with_scope(&inner, assigner, position, scope)?;
            let region =
                assigner.region_for_ref(label.as_deref(), position, || self.fresh_region());
            return Ok(Some(MirType::Ref(region, Box::new(inner_ty), kind.into())));
        }
        if let Some((kind, inner)) = self.parse_interior_mutability_type(term_norm)? {
            let inner_ty = self.lower_type_in_fn_with_scope(&inner, assigner, position, scope)?;
            return Ok(Some(MirType::InteriorMutable(Box::new(inner_ty), kind)));
        }

        if let Some((name, marker, unfolded)) = self.unfold_marked_borrow_wrapper(term_norm)? {
            if let Some(expected) = ref_kind_for_borrow_wrapper(marker) {
                match self.parse_ref_type(&unfolded) {
                    Some((kind, inner, label)) if kind == expected => {
                        let inner_ty =
                            self.lower_type_in_fn_with_scope(&inner, assigner, position, scope)?;
                        let region = assigner
                            .region_for_ref(label.as_deref(), position, || self.fresh_region());
                        return Ok(Some(MirType::Ref(region, Box::new(inner_ty), kind.into())));
                    }
                    Some((kind, _, _)) => {
                        return Err(self.lowering_error(format!(
                            "Borrow-wrapper marker on '{}' expects {:?}, but unfolded to {:?}",
                            name, expected, kind
                        )));
                    }
                    None => {
                        return Err(self.lowering_error(format!(
                            "Borrow-wrapper marker on '{}' expects Ref shape, but unfolded term is not Ref",
                            name
                        )));
                    }
                }
            }
            if let Some(expected) = interior_mutability_for_borrow_wrapper(marker) {
                match self.parse_interior_mutability_type(&unfolded)? {
                    Some((kind, inner)) if kind == expected => {
                        let inner_ty =
                            self.lower_type_in_fn_with_scope(&inner, assigner, position, scope)?;
                        return Ok(Some(MirType::InteriorMutable(Box::new(inner_ty), kind)));
                    }
                    Some((kind, _)) => {
                        return Err(self.lowering_error(format!(
                            "Borrow-wrapper marker on '{}' expects {:?}, but unfolded to {:?}",
                            name, expected, kind
                        )));
                    }
                    None => {
                        return Err(self.lowering_error(format!(
                            "Borrow-wrapper marker on '{}' expects interior mutability shape, but unfolded term is not interior mutable",
                            name
                        )));
                    }
                }
            }
        }

        Ok(None)
    }

    fn unfold_marked_borrow_wrapper(
        &mut self,
        term_norm: &Rc<Term>,
    ) -> LoweringResult<Option<(String, BorrowWrapperMarker, Rc<Term>)>> {
        let (head, _) = collect_app_spine(term_norm);
        let Term::Const(name, _) = &*head else {
            return Ok(None);
        };
        let Some(def) = self.kernel_env.get_definition(name) else {
            return Ok(None);
        };
        let Some(marker) = def.borrow_wrapper_marker else {
            return Ok(None);
        };
        if def.transparency != Transparency::None {
            return Ok(None);
        }
        if def.value.is_none() {
            return Err(self.lowering_error(format!(
                "Borrow-wrapper marker on '{}' requires a definition body",
                name
            )));
        }

        let unfolded = whnf_in_ctx(
            self.kernel_env,
            &self.checker_ctx,
            term_norm.clone(),
            Transparency::All,
        )
        .map_err(|err| {
            self.lowering_error(format!(
                "Failed to unfold borrow-wrapper alias '{}': {}",
                name, err
            ))
        })?;
        Ok(Some((name.clone(), marker, unfolded)))
    }

    fn function_signature_from_type(
        &mut self,
        ty: &Rc<Term>,
    ) -> LoweringResult<Option<FunctionSignature>> {
        let ty_norm = whnf_in_ctx(
            self.kernel_env,
            &self.checker_ctx,
            ty.clone(),
            Transparency::Reducible,
        )
        .map_err(|err| {
            self.lowering_error(format!(
                "Failed to normalize function signature during MIR lowering: {}",
                err
            ))
        })?;
        if !matches!(&*ty_norm, Term::Pi(_, _, _, _)) {
            return Ok(None);
        }
        let mir_ty = self.lower_fn_type(&ty_norm)?;
        match mir_ty {
            MirType::Fn(kind, region_params, args, ret) => {
                Ok(Some((kind, region_params, args, ret)))
            }
            _ => Ok(None),
        }
    }

    fn function_value_mir_type(
        &mut self,
        term: &Rc<Term>,
        ty: &Rc<Term>,
    ) -> LoweringResult<Option<MirType>> {
        let Some((kind, region_params, args, ret)) = self.function_signature_from_type(ty)? else {
            return Ok(None);
        };
        match &**term {
            Term::Const(_, _) => Ok(self
                .def_id_for_const(term)
                .map(|def_id| MirType::FnItem(def_id, kind, region_params, args, ret))),
            Term::Lam(_, _, _, _) | Term::Fix(_, _) => {
                let self_region = self.fresh_region();
                Ok(Some(MirType::Closure(
                    kind,
                    self_region,
                    region_params,
                    args,
                    ret,
                )))
            }
            _ => Ok(None),
        }
    }

    fn lower_inductive_type_general(
        &mut self,
        name: &str,
        args: &[Rc<Term>],
        scope: &mut TypeParamScope,
    ) -> LoweringResult<MirType> {
        let adt_id = self.ids.adt_id(name).unwrap_or_else(|| AdtId::new(name));

        if adt_id.is_builtin(Builtin::Nat) {
            return Ok(MirType::Nat);
        }
        if adt_id.is_builtin(Builtin::Bool) {
            return Ok(MirType::Bool);
        }

        let param_count = self
            .ids
            .adt_num_params(&adt_id)
            .or_else(|| {
                self.kernel_env
                    .inductives
                    .get(name)
                    .map(|decl| decl.num_params)
            })
            .unwrap_or(args.len());

        // Representation types: indices are erased, value parameters become `Unit`
        // (docs/spec/mir/typing.md, "Indexed families").
        let mut kept_args = Vec::new();
        for (idx, arg) in args.iter().enumerate().take(param_count) {
            if self.ids.adt_param_is_type(&adt_id, idx) {
                kept_args.push(self.lower_type_general_with_scope(arg, scope)?);
            } else {
                kept_args.push(MirType::Unit);
            }
        }

        Ok(MirType::Adt(adt_id, kept_args))
    }

    fn lower_inductive_type_in_fn(
        &mut self,
        name: &str,
        args: &[Rc<Term>],
        assigner: &mut RegionParamAssigner,
        position: LifetimePosition,
        scope: &mut TypeParamScope,
    ) -> LoweringResult<MirType> {
        let adt_id = self.ids.adt_id(name).unwrap_or_else(|| AdtId::new(name));

        if adt_id.is_builtin(Builtin::Nat) {
            return Ok(MirType::Nat);
        }
        if adt_id.is_builtin(Builtin::Bool) {
            return Ok(MirType::Bool);
        }

        let param_count = self
            .ids
            .adt_num_params(&adt_id)
            .or_else(|| {
                self.kernel_env
                    .inductives
                    .get(name)
                    .map(|decl| decl.num_params)
            })
            .unwrap_or(args.len());

        // Representation types: indices are erased, value parameters become `Unit`
        // (docs/spec/mir/typing.md, "Indexed families").
        let mut kept_args = Vec::new();
        for (idx, arg) in args.iter().enumerate().take(param_count) {
            if self.ids.adt_param_is_type(&adt_id, idx) {
                kept_args.push(self.lower_type_in_fn_with_scope(arg, assigner, position, scope)?);
            } else {
                kept_args.push(MirType::Unit);
            }
        }

        Ok(MirType::Adt(adt_id, kept_args))
    }

    fn fresh_region(&mut self) -> Region {
        let region = Region(self.next_region);
        self.next_region += 1;
        region
    }

    fn parse_ref_type(&self, ty: &Rc<Term>) -> Option<(BorrowKind, Rc<Term>, Option<String>)> {
        // pattern: (App (App (Const Ref) (Const Mut/Shared)) T)
        let ref_def = self.ids.ref_def()?;
        let mut_def = self.ids.mut_def()?;
        let shared_def = self.ids.shared_def()?;

        if let Term::App(f1, inner_ty, label) = &**ty {
            if let Term::App(ref_const, kind_node, _) = &**f1 {
                let ref_id = self.def_id_for_const(ref_const)?;
                if ref_id != ref_def {
                    return None;
                }

                let kind_id = self.def_id_for_const(kind_node)?;
                if kind_id == mut_def {
                    return Some((BorrowKind::Mut, inner_ty.clone(), label.clone()));
                }
                if kind_id == shared_def {
                    return Some((BorrowKind::Shared, inner_ty.clone(), label.clone()));
                }
            }
        }
        None
    }

    fn def_id_for_const(&self, term: &Rc<Term>) -> Option<DefId> {
        if let Term::Const(name, _) = &**term {
            self.ids.def_id(name)
        } else {
            None
        }
    }

    fn place_from_term(&self, term: &Rc<Term>) -> LoweringResult<Place> {
        match &**term {
            Term::Var(idx) => {
                let env_idx = self
                    .debruijn_map
                    .len()
                    .checked_sub(1 + *idx)
                    .ok_or_else(|| {
                        self.lowering_error(format!(
                            "De Bruijn index out of bounds: {} (context size {})",
                            idx,
                            self.debruijn_map.len()
                        ))
                    })?;
                let local = self.debruijn_map[env_idx];
                if self.borrowed_capture_locals.contains(&local) {
                    Ok(Place {
                        local,
                        projection: vec![PlaceElem::Deref],
                    })
                } else {
                    Ok(Place::from(local))
                }
            }
            _ => Err(self.lowering_error("Borrow expects a variable place")),
        }
    }

    fn parse_interior_mutability_type(
        &mut self,
        ty: &Rc<Term>,
    ) -> LoweringResult<Option<(IMKind, Rc<Term>)>> {
        if let Term::App(f, inner_ty, _) = &**ty {
            if let Term::Ind(name, _) = &**f {
                if let Some(decl) = self.kernel_env.inductives.get(name) {
                    if let Some(kind) = self.interior_mutability_kind(name, &decl.markers)? {
                        return Ok(Some((kind, inner_ty.clone())));
                    }
                }
            }
        }
        Ok(None)
    }

    fn interior_mutability_kind(
        &self,
        type_name: &str,
        markers: &[MarkerId],
    ) -> LoweringResult<Option<IMKind>> {
        let has = |marker| {
            self.kernel_env.has_marker(markers, marker).map_err(|err| {
                self.lowering_error(format!(
                    "Marker registry error while lowering interior mutability type '{}': {}",
                    type_name, err
                ))
            })
        };

        if has(TypeMarker::MayPanicOnBorrowViolation)? {
            return Ok(Some(IMKind::RefCell));
        }
        if has(TypeMarker::AtomicPrimitive)? {
            return Ok(Some(IMKind::Atomic));
        }
        if has(TypeMarker::ConcurrencyPrimitive)? {
            return Ok(Some(IMKind::Mutex));
        }

        Ok(None)
    }

    fn collect_captures(
        &mut self,
        kind: FunctionKind,
        captured_indices: &HashSet<usize>,
        capture_modes: Option<&CaptureModes>,
        required_modes: Option<&CaptureModes>,
        borrow_fn_values: bool,
        erased_only: &HashSet<usize>,
    ) -> LoweringResult<CapturePlan> {
        let mut plan = CapturePlan {
            outer_indices: Vec::new(),
            operands: Vec::new(),
            term_types: Vec::new(),
            mir_types: Vec::new(),
            is_copy: Vec::new(),
            borrowed: Vec::new(),
        };

        let captured_locals: Vec<Local> = self.debruijn_map.clone();
        for (pos, local) in captured_locals.iter().enumerate() {
            let idx = captured_locals.len().saturating_sub(1 + pos);
            if !captured_indices.contains(&idx) {
                continue;
            }
            let Some(term_ty) = self.checker_ctx.get(idx) else {
                return Err(LoweringError::new("Capture type lookup failed".to_string()));
            };
            let decl = &self.body.local_decls[local.index()];
            let local_mir_ty = decl.ty.clone();
            let local_is_copy = decl.is_copy;

            let required_mode = required_modes.and_then(|modes| modes.get(&idx).copied());
            let annotated_mode = capture_modes.and_then(|modes| modes.get(&idx).copied());
            let mut capture_mode = match required_mode {
                Some(required) => {
                    if let Some(annotated) = annotated_mode {
                        if usage_mode_rank(annotated) < usage_mode_rank(required) {
                            return Err(LoweringError::new(format!(
                                "Capture mode annotation weaker than required for capture {}",
                                idx
                            )));
                        }
                        annotated
                    } else {
                        required
                    }
                }
                None => annotated_mode.unwrap_or_else(|| usage_mode_for_kind(kind)),
            };

            // A minor premise that must stay duplicable keeps its read-only captures as
            // shared borrows (see `borrow_fn_captures_in_next_closure`).
            let keep_shared_borrow =
                borrow_fn_values && matches!(capture_mode, UsageMode::Observational);
            if matches!(capture_mode, UsageMode::Observational)
                && matches!(kind, FunctionKind::FnOnce)
                && !local_is_copy
                && !keep_shared_borrow
            {
                capture_mode = UsageMode::Consuming;
            }
            if matches!(capture_mode, UsageMode::Observational)
                && erased_only.contains(&idx)
                && !local_is_copy
                && !keep_shared_borrow
            {
                // Only needed in erased positions: move it into the closure instead of
                // borrowing it (a borrow would tie the closure to this scope).
                capture_mode = UsageMode::Consuming;
            }
            if !local_is_copy
                && !keep_shared_borrow
                && matches!(
                    capture_mode,
                    UsageMode::Observational | UsageMode::MutBorrow
                )
                && matches!(
                    local_mir_ty,
                    MirType::Fn(_, _, _, _)
                        | MirType::FnItem(_, _, _, _, _)
                        | MirType::Closure(_, _, _, _, _)
                )
            {
                // Capturing function values by borrow causes dangling refs when closures escape.
                // Move them into the closure environment instead.
                capture_mode = UsageMode::Consuming;
            }

            if local_is_copy {
                plan.operands.push(Operand::Copy(Place::from(*local)));
                plan.mir_types.push(local_mir_ty);
                plan.is_copy.push(true);
                // Re-capturing a variable that this body itself holds by shared reference
                // copies the reference; the nested closure must dereference it as well.
                plan.borrowed
                    .push(self.borrowed_capture_locals.contains(local));
            } else {
                // A variable that this body itself holds through a borrowed capture (`local`
                // holds `&T` / `&mut T` to it) is re-borrowed THROUGH that reference
                // (`&*local` / `&mut *local`, a reference to `T`), not by borrowing `local`
                // (which would give `&&mut T`): the nested closure dereferences its capture
                // exactly once, like every borrowed capture.
                let held_by_reference = self.borrowed_capture_locals.contains(local);
                let (borrowed_place, borrowed_ty) = match (&local_mir_ty, held_by_reference) {
                    (MirType::Ref(_, inner, _), true) => (
                        Place {
                            local: *local,
                            projection: vec![PlaceElem::Deref],
                        },
                        (**inner).clone(),
                    ),
                    _ => (Place::from(*local), local_mir_ty.clone()),
                };
                match capture_mode {
                    UsageMode::Observational => {
                        let region = self.fresh_region();
                        let ref_ty = MirType::Ref(region, Box::new(borrowed_ty), Mutability::Not);
                        let ref_local = self.push_mir_local(ref_ty.clone(), None);
                        self.push_statement(Statement::StorageLive(ref_local));
                        self.push_statement(Statement::Assign(
                            Place::from(ref_local),
                            Rvalue::Ref(BorrowKind::Shared, borrowed_place),
                        ));
                        plan.operands.push(Operand::Copy(Place::from(ref_local)));
                        plan.mir_types.push(ref_ty);
                        plan.is_copy.push(true);
                        plan.borrowed.push(true);
                    }
                    UsageMode::MutBorrow => {
                        let region = self.fresh_region();
                        let ref_ty = MirType::Ref(region, Box::new(borrowed_ty), Mutability::Mut);
                        let ref_local = self.push_mir_local(ref_ty.clone(), None);
                        self.push_statement(Statement::StorageLive(ref_local));
                        self.push_statement(Statement::Assign(
                            Place::from(ref_local),
                            Rvalue::Ref(BorrowKind::Mut, borrowed_place),
                        ));
                        plan.operands.push(Operand::Move(Place::from(ref_local)));
                        plan.mir_types.push(ref_ty);
                        plan.is_copy.push(false);
                        plan.borrowed.push(true);
                    }
                    UsageMode::Consuming => {
                        plan.operands.push(Operand::Move(Place::from(*local)));
                        plan.mir_types.push(local_mir_ty);
                        plan.is_copy.push(false);
                        // Moving a reference this body holds to the variable: the nested
                        // closure reaches the variable through it, too.
                        plan.borrowed.push(held_by_reference);
                    }
                }
            }

            plan.outer_indices.push(idx);
            plan.term_types.push(term_ty);
        }

        Ok(plan)
    }

    fn merge_capture_modes(into: &mut CaptureModes, from: CaptureModes) {
        for (idx, mode) in from {
            into.entry(idx)
                .and_modify(|existing| {
                    if usage_mode_rank(mode) > usage_mode_rank(*existing) {
                        *existing = mode;
                    }
                })
                .or_insert(mode);
        }
    }

    fn is_copy_type_in_ctx(&self, ctx: &Context, ty: &Rc<Term>) -> LoweringResult<bool> {
        kernel::checker::is_copy_type_in_ctx(self.kernel_env, ctx, ty).map_err(|err| {
            self.lowering_error(format!(
                "Failed to determine capture Copy-ness during MIR lowering: {}",
                err
            ))
        })
    }

    fn is_mut_ref_type(&self, ctx: &Context, ty: &Rc<Term>) -> LoweringResult<bool> {
        let ty_whnf = whnf_in_ctx(self.kernel_env, ctx, ty.clone(), Transparency::Reducible)
            .map_err(|err| {
                self.lowering_error(format!(
                    "Failed to normalize capture type during MIR lowering: {}",
                    err
                ))
            })?;
        let (head, args) = collect_app_spine(&ty_whnf);
        let is_mut_ref = match (&*head, args.as_slice()) {
            (Term::Const(name, _), [kind, _]) if name == "Ref" => {
                matches!(&**kind, Term::Const(k, _) if k == "Mut")
            }
            _ => false,
        };
        Ok(is_mut_ref)
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
                .and_then(|ty| self.function_pi_info_from_term(&ty, ctx)),
            Term::Const(name, _) => self
                .kernel_env
                .get_definition(name)
                .and_then(|def| self.function_pi_info_from_term(&def.ty, ctx)),
            Term::Rec(ind, levels) => self
                .kernel_env
                .get_inductive(ind)
                .map(|decl| compute_recursor_type(decl, levels))
                .and_then(|ty| self.function_pi_info_from_term(&ty, ctx)),
            _ => None,
        }
    }

    fn count_pi_args(ty: &Rc<Term>) -> usize {
        match &**ty {
            Term::Pi(_, body, _, _) => 1 + Self::count_pi_args(body),
            _ => 0,
        }
    }

    fn collect_required_capture_modes_in_term(
        &self,
        term: &Rc<Term>,
        ctx: &Context,
        capture_depth: usize,
        mode: UsageMode,
    ) -> LoweringResult<Option<CaptureModes>> {
        match &**term {
            Term::Var(idx) => {
                let mut modes = HashMap::new();
                if *idx >= capture_depth {
                    let mut capture_mode = mode;
                    if capture_mode == UsageMode::Consuming {
                        if let Some(ty) = ctx.get(*idx) {
                            if self.is_mut_ref_type(ctx, &ty)? {
                                capture_mode = UsageMode::MutBorrow;
                            } else if self.is_copy_type_in_ctx(ctx, &ty)? {
                                capture_mode = UsageMode::Observational;
                            }
                        }
                    }
                    let capture_idx = idx - capture_depth;
                    modes.insert(capture_idx, capture_mode);
                }
                Ok(Some(modes))
            }
            Term::App(f, a, _) => {
                if mode != UsageMode::Observational {
                    let (head, args) = collect_app_spine(term);
                    if let Term::Rec(ind_name, _levels) = &*head {
                        if let Some(decl) = self.kernel_env.get_inductive(ind_name) {
                            let num_params = decl.num_params;
                            let num_indices =
                                Self::count_pi_args(&decl.ty).saturating_sub(num_params);
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
                                let Some(arg_modes) = self.collect_required_capture_modes_in_term(
                                    arg,
                                    ctx,
                                    capture_depth,
                                    arg_mode,
                                )?
                                else {
                                    return Ok(None);
                                };
                                Self::merge_capture_modes(&mut modes, arg_modes);
                            }
                            return Ok(Some(modes));
                        }
                    }
                }

                if mode == UsageMode::Observational {
                    let Some(mut modes) = self.collect_required_capture_modes_in_term(
                        f,
                        ctx,
                        capture_depth,
                        UsageMode::Observational,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(arg_modes) = self.collect_required_capture_modes_in_term(
                        a,
                        ctx,
                        capture_depth,
                        UsageMode::Observational,
                    )?
                    else {
                        return Ok(None);
                    };
                    Self::merge_capture_modes(&mut modes, arg_modes);
                    Ok(Some(modes))
                } else {
                    let (arg_mode, f_mode) = match self.function_pi_info_from_term(f, ctx) {
                        Some((arg_ty, info, kind)) => {
                            let arg_mode = match info {
                                kernel::ast::BinderInfo::Implicit
                                | kernel::ast::BinderInfo::StrictImplicit => {
                                    if self.is_copy_type_in_ctx(ctx, &arg_ty)? {
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
                        None => return Ok(None),
                    };
                    let f_eval_mode = match (&**f, f_mode) {
                        (Term::Var(_), UsageMode::Observational) => UsageMode::Observational,
                        (Term::Var(_), UsageMode::MutBorrow) => UsageMode::MutBorrow,
                        _ => UsageMode::Consuming,
                    };
                    let Some(mut modes) = self.collect_required_capture_modes_in_term(
                        f,
                        ctx,
                        capture_depth,
                        f_eval_mode,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(arg_modes) = self.collect_required_capture_modes_in_term(
                        a,
                        ctx,
                        capture_depth,
                        arg_mode,
                    )?
                    else {
                        return Ok(None);
                    };
                    Self::merge_capture_modes(&mut modes, arg_modes);
                    Ok(Some(modes))
                }
            }
            Term::Lam(ty, body, _, _) => {
                let Some(mut modes) = self.collect_required_capture_modes_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                )?
                else {
                    return Ok(None);
                };
                let new_ctx = ctx.push(ty.clone());
                let Some(body_modes) = self.collect_required_capture_modes_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                )?
                else {
                    return Ok(None);
                };
                Self::merge_capture_modes(&mut modes, body_modes);
                Ok(Some(modes))
            }
            Term::Pi(ty, body, _, _) => {
                let Some(mut modes) = self.collect_required_capture_modes_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                )?
                else {
                    return Ok(None);
                };
                let new_ctx = ctx.push(ty.clone());
                let Some(body_modes) = self.collect_required_capture_modes_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    UsageMode::Observational,
                )?
                else {
                    return Ok(None);
                };
                Self::merge_capture_modes(&mut modes, body_modes);
                Ok(Some(modes))
            }
            Term::LetE(ty, val, body) => {
                let Some(mut modes) = self.collect_required_capture_modes_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                )?
                else {
                    return Ok(None);
                };
                let Some(val_modes) =
                    self.collect_required_capture_modes_in_term(val, ctx, capture_depth, mode)?
                else {
                    return Ok(None);
                };
                Self::merge_capture_modes(&mut modes, val_modes);
                let new_ctx = ctx.push(ty.clone());
                let Some(body_modes) = self.collect_required_capture_modes_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                )?
                else {
                    return Ok(None);
                };
                Self::merge_capture_modes(&mut modes, body_modes);
                Ok(Some(modes))
            }
            Term::Fix(ty, body) => {
                let Some(mut modes) = self.collect_required_capture_modes_in_term(
                    ty,
                    ctx,
                    capture_depth,
                    UsageMode::Observational,
                )?
                else {
                    return Ok(None);
                };
                let new_ctx = ctx.push(ty.clone());
                let Some(body_modes) = self.collect_required_capture_modes_in_term(
                    body,
                    &new_ctx,
                    capture_depth + 1,
                    mode,
                )?
                else {
                    return Ok(None);
                };
                Self::merge_capture_modes(&mut modes, body_modes);
                Ok(Some(modes))
            }
            Term::Const(_, _)
            | Term::Sort(_)
            | Term::Ind(_, _)
            | Term::Ctor(_, _, _)
            | Term::Rec(_, _)
            | Term::Meta(_) => Ok(Some(HashMap::new())),
        }
    }

    /// Capture modes the closure `λx:arg_ty. body` requires. This is the kernel's analysis
    /// (`kernel::checker::term_variable_uses`), which the elaborator also uses to record capture
    /// modes; the local syntactic analysis is a fallback for terms the kernel cannot type here.
    fn required_capture_modes_for_closure(
        &self,
        arg_ty: &Rc<Term>,
        body: &Rc<Term>,
    ) -> LoweringResult<Option<CaptureModes>> {
        let ctx = self.checker_ctx.push(arg_ty.clone());
        if let Ok(uses) = kernel::checker::term_variable_uses(self.kernel_env, &ctx, body) {
            if let Ok(modes) =
                kernel::checker::capture_modes_from_uses(self.kernel_env, &ctx, &uses)
            {
                return Ok(Some(modes));
            }
        }
        self.collect_required_capture_modes_in_term(body, &ctx, 1, UsageMode::Consuming)
    }

    /// Captured variables (outer de Bruijn indices) of `λx:arg_ty. body` that occur in the body
    /// only in erased positions (types, proofs, motives, indices, parameters), per the kernel's
    /// analysis (`kernel::checker::term_runtime_variables`). Their values are not needed at run
    /// time; `collect_captures` moves rather than borrows them, so the closure does not hold a
    /// reference to a local it may outlive.
    fn erased_only_captures(
        &self,
        arg_ty: &Rc<Term>,
        body: &Rc<Term>,
        captured_indices: &HashSet<usize>,
    ) -> HashSet<usize> {
        let ctx = self.checker_ctx.push(arg_ty.clone());
        match kernel::checker::term_runtime_variables(self.kernel_env, &ctx, body) {
            Ok(runtime) => captured_indices
                .iter()
                .filter(|idx| !runtime.contains(&(**idx + 1)))
                .copied()
                .collect(),
            Err(_) => HashSet::new(),
        }
    }

    fn is_prop_type(&self, ty: &Rc<Term>) -> LoweringResult<bool> {
        match is_prop_like_with_transparency(
            self.kernel_env,
            &self.checker_ctx,
            ty,
            PropTransparencyContext::UnfoldOpaque,
        ) {
            Ok(is_prop) => Ok(is_prop),
            // Local declarations may carry open dependent types; treat unknown
            // de Bruijn variables conservatively as non-Prop instead of aborting.
            Err(TypeError::UnknownVariable(_)) => Ok(false),
            Err(err) => Err(self.lowering_error(format!(
                "Failed to determine Prop-like status during MIR lowering: {}",
                err
            ))),
        }
    }

    /// Whether `destination` is a whole local holding a proof that is erased at run time: a
    /// value of a proposition whose MIR type is not a function type (the same rule as
    /// `transform::erasure`, which later replaces such locals by `()`).
    fn is_erased_proof_destination(&self, destination: &Place) -> bool {
        if !destination.projection.is_empty() {
            return false;
        }
        let Some(decl) = self.body.local_decls.get(destination.local.index()) else {
            return false;
        };
        decl.is_prop
            && !matches!(
                decl.ty,
                MirType::Fn(_, _, _, _)
                    | MirType::FnItem(_, _, _, _, _)
                    | MirType::Closure(_, _, _, _, _)
            )
    }

    /// Whether `destination` is a whole local holding a proof of function type (a value whose
    /// type is a Pi ending in a proposition). Such values are erased proofs for the kernel; at
    /// run time they are represented by capture-free closures (see the `Term::Lam` case of
    /// `lower_term`) or function items, never by evaluating the term that produced them.
    fn is_erased_proof_function_destination(&self, destination: &Place) -> bool {
        if !destination.projection.is_empty() {
            return false;
        }
        let Some(decl) = self.body.local_decls.get(destination.local.index()) else {
            return false;
        };
        decl.is_prop
            && matches!(
                decl.ty,
                MirType::Fn(_, _, _, _)
                    | MirType::FnItem(_, _, _, _, _)
                    | MirType::Closure(_, _, _, _, _)
            )
    }

    /// Copy-ness of a local of kernel type `ty` (in the current checker context) and MIR type
    /// `mir_ty`. Proofs (`is_prop`) are erased at run time and Copy, as in the kernel; this is
    /// decided here with the local context, which the kernel's context-free `is_type_copy` lacks
    /// for open proof types. This includes proofs of function type: their run-time values are
    /// capture-free closures or function items (proof-typed closures are built without
    /// captures, and terms producing them are not evaluated), so duplicating them is safe.
    fn compute_is_copy_for_local(&self, ty: &Rc<Term>, mir_ty: &MirType, is_prop: bool) -> bool {
        if is_prop && !matches!(mir_ty, MirType::Opaque { .. }) {
            return true;
        }
        self.compute_is_copy_for_mir(ty, mir_ty)
    }

    fn compute_is_copy_for_mir(&self, ty: &Rc<Term>, mir_ty: &MirType) -> bool {
        let mut is_copy = self.is_type_copy(ty);
        if matches!(mir_ty, MirType::Opaque { .. }) {
            is_copy = false;
        }
        if matches!(mir_ty, MirType::Adt(_, _)) && mir_type_contains_opaque(mir_ty) {
            is_copy = false;
        }
        if matches!(
            mir_ty,
            MirType::Fn(_, _, _, _)
                | MirType::FnItem(_, _, _, _, _)
                | MirType::Closure(_, _, _, _, _)
        ) {
            is_copy = mir_ty.is_copy();
        }
        is_copy
    }

    pub fn push_local(&mut self, ty: Rc<Term>, name: Option<String>) -> LoweringResult<Local> {
        let idx = self.body.local_decls.len();

        // Determine if type is Prop (for Erasure)
        let is_prop = self.is_prop_type(&ty)?;

        // Lower to MIR Type
        let mir_ty = self.lower_type(&ty)?;

        // Determine if type has Copy semantics (opaque types are always non-Copy)
        let is_copy = self.compute_is_copy_for_local(&ty, &mir_ty, is_prop);

        // Update checker context
        self.checker_ctx = self.checker_ctx.push(ty.clone());

        self.body.local_decls.push(LocalDecl {
            ty: mir_ty,
            name,
            is_prop,
            is_copy,
            closure_captures: Vec::new(),
        });
        Ok(Local(idx as u32))
    }

    fn push_temp_local(&mut self, ty: Rc<Term>, name: Option<String>) -> LoweringResult<Local> {
        let idx = self.body.local_decls.len();

        // Determine if type is Prop (for Erasure)
        let is_prop = self.is_prop_type(&ty)?;

        let mir_ty = self.lower_type(&ty)?;
        let is_copy = self.compute_is_copy_for_local(&ty, &mir_ty, is_prop);

        self.body.local_decls.push(LocalDecl {
            ty: mir_ty,
            name,
            is_prop,
            is_copy,
            closure_captures: Vec::new(),
        });
        Ok(Local(idx as u32))
    }

    fn push_temp_local_with_mir(
        &mut self,
        ty: Rc<Term>,
        mir_ty: MirType,
        name: Option<String>,
    ) -> LoweringResult<Local> {
        let idx = self.body.local_decls.len();
        let is_prop = self.is_prop_type(&ty)?;
        let is_copy = self.compute_is_copy_for_local(&ty, &mir_ty, is_prop);
        self.body.local_decls.push(LocalDecl {
            ty: mir_ty,
            name,
            is_prop,
            is_copy,
            closure_captures: Vec::new(),
        });
        Ok(Local(idx as u32))
    }

    fn push_temp_local_for_value(
        &mut self,
        term: &Rc<Term>,
        ty: Rc<Term>,
        name: Option<String>,
    ) -> LoweringResult<Local> {
        if let Some(mir_ty) = self.function_value_mir_type(term, &ty)? {
            return self.push_temp_local_with_mir(ty, mir_ty, name);
        }
        self.push_temp_local(ty, name)
    }

    fn push_mir_local(&mut self, ty: MirType, name: Option<String>) -> Local {
        let idx = self.body.local_decls.len();
        let is_copy = ty.is_copy();
        self.body.local_decls.push(LocalDecl {
            ty,
            name,
            is_prop: false,
            is_copy,
            closure_captures: Vec::new(),
        });
        Local(idx as u32)
    }

    fn term_key(term: &Rc<Term>) -> usize {
        Rc::as_ptr(term) as usize
    }

    fn term_span_for(&self, term: &Rc<Term>) -> Option<SourceSpan> {
        self.term_span_map
            .as_ref()
            .and_then(|map| map.span_for_term(term))
    }

    fn capture_modes_for(&self, term: &Rc<Term>) -> Option<CaptureModes> {
        let closure_id = self
            .closure_id_map
            .as_ref()
            .and_then(|map| map.get(&Self::term_key(term)))?;
        self.capture_mode_map
            .as_ref()
            .and_then(|map| map.get(closure_id))
            .cloned()
    }

    fn closure_metadata_label(&self, term: &Rc<Term>) -> String {
        if let Some(closure_id) = self
            .closure_id_map
            .as_ref()
            .and_then(|map| map.get(&Self::term_key(term)))
        {
            return format!("DefId({})", closure_id.0);
        }
        format!("ptr@0x{:x}", Self::term_key(term))
    }

    fn capture_modes_for_required_closure(
        &self,
        term: &Rc<Term>,
        captured_indices: &HashSet<usize>,
    ) -> LoweringResult<Option<CaptureModes>> {
        if captured_indices.is_empty() {
            return Ok(self.capture_modes_for(term));
        }

        // Fail closed: capturing closures require source spans for actionable diagnostics.
        if self.term_span_map.is_some() && self.term_span_for(term).is_none() {
            return Err(self.lowering_error(format!(
                "Missing closure span metadata for {} while lowering capturing closure",
                self.closure_metadata_label(term)
            )));
        }

        let capture_modes = self.capture_modes_for(term);
        // Fail closed: silently dropping capture metadata can change capture lowering semantics.
        if self.capture_mode_map.is_some() && capture_modes.is_none() {
            return Err(self.lowering_error(format!(
                "Missing closure capture metadata for {} while lowering capturing closure",
                self.closure_metadata_label(term)
            )));
        }

        Ok(capture_modes)
    }

    fn ensure_capture_modes_complete(
        &self,
        term: &Rc<Term>,
        captured_indices: &HashSet<usize>,
        capture_modes: Option<&CaptureModes>,
    ) -> LoweringResult<()> {
        let Some(capture_modes) = capture_modes else {
            return Ok(());
        };
        // Sparse annotations are accepted: missing entries fall back to required modes
        // computed from the lowered closure body.
        let mut unexpected: Vec<usize> = capture_modes
            .keys()
            .copied()
            .filter(|idx| !captured_indices.contains(idx))
            .collect();
        unexpected.sort_unstable();
        if let Some(idx) = unexpected.first() {
            return Err(self.lowering_error(format!(
                "Invalid closure capture metadata for {}: unknown capture index {}",
                self.closure_metadata_label(term),
                idx
            )));
        }
        Ok(())
    }

    fn ensure_closure_id_map(&mut self, term: &Rc<Term>) {
        if self.closure_id_map.is_some() {
            return;
        }
        let Some(def_name) = self.def_name.as_ref() else {
            return;
        };
        let ids = kernel::ownership::collect_closure_ids(term, def_name);
        self.closure_id_map = Some(Rc::new(ids));
    }

    fn enter_term_span(&mut self, term: &Rc<Term>) -> SpanRestore<'a> {
        let prev = self.current_span;
        if let Some(span) = self.term_span_for(term) {
            self.current_span = Some(span);
        }
        SpanRestore { ctx: self, prev }
    }

    fn lowering_error(&self, message: impl Into<String>) -> LoweringError {
        LoweringError::with_span(message, self.current_span)
    }

    pub fn push_statement(&mut self, stmt: Statement) {
        let block = self.current_block;
        let stmt_idx = self.body.basic_blocks[block.index()].statements.len();
        self.body.basic_blocks[block.index()].statements.push(stmt);
        if let Some(span) = self.current_span {
            self.span_table.insert(
                MirSpan {
                    block,
                    statement_index: stmt_idx,
                },
                span,
            );
        }
    }

    pub fn terminate(&mut self, terminator: Terminator) {
        let block = self.current_block;
        let stmt_idx = self.body.basic_blocks[block.index()].statements.len();
        self.body.basic_blocks[block.index()].terminator = Some(terminator);
        if let Some(span) = self.current_span {
            self.span_table.insert(
                MirSpan {
                    block,
                    statement_index: stmt_idx,
                },
                span,
            );
        }
    }

    pub fn terminate_with_term_span(&mut self, term: &Rc<Term>, terminator: Terminator) {
        let prev = self.current_span;
        if let Some(span) = self.term_span_for(term) {
            self.current_span = Some(span);
        }
        self.terminate(terminator);
        self.current_span = prev;
    }

    /// Whether `term` is a type (its type is a sort). Types are erased at run time. The head of
    /// an application decides cheaply in the common cases (an inductive type, a sort or a Pi is a
    /// type; a constructor application is a value); otherwise the term's type is inferred and
    /// reduced to weak head normal form.
    fn term_is_type(&self, term: &Rc<Term>) -> bool {
        let (head, args) = collect_app_spine(term);
        match &*head {
            Term::Ind(_, _) | Term::Sort(_) | Term::Pi(_, _, _, _) => return true,
            Term::Ctor(_, _, _) => return false,
            _ => {}
        }
        // The type of the head, instantiated with the arguments (the arguments are not
        // re-checked: the term is well typed).
        let whnf = |ty: Rc<Term>| {
            whnf_in_ctx(
                self.kernel_env,
                &self.checker_ctx,
                ty,
                Transparency::Reducible,
            )
            .ok()
        };
        let Ok(mut ty) = self.infer_term_type(&head) else {
            return false;
        };
        for arg in &args {
            let Some(ty_norm) = whnf(ty) else {
                return false;
            };
            let Term::Pi(_, body, _, _) = &*ty_norm else {
                return false;
            };
            ty = body.subst(0, arg);
        }
        whnf(ty).is_some_and(|ty| matches!(&*ty, Term::Sort(_)))
    }

    /// Lowers `term`, a proof, into `destination` without evaluating it and without reading any
    /// variable (the body of a proof-typed closure, which has no captures): a proof of function
    /// type becomes a capture-free closure (a λ is lowered as such, any other term through its
    /// eta-expansion), any other proof the unit value it is erased to.
    fn lower_erased_proof_value(
        &mut self,
        term: &Rc<Term>,
        destination: Place,
        target: BasicBlock,
    ) -> LoweringResult<()> {
        if self.is_erased_proof_function_destination(&destination) {
            let lam = if matches!(&**term, Term::Lam(..)) {
                Some(term.clone())
            } else {
                self.eta_expand_proof_function(term)?
            };
            if let Some(lam) = lam {
                return self.lower_term(&lam, destination, target);
            }
        }
        let ty = self.body.local_decls[destination.local.index()].ty.clone();
        let constant = Constant {
            literal: Literal::Unit,
            ty,
        };
        self.push_statement(Statement::Assign(
            destination,
            Rvalue::Use(Operand::Constant(Box::new(constant))),
        ));
        self.terminate(Terminator::Goto { target });
        Ok(())
    }

    /// The eta-expansion `λx:A. t x` of a term `t` whose type reduces to `Π x:A. B` (the binder
    /// info and function kind are kept); `None` if the type is not a Pi.
    fn eta_expand_proof_function(&self, term: &Rc<Term>) -> LoweringResult<Option<Rc<Term>>> {
        let ty = self.infer_term_type(term)?;
        let ty_whnf = whnf_in_ctx(
            self.kernel_env,
            &self.checker_ctx,
            ty,
            Transparency::Reducible,
        )
        .map_err(|e| self.lowering_error(format!("Failed to reduce a proof type: {}", e)))?;
        let Term::Pi(dom, _, info, kind) = &*ty_whnf else {
            return Ok(None);
        };
        let body = Term::app(term.shift(0, 1), Rc::new(Term::Var(0)));
        Ok(Some(Rc::new(Term::Lam(dom.clone(), body, *info, *kind))))
    }

    fn infer_term_type(&self, term: &Rc<Term>) -> LoweringResult<Rc<Term>> {
        infer(self.kernel_env, &self.checker_ctx, term.clone())
            .map_err(|e| LoweringError::new(format!("Type inference failed for {:?}: {}", term, e)))
    }

    fn lower_term_to_local(&mut self, term: &Rc<Term>) -> LoweringResult<Local> {
        let ty = self.infer_term_type(term)?;
        let temp = self.push_temp_local_for_value(term, ty, None)?;
        self.push_statement(Statement::StorageLive(temp));
        let next_block = self.new_block();
        self.lower_term(term, Place::from(temp), next_block)?;
        self.set_block(next_block);
        Ok(temp)
    }

    fn eval_term_with_locals(
        &mut self,
        term: &Rc<Term>,
        locals: &[Local],
        local_types: &[Rc<Term>],
    ) -> LoweringResult<Local> {
        let saved_len = self.debruijn_map.len();
        let saved_ctx = self.checker_ctx.clone();
        self.debruijn_map.extend_from_slice(locals);
        for ty in local_types {
            self.checker_ctx = self.checker_ctx.push(ty.clone());
        }
        let temp = self.lower_term_to_local(term)?;
        self.debruijn_map.truncate(saved_len);
        self.checker_ctx = saved_ctx;
        Ok(temp)
    }

    fn local_is_copy(&self, local: Local) -> bool {
        self.body.local_decls[local.index()].is_copy
    }

    fn local_operand(&self, local: Local) -> Operand {
        if self.local_is_copy(local) {
            Operand::Copy(Place::from(local))
        } else {
            Operand::Move(Place::from(local))
        }
    }

    fn function_kind_for_ty(&self, func_ty: &MirType) -> Option<FunctionKind> {
        match func_ty {
            MirType::Fn(kind, _, _, _) => Some(*kind),
            MirType::FnItem(_, kind, _, _, _) => Some(*kind),
            MirType::Closure(kind, _, _, _, _) => Some(*kind),
            _ => None,
        }
    }

    fn call_operand_for_func(&self, local: Local, func_ty: &MirType) -> CallOperand {
        let Some(kind) = self.function_kind_for_ty(func_ty) else {
            return CallOperand::from(self.local_operand(local));
        };
        match kind {
            FunctionKind::Fn => CallOperand::Borrow(BorrowKind::Shared, Place::from(local)),
            FunctionKind::FnMut => CallOperand::Borrow(BorrowKind::Mut, Place::from(local)),
            FunctionKind::FnOnce => CallOperand::from(Operand::Move(Place::from(local))),
        }
    }

    fn call_operand_for_place(&self, place: &Place, func_ty: &MirType) -> CallOperand {
        let Some(kind) = self.function_kind_for_ty(func_ty) else {
            if place.projection.is_empty() {
                return CallOperand::from(self.local_operand(place.local));
            }
            return CallOperand::from(Operand::Move(place.clone()));
        };
        match kind {
            FunctionKind::Fn => CallOperand::Borrow(BorrowKind::Shared, place.clone()),
            FunctionKind::FnMut => CallOperand::Borrow(BorrowKind::Mut, place.clone()),
            FunctionKind::FnOnce => CallOperand::from(Operand::Move(place.clone())),
        }
    }

    fn apply_function_type(&self, func_ty: &MirType) -> LoweringResult<MirType> {
        let apply = |kind: FunctionKind,
                     region_params: &[Region],
                     args: &[MirType],
                     ret: &MirType|
         -> LoweringResult<MirType> {
            if args.is_empty() {
                Err(LoweringError::new(
                    "Function type has no arguments".to_string(),
                ))
            } else if args.len() == 1 {
                Ok(ret.clone())
            } else {
                Ok(MirType::Fn(
                    kind,
                    region_params.to_vec(),
                    args[1..].to_vec(),
                    Box::new(ret.clone()),
                ))
            }
        };

        match func_ty {
            MirType::Fn(kind, region_params, args, ret) => {
                apply(*kind, region_params, args, ret.as_ref())
            }
            MirType::FnItem(_, kind, region_params, args, ret) => {
                apply(*kind, region_params, args, ret.as_ref())
            }
            MirType::Closure(kind, _self_region, region_params, args, ret) => {
                apply(*kind, region_params, args, ret.as_ref())
            }
            _ => Err(LoweringError::new(format!(
                "Expected function type in MIR, got {:?}",
                func_ty
            ))),
        }
    }

    fn call_with_args(
        &mut self,
        func_local: Local,
        args: &[Operand],
        final_place: Option<Place>,
    ) -> LoweringResult<Local> {
        if args.is_empty() {
            return Ok(func_local);
        }

        let mut current_func = func_local;
        let mut current_func_ty = self.body.local_decls[current_func.index()].ty.clone();
        let mut last_local = func_local;

        for (i, arg_op) in args.iter().enumerate() {
            let is_last = i == args.len() - 1;
            let result_ty = self.apply_function_type(&current_func_ty)?;
            let dest_place = if is_last {
                if let Some(place) = final_place.clone() {
                    place
                } else {
                    let t = self.push_mir_local(result_ty.clone(), None);
                    self.push_statement(Statement::StorageLive(t));
                    Place::from(t)
                }
            } else {
                let t = self.push_mir_local(result_ty.clone(), None);
                self.push_statement(Statement::StorageLive(t));
                Place::from(t)
            };

            last_local = dest_place.local;
            let next_block = self.new_block();

            let func_operand = self.call_operand_for_func(current_func, &current_func_ty);
            self.terminate(Terminator::Call {
                func: func_operand,
                args: vec![arg_op.clone()],
                destination: dest_place.clone(),
                target: Some(next_block),
            });
            self.set_block(next_block);

            if i > 0 {
                self.push_statement(Statement::StorageDead(current_func));
            }

            if !is_last {
                current_func = dest_place.local;
                current_func_ty = result_ty;
            }
        }

        Ok(last_local)
    }

    pub fn new_block(&mut self) -> BasicBlock {
        let idx = self.body.basic_blocks.len();
        self.body.basic_blocks.push(BasicBlockData {
            statements: Vec::new(),
            terminator: None,
        });
        BasicBlock(idx as u32)
    }

    pub fn set_block(&mut self, block: BasicBlock) {
        self.current_block = block;
    }

    pub fn finish(self) -> Body {
        self.body
    }

    // Core lowering logic
    pub fn lower_term(
        &mut self,
        term: &Rc<Term>,
        destination: Place,
        target: BasicBlock,
    ) -> LoweringResult<()> {
        self.ensure_closure_id_map(term);
        let _span_guard = self.enter_term_span(term);
        if self.is_erased_proof_destination(&destination) && !matches!(&**term, Term::Var(_)) {
            // A proof is erased at run time, so it is not evaluated: the kernel's ownership
            // walk never visits proof terms (docs/spec/ownership_model.md, erased positions), and
            // evaluating them here would move values the kernel considers unused, or run
            // eliminations of erased proofs (projections out of a `()` at run time).
            let ty = self.body.local_decls[destination.local.index()].ty.clone();
            let constant = Constant {
                literal: Literal::Unit,
                ty,
            };
            self.push_statement(Statement::Assign(
                destination,
                Rvalue::Use(Operand::Constant(Box::new(constant))),
            ));
            self.terminate(Terminator::Goto { target });
            return Ok(());
        }
        if self.is_erased_proof_function_destination(&destination)
            && !matches!(
                &**term,
                Term::Var(_) | Term::Lam(..) | Term::Const(..) | Term::Ctor(..)
            )
        {
            // A proof of function type produced by a computation (an application, a `let`, an
            // elimination, ...) is not evaluated either: it is replaced by its eta-expansion
            // `λx. t x`, which the `Term::Lam` case builds as a capture-free closure whose body
            // (a proof) is erased.
            if let Some(eta) = self.eta_expand_proof_function(term)? {
                return self.lower_term(&eta, destination, target);
            }
        }
        if !matches!(&**term, Term::Var(_)) && self.local_has_stuck_type(&destination) {
            if let Some(temp) = self.push_temp_for_known_value_into_stuck(term)? {
                // A value of a known type stored in a place of a type computed at run time
                // (docs/spec/mir/typing.md, "Types Computed at Run Time"): the value is built
                // in a temporary of its own type, so that the change of representation is an
                // assignment between two locals with faithful declared types (constants such
                // as constructors carry only a placeholder type).
                self.push_statement(Statement::StorageLive(temp));
                let value_end = self.new_block();
                self.lower_term(term, Place::from(temp), value_end)?;
                self.set_block(value_end);
                let value = self.local_operand(temp);
                self.push_statement(Statement::Assign(destination, Rvalue::Use(value)));
                self.push_statement(Statement::StorageDead(temp));
                self.terminate(Terminator::Goto { target });
                return Ok(());
            }
        }
        if let Some(nat_value) = self.try_nat_literal(term) {
            let constant = Constant {
                literal: Literal::Nat(nat_value),
                ty: MirType::Nat,
            };
            self.push_statement(Statement::Assign(
                destination,
                Rvalue::Use(Operand::Constant(Box::new(constant))),
            ));
            self.terminate(Terminator::Goto { target });
            return Ok(());
        }
        match &**term {
            Term::Var(idx) => {
                let env_idx = self
                    .debruijn_map
                    .len()
                    .checked_sub(1 + *idx)
                    .ok_or_else(|| {
                        LoweringError::new(format!(
                            "De Bruijn index out of bounds: {} (context size {})",
                            idx,
                            self.debruijn_map.len()
                        ))
                    })?;
                let local = self.debruijn_map[env_idx];
                let operand = if self.borrowed_capture_locals.contains(&local) {
                    Operand::Copy(Place {
                        local,
                        projection: vec![PlaceElem::Deref],
                    })
                } else {
                    // Look up type to decide Move vs Copy
                    let decl = &self.body.local_decls[local.0 as usize];
                    if decl.is_copy {
                        Operand::Copy(Place::from(local))
                    } else {
                        Operand::Move(Place::from(local))
                    }
                };

                self.push_statement(Statement::Assign(destination, Rvalue::Use(operand)));
                self.terminate(Terminator::Goto { target });
            }
            Term::LetE(ty, val, body) => {
                let temp = self.push_temp_local_for_value(val, ty.clone(), None)?;
                self.push_statement(Statement::StorageLive(temp));
                let next_block = self.new_block();
                self.lower_term(val, Place::from(temp), next_block)?;
                self.current_block = next_block;
                let saved_ctx = self.checker_ctx.clone();
                self.checker_ctx = self.checker_ctx.push(ty.clone());
                self.debruijn_map.push(temp);
                let after_body_block = self.new_block();
                self.lower_term(body, destination.clone(), after_body_block)?;
                self.debruijn_map.pop();
                self.checker_ctx = saved_ctx;
                self.set_block(after_body_block);
                self.push_statement(Statement::StorageDead(temp));
                self.terminate(Terminator::Goto { target });
            }
            Term::App(_, _, _) if self.term_is_type(term) => {
                // A type APPLICATION (`List Nat`, `Vec A 1`, `T k` with `T : Nat -> Type`) is
                // erased like a bare inductive or Pi: its value is `()`. Lowering it as a call
                // would apply the erased head (a `()` placeholder) at run time.
                let constant = Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                };
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))),
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::App(_, _, _) => {
                let (head, args) = collect_app_spine(term);

                if let Term::Const(name, _) = &*head {
                    if let Some(def_id) = self.def_id_for_const(&head) {
                        if self.ids.is_index_def(def_id) {
                            if args.len() < 2 {
                                return Err(LoweringError::new(
                                    "Index expects a container and index argument".to_string(),
                                ));
                            }
                            let container_term = &args[args.len() - 2];
                            let index_term = &args[args.len() - 1];

                            let (container_place, container_temp) = match &**container_term {
                                Term::Var(_) => (self.place_from_term(container_term)?, None),
                                _ => {
                                    let temp = self.lower_term_to_local(container_term)?;
                                    (Place::from(temp), Some(temp))
                                }
                            };
                            let (index_local, index_temp) = match &**index_term {
                                Term::Var(_) => (self.place_from_term(index_term)?.local, None),
                                _ => {
                                    let temp = self.lower_term_to_local(index_term)?;
                                    (temp, Some(temp))
                                }
                            };

                            let container_ty = self.body.local_decls[container_place.local.index()]
                                .ty
                                .clone();
                            let (adt_id, args) = match container_ty {
                                MirType::Adt(id, args) => (id, args),
                                other => {
                                    return Err(LoweringError::new(format!(
                                        "Indexing expects an ADT container, got {:?}",
                                        other
                                    )));
                                }
                            };

                            if !self.ids.is_indexable_adt(&adt_id) {
                                return Err(LoweringError::new(format!(
                                    "Indexing not supported for {:?}",
                                    adt_id
                                )));
                            }

                            let _elem_ty = args.first().cloned().unwrap_or(MirType::Unit);
                            let mut projection = container_place.projection.clone();
                            projection.push(PlaceElem::Index(index_local));
                            let indexed_place = Place {
                                local: container_place.local,
                                projection,
                            };

                            self.push_statement(Statement::RuntimeCheck(
                                RuntimeCheckKind::BoundsCheck {
                                    local: container_place.local,
                                    index: index_local,
                                },
                            ));

                            // Indexing is a by-value library op; always consume the container.
                            let op = Operand::Move(indexed_place);
                            self.push_statement(Statement::Assign(destination, Rvalue::Use(op)));

                            if let Some(temp) = index_temp {
                                self.push_statement(Statement::StorageDead(temp));
                            }
                            if let Some(temp) = container_temp {
                                self.push_statement(Statement::StorageDead(temp));
                            }

                            self.terminate(Terminator::Goto { target });
                            return Ok(());
                        }
                    }

                    if name == "borrow_shared" || name == "borrow_mut" {
                        let kind = if name == "borrow_shared" {
                            BorrowKind::Shared
                        } else {
                            BorrowKind::Mut
                        };
                        let Some(arg) = args.last() else {
                            return Err(self.lowering_error(format!(
                                "Malformed borrow application: `{}` requires an argument",
                                name
                            )));
                        };
                        let place = self.place_from_term(arg)?;
                        self.push_statement(Statement::Assign(
                            destination,
                            Rvalue::Ref(kind, place),
                        ));
                        self.terminate(Terminator::Goto { target });
                        return Ok(());
                    }
                }

                if let Term::Rec(ind_name, levels) = &*head {
                    let info = self.kernel_env.inductive_info(ind_name).ok_or_else(|| {
                        self.lowering_error(format!(
                            "Unknown inductive in Rec application: {}",
                            ind_name
                        ))
                    })?;
                    let recursor = &info.recursor;
                    let expected_args = recursor.expected_args;

                    if args.len() > expected_args {
                        let mut rec_term = head.clone();
                        for arg in args.iter().take(expected_args) {
                            rec_term = Term::app(rec_term, arg.clone());
                        }
                        let func_local = self.lower_term_to_local(&rec_term)?;
                        let mut current_func = func_local;
                        let mut current_func_ty =
                            self.body.local_decls[current_func.index()].ty.clone();
                        let mut current_func_is_temp = true;

                        for (i, arg) in args.iter().skip(expected_args).enumerate() {
                            let is_last = i == args.len() - expected_args - 1;
                            let temp_arg = self.lower_term_to_local(arg)?;
                            let result_ty = self.apply_function_type(&current_func_ty)?;
                            let call_dest = if is_last {
                                destination.clone()
                            } else {
                                let t = self.push_mir_local(result_ty.clone(), None);
                                self.push_statement(Statement::StorageLive(t));
                                Place::from(t)
                            };

                            let next_block = self.new_block();
                            let func_operand =
                                self.call_operand_for_func(current_func, &current_func_ty);
                            self.terminate(Terminator::Call {
                                func: func_operand,
                                args: vec![self.local_operand(temp_arg)],
                                destination: call_dest.clone(),
                                target: Some(next_block),
                            });

                            self.set_block(next_block);
                            self.push_statement(Statement::StorageDead(temp_arg));

                            if !is_last {
                                if current_func_is_temp {
                                    self.push_statement(Statement::StorageDead(current_func));
                                }
                                current_func = call_dest.local;
                                current_func_ty = result_ty;
                                current_func_is_temp = true;
                            } else if current_func_is_temp {
                                self.push_statement(Statement::StorageDead(current_func));
                            }
                        }

                        self.terminate(Terminator::Goto { target });
                        return Ok(());
                    }

                    self.lower_rec(ind_name, levels, &args, destination, target)?;
                    return Ok(());
                }

                let mut current_func_place: Option<Place> = None;
                let mut current_func_is_temp = true;
                let mut current_func = if let Term::Var(_) = &*head {
                    let place = self.place_from_term(&head)?;
                    if place.projection.is_empty() {
                        current_func_place = Some(place.clone());
                        current_func_is_temp = false;
                        place.local
                    } else {
                        self.lower_term_to_local(&head)?
                    }
                } else {
                    self.lower_term_to_local(&head)?
                };
                let mut current_func_ty = self.body.local_decls[current_func.index()].ty.clone();

                for (i, arg) in args.iter().enumerate() {
                    let is_last = i == args.len() - 1;
                    let temp_arg = self.lower_term_to_local(arg)?;
                    let result_ty = self.apply_function_type(&current_func_ty)?;
                    let call_dest = if is_last {
                        destination.clone()
                    } else {
                        let t = self.push_mir_local(result_ty.clone(), None);
                        self.push_statement(Statement::StorageLive(t));
                        Place::from(t)
                    };

                    let next_block = self.new_block();

                    let func_operand = if let Some(place) = current_func_place.as_ref() {
                        self.call_operand_for_place(place, &current_func_ty)
                    } else {
                        self.call_operand_for_func(current_func, &current_func_ty)
                    };
                    self.terminate(Terminator::Call {
                        func: func_operand,
                        args: vec![self.local_operand(temp_arg)],
                        destination: call_dest.clone(),
                        target: Some(next_block),
                    });

                    self.set_block(next_block);
                    self.push_statement(Statement::StorageDead(temp_arg));

                    if !is_last {
                        if current_func_is_temp {
                            self.push_statement(Statement::StorageDead(current_func));
                        }
                        current_func = call_dest.local;
                        current_func_ty = result_ty;
                        current_func_place = None;
                        current_func_is_temp = true;
                    } else if current_func_is_temp {
                        self.push_statement(Statement::StorageDead(current_func));
                    }
                }

                self.terminate(Terminator::Goto { target });
            }

            Term::Sort(_) => {
                let constant = Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                };
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))),
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Const(_, _) => {
                let constant = self.constant_for_term(term.clone())?;
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))),
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Lam(ty, body, _info, kind) => {
                let borrow_fn_values =
                    std::mem::replace(&mut self.borrow_fn_captures_in_next_closure, false);
                let arg_ty = ty.clone();
                // A closure whose type is a proposition (a Pi ending in Prop) is a proof: the
                // kernel never walks it and treats it as Copy. Its body produces a proof, which
                // is erased (never evaluated), so the closure needs no captures: it is built
                // capture-free (and is therefore Copy), and no captured value is moved or
                // borrowed by building it.
                let erased_proof_closure = self.is_prop_type(&self.infer_term_type(term)?)?;
                let mut free_vars = HashSet::new();
                if !erased_proof_closure {
                    collect_free_vars(body, 1, &mut free_vars);
                }
                let (required_modes, capture_modes, erased_only) = if erased_proof_closure {
                    (None, None, HashSet::new())
                } else {
                    let required_modes = self.required_capture_modes_for_closure(ty, body)?;
                    let capture_modes =
                        self.capture_modes_for_required_closure(term, &free_vars)?;
                    self.ensure_capture_modes_complete(term, &free_vars, capture_modes.as_ref())?;
                    let erased_only = self.erased_only_captures(ty, body, &free_vars);
                    (required_modes, capture_modes, erased_only)
                };
                let capture_plan = self.collect_captures(
                    *kind,
                    &free_vars,
                    capture_modes.as_ref(),
                    required_modes.as_ref(),
                    borrow_fn_values,
                    &erased_only,
                )?;

                let mut mir_body = Body::new(2);
                mir_body.adt_layouts = self.ids.adt_layouts().clone();
                mir_body.basic_blocks.push(BasicBlockData {
                    statements: vec![],
                    terminator: None,
                });

                let mut sub_ctx = LoweringContext {
                    body: mir_body,
                    current_block: BasicBlock(0),
                    debruijn_map: Vec::new(),
                    borrowed_capture_locals: std::collections::HashSet::new(),
                    kernel_env: self.kernel_env,
                    ids: self.ids,
                    checker_ctx: Context::new(),
                    derived_bodies: self.derived_bodies.clone(),
                    derived_span_tables: self.derived_span_tables.clone(),
                    span_table: HashMap::new(),
                    term_span_map: self.term_span_map.clone(),
                    capture_mode_map: self.capture_mode_map.clone(),
                    closure_id_map: self.closure_id_map.clone(),
                    def_name: self.def_name.clone(),
                    current_span: None,
                    // Continue the enclosing body's region counter: the closure body's own
                    // regions must not coincide with the regions of its captured types
                    // (allocated by enclosing bodies), which the borrow checker would identify.
                    next_region: self.next_region,
                    borrow_fn_captures_in_next_closure: false,
                    non_copy_closure_locals: HashSet::new(),
                    copy_closure_locals: HashSet::new(),
                };

                if destination.projection.is_empty() {
                    let local = destination.local;
                    let all_captures_copy = capture_plan.is_copy.iter().all(|is_copy| *is_copy);
                    let decl = &mut self.body.local_decls[local.index()];
                    decl.closure_captures.clone_from(&capture_plan.mir_types);
                    if all_captures_copy {
                        if !self.non_copy_closure_locals.contains(&local) && !decl.is_copy {
                            // Closures with copyable captures can be duplicated by cloning.
                            // This keeps recursive recursor minor-premise closures reusable.
                            decl.is_copy = true;
                            self.copy_closure_locals.insert(local);
                        }
                    } else {
                        self.non_copy_closure_locals.insert(local);
                        if self.copy_closure_locals.remove(&local) {
                            // An earlier closure written into this local (another arm) made
                            // it Copy; this one holds a non-Copy capture.
                            decl.is_copy = false;
                        }
                    }
                }

                let ret_ty_term = self.infer_term_type(term)?;
                let ret_ty = match &*ret_ty_term {
                    Term::Pi(_, cod, _, _) => cod.clone(),
                    other => {
                        return Err(LoweringError::new(format!(
                            "Expected lambda type to be Pi, got {:?}",
                            other
                        )));
                    }
                };
                let outer_checker_ctx = self.checker_ctx.clone();
                sub_ctx.checker_ctx = outer_checker_ctx.clone();
                let arg_mir_ty = sub_ctx.lower_type(&arg_ty)?;
                sub_ctx.checker_ctx = outer_checker_ctx.push(arg_ty.clone());
                let ret_mir_ty = sub_ctx.lower_type(&ret_ty)?;

                sub_ctx.push_temp_local_with_mir(
                    ret_ty.clone(),
                    ret_mir_ty,
                    Some("_0".to_string()),
                )?;
                sub_ctx.checker_ctx = outer_checker_ctx.clone();

                let env_local = sub_ctx.push_temp_local(
                    Rc::new(Term::Sort(kernel::ast::Level::Zero)),
                    Some("env".to_string()),
                )?;
                if !capture_plan.mir_types.is_empty() {
                    sub_ctx.body.local_decls[env_local.index()]
                        .closure_captures
                        .clone_from(&capture_plan.mir_types);
                }
                sub_ctx.checker_ctx = outer_checker_ctx.clone();
                let arg_local = sub_ctx.push_temp_local_with_mir(
                    arg_ty.clone(),
                    arg_mir_ty,
                    Some("arg0".to_string()),
                )?;
                sub_ctx.checker_ctx = Context::new();

                let mut capture_locals = HashMap::new();
                for (i, outer_idx) in capture_plan.outer_indices.iter().enumerate() {
                    let mir_ty = capture_plan.mir_types[i].clone();
                    let cap_local_idx = sub_ctx.body.local_decls.len();
                    sub_ctx.body.local_decls.push(LocalDecl {
                        ty: mir_ty.clone(),
                        name: None,
                        is_prop: false,
                        is_copy: capture_plan.is_copy[i],
                        closure_captures: Vec::new(),
                    });
                    let cap_local = Local(cap_local_idx as u32);

                    let env_field = Place {
                        local: env_local,
                        projection: vec![PlaceElem::Field(i)],
                    };
                    let cap_operand = if capture_plan.is_copy[i] {
                        Operand::Copy(env_field)
                    } else {
                        Operand::Move(env_field)
                    };
                    sub_ctx.push_statement(Statement::Assign(
                        Place::from(cap_local),
                        Rvalue::Use(cap_operand),
                    ));
                    if capture_plan.borrowed[i] {
                        sub_ctx.borrowed_capture_locals.insert(cap_local);
                    }
                    capture_locals.insert(*outer_idx, cap_local);
                }

                let outer_len = self.debruijn_map.len();
                for pos in 0..outer_len {
                    let idx = outer_len - 1 - pos;
                    let Some(term_ty) = self.checker_ctx.get(idx) else {
                        return Err(LoweringError::new("Capture type lookup failed".to_string()));
                    };
                    let local = if let Some(cap_local) = capture_locals.get(&idx) {
                        *cap_local
                    } else {
                        let parent_local = self.debruijn_map[pos];
                        let decl = &self.body.local_decls[parent_local.index()];
                        let placeholder_idx = sub_ctx.body.local_decls.len();
                        sub_ctx.body.local_decls.push(LocalDecl {
                            ty: decl.ty.clone(),
                            name: None,
                            is_prop: decl.is_prop,
                            is_copy: decl.is_copy,
                            closure_captures: Vec::new(),
                        });
                        Local(placeholder_idx as u32)
                    };
                    sub_ctx.debruijn_map.push(local);
                    sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(term_ty);
                }

                sub_ctx.debruijn_map.push(arg_local);
                sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(arg_ty);

                let return_block = sub_ctx.new_block();
                if erased_proof_closure {
                    // The closure captured nothing: its body (a proof) is not evaluated, and
                    // must not read the outer variables either.
                    sub_ctx.lower_erased_proof_value(body, Place::from(Local(0)), return_block)?;
                } else {
                    sub_ctx.lower_term(body, Place::from(Local(0)), return_block)?;
                }
                sub_ctx.set_block(return_block);
                sub_ctx.terminate_with_term_span(body, Terminator::Return);

                let body_obj = sub_ctx.body;
                let index = self.derived_bodies.borrow().len();
                self.derived_bodies.borrow_mut().push(body_obj);
                self.derived_span_tables
                    .borrow_mut()
                    .push(sub_ctx.span_table);

                let fn_ty = self.infer_term_type(term)?;
                let closure_ty = self.function_value_mir_type(term, &fn_ty)?.ok_or_else(|| {
                    LoweringError::new("Failed to lower closure type for lambda".to_string())
                })?;
                let constant = Constant {
                    literal: Literal::Closure(index, capture_plan.operands),
                    ty: closure_ty,
                };

                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))),
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Ctor(name, idx, _) => {
                let ctor_id = self
                    .ids
                    .ctor_id(name, *idx)
                    .unwrap_or_else(|| CtorId::new(AdtId::new(name), *idx));
                let arity = self
                    .ids
                    .ctor_arity(&ctor_id)
                    .or_else(|| self.get_ctor_arity(name, *idx))
                    .unwrap_or(0);
                let runtime_arity = self
                    .ids
                    .adt_layouts()
                    .get(&ctor_id.adt)
                    .and_then(|layout| layout.variants.get(*idx))
                    .map(|variant| variant.fields.len())
                    .unwrap_or(arity);
                let constant = Constant {
                    literal: Literal::InductiveCtor(ctor_id, arity, runtime_arity),
                    ty: MirType::Unit,
                };
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))),
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Pi(_, _, _, _) | Term::Ind(_, _) => {
                let constant = Constant {
                    literal: Literal::Unit,
                    ty: MirType::Unit,
                };
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))),
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Rec(_, _) => {
                let constant = self.constant_for_term(term.clone())?;
                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))),
                ));
                self.terminate(Terminator::Goto { target });
            }
            Term::Meta(id) => {
                return Err(LoweringError::new(format!(
                    "Unresolved metavariable ?{} in lowering",
                    id
                )));
            }
            Term::Fix(ty, body) => {
                let (arg_ty, fn_kind) = match &**ty {
                    Term::Pi(dom, _, _, kind) => (dom.clone(), *kind),
                    _ => {
                        return Err(LoweringError::new(format!(
                            "Expected Pi type for fix, got {:?}",
                            ty
                        )));
                    }
                };
                let mut free_vars = HashSet::new();
                collect_free_vars(body, 1, &mut free_vars);
                let required_modes = self.required_capture_modes_for_closure(&arg_ty, body)?;
                let capture_modes = self.capture_modes_for_required_closure(term, &free_vars)?;
                self.ensure_capture_modes_complete(term, &free_vars, capture_modes.as_ref())?;
                let capture_plan = self.collect_captures(
                    fn_kind,
                    &free_vars,
                    capture_modes.as_ref(),
                    required_modes.as_ref(),
                    false,
                    &HashSet::new(),
                )?;

                let mut mir_body = Body::new(2);
                mir_body.adt_layouts = self.ids.adt_layouts().clone();
                mir_body.basic_blocks.push(BasicBlockData {
                    statements: vec![],
                    terminator: None,
                });

                let mut sub_ctx = LoweringContext {
                    body: mir_body,
                    current_block: BasicBlock(0),
                    debruijn_map: Vec::new(),
                    borrowed_capture_locals: std::collections::HashSet::new(),
                    kernel_env: self.kernel_env,
                    ids: self.ids,
                    checker_ctx: Context::new(),
                    derived_bodies: self.derived_bodies.clone(),
                    derived_span_tables: self.derived_span_tables.clone(),
                    span_table: HashMap::new(),
                    term_span_map: self.term_span_map.clone(),
                    capture_mode_map: self.capture_mode_map.clone(),
                    closure_id_map: self.closure_id_map.clone(),
                    def_name: self.def_name.clone(),
                    current_span: None,
                    // Continue the enclosing body's region counter: the closure body's own
                    // regions must not coincide with the regions of its captured types
                    // (allocated by enclosing bodies), which the borrow checker would identify.
                    next_region: self.next_region,
                    borrow_fn_captures_in_next_closure: false,
                    non_copy_closure_locals: HashSet::new(),
                    copy_closure_locals: HashSet::new(),
                };

                if destination.projection.is_empty() {
                    let decl = &mut self.body.local_decls[destination.local.index()];
                    decl.closure_captures.clone_from(&capture_plan.mir_types);
                }

                let ret_ty = match &**ty {
                    Term::Pi(_, cod, _, _) => cod.clone(),
                    _ => {
                        return Err(LoweringError::new(format!(
                            "Expected Pi return type for fix, got {:?}",
                            ty
                        )));
                    }
                };
                let outer_checker_ctx = self.checker_ctx.clone();
                sub_ctx.checker_ctx = outer_checker_ctx.clone();
                let arg_mir_ty = sub_ctx.lower_type(&arg_ty)?;
                sub_ctx.checker_ctx = outer_checker_ctx.push(arg_ty.clone());
                let ret_mir_ty = sub_ctx.lower_type(&ret_ty)?;

                sub_ctx.push_temp_local_with_mir(
                    ret_ty.clone(),
                    ret_mir_ty,
                    Some("_0".to_string()),
                )?;
                sub_ctx.checker_ctx = outer_checker_ctx.clone();

                let env_local = sub_ctx.push_temp_local(
                    Rc::new(Term::Sort(kernel::ast::Level::Zero)),
                    Some("env".to_string()),
                )?;
                // env[0] is the fixpoint itself (read below as `self`), env[1..] the captures;
                // record the self slot even without captures so that the environment shape
                // matches the body's reads (the typed backend requires it).
                let mut env_types = Vec::with_capacity(capture_plan.mir_types.len() + 1);
                env_types.push(self.lower_type(ty)?);
                env_types.extend(capture_plan.mir_types.clone());
                sub_ctx.body.local_decls[env_local.index()].closure_captures = env_types;
                sub_ctx.checker_ctx = outer_checker_ctx.clone();
                let arg_local = sub_ctx.push_temp_local_with_mir(
                    arg_ty.clone(),
                    arg_mir_ty,
                    Some("arg0".to_string()),
                )?;
                sub_ctx.checker_ctx = Context::new();

                let mut capture_locals = HashMap::new();
                // Unpack captures from env fields starting at 1 (env[0] is self)
                for (i, outer_idx) in capture_plan.outer_indices.iter().enumerate() {
                    let mir_ty = capture_plan.mir_types[i].clone();
                    let cap_local_idx = sub_ctx.body.local_decls.len();
                    sub_ctx.body.local_decls.push(LocalDecl {
                        ty: mir_ty.clone(),
                        name: None,
                        is_prop: false,
                        is_copy: capture_plan.is_copy[i],
                        closure_captures: Vec::new(),
                    });
                    let cap_local = Local(cap_local_idx as u32);

                    sub_ctx.push_statement(Statement::Assign(
                        Place::from(cap_local),
                        Rvalue::Use(Operand::Copy(Place {
                            local: env_local,
                            projection: vec![PlaceElem::Field(i + 1)],
                        })),
                    ));
                    if capture_plan.borrowed[i] {
                        sub_ctx.borrowed_capture_locals.insert(cap_local);
                    }
                    capture_locals.insert(*outer_idx, cap_local);
                }

                let outer_len = self.debruijn_map.len();
                for pos in 0..outer_len {
                    let idx = outer_len - 1 - pos;
                    let Some(term_ty) = self.checker_ctx.get(idx) else {
                        return Err(LoweringError::new("Capture type lookup failed".to_string()));
                    };
                    let local = if let Some(cap_local) = capture_locals.get(&idx) {
                        *cap_local
                    } else {
                        let parent_local = self.debruijn_map[pos];
                        let decl = &self.body.local_decls[parent_local.index()];
                        let placeholder_idx = sub_ctx.body.local_decls.len();
                        sub_ctx.body.local_decls.push(LocalDecl {
                            ty: decl.ty.clone(),
                            name: None,
                            is_prop: decl.is_prop,
                            is_copy: decl.is_copy,
                            closure_captures: Vec::new(),
                        });
                        Local(placeholder_idx as u32)
                    };
                    sub_ctx.debruijn_map.push(local);
                    sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(term_ty);
                }

                // Bind self from env[0]
                let self_local = sub_ctx.push_temp_local(ty.clone(), Some("self".to_string()))?;
                sub_ctx.push_statement(Statement::Assign(
                    Place::from(self_local),
                    Rvalue::Use(Operand::Copy(Place {
                        local: env_local,
                        projection: vec![PlaceElem::Field(0)],
                    })),
                ));
                sub_ctx.debruijn_map.push(self_local);
                sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(ty.clone());

                // Argument is last
                sub_ctx.debruijn_map.push(arg_local);
                sub_ctx.checker_ctx = sub_ctx.checker_ctx.push(arg_ty);

                let return_block = sub_ctx.new_block();

                // The fixpoint body is a function of the argument. When it is a syntactic λ,
                // lower its body directly (the argument local plays the role of the λ-binder:
                // Var(0) = argument, Var(1) = self). Building `(shift body) arg` instead would
                // create fresh terms whose closures have no span/capture metadata (keyed by
                // term pointer), so a capturing closure inside the body could not be lowered.
                if let Term::Lam(_, lam_body, _, _) = &**body {
                    sub_ctx.lower_term(lam_body, Place::from(Local(0)), return_block)?;
                    sub_ctx.set_block(return_block);
                    sub_ctx.terminate_with_term_span(lam_body, Terminator::Return);
                } else {
                    let shifted_body = body.shift(0, 1);
                    let body_app = Term::app(shifted_body, Rc::new(Term::Var(0)));
                    sub_ctx.lower_term(&body_app, Place::from(Local(0)), return_block)?;
                    sub_ctx.set_block(return_block);
                    sub_ctx.terminate_with_term_span(&body_app, Terminator::Return);
                }

                let body_obj = sub_ctx.body;
                let index = self.derived_bodies.borrow().len();
                self.derived_bodies.borrow_mut().push(body_obj);
                self.derived_span_tables
                    .borrow_mut()
                    .push(sub_ctx.span_table);

                let closure_ty = self.function_value_mir_type(term, ty)?.ok_or_else(|| {
                    LoweringError::new("Failed to lower closure type for fixpoint".to_string())
                })?;
                let constant = Constant {
                    literal: Literal::Fix(index, capture_plan.operands),
                    ty: closure_ty,
                };

                self.push_statement(Statement::Assign(
                    destination,
                    Rvalue::Use(Operand::Constant(Box::new(constant))),
                ));
                self.terminate(Terminator::Goto { target });
            }
        }

        Ok(())
    }

    fn constant_for_term(&mut self, term: Rc<Term>) -> LoweringResult<Constant> {
        let ty = self.infer_term_type(&term)?;
        let literal = match &*term {
            Term::Sort(_) | Term::Pi(_, _, _, _) | Term::Ind(_, _) => Literal::Unit,
            Term::Const(name, _) => Literal::GlobalDef(name.clone()),
            Term::Rec(name, _) => Literal::Recursor(name.clone()),
            _ => Literal::OpaqueConst(opaque_reason(&term)),
        };
        if let Some(mir_ty) = self.function_value_mir_type(&term, &ty)? {
            return Ok(Constant {
                literal,
                ty: mir_ty,
            });
        }
        let mir_ty = self.lower_type_general(&ty)?;
        Ok(Constant {
            literal,
            ty: mir_ty,
        })
    }

    fn lower_rec(
        &mut self,
        ind_name: &str,
        levels: &[Level],
        args: &[Rc<Term>],
        destination: Place,
        target: BasicBlock,
    ) -> LoweringResult<()> {
        let decl = self.kernel_env.get_inductive(ind_name).ok_or_else(|| {
            self.lowering_error(format!("Unknown inductive in Rec: {}", ind_name))
        })?;
        let info = self.kernel_env.inductive_info(ind_name).ok_or_else(|| {
            self.lowering_error(format!(
                "Missing recursor metadata for inductive: {}",
                ind_name
            ))
        })?;
        let recursor = &info.recursor;
        let n_params = recursor.num_params;
        let n_motives = 1;
        let n_minors = recursor.num_ctors;
        let n_indices = recursor.num_indices;
        let expected_args = recursor.expected_args;

        if args.len() < expected_args {
            // An unsaturated recursor application used to be emitted as an opaque constant,
            // which no backend can execute (the dynamic binary panicked with "OpaqueConst
            // literal reached codegen", the typed backend's Rust output did not compile).
            // Reject it here instead, with a hint.
            return Err(self.lowering_error(format!(
                "Partially applied recursor for '{}' ({} of {} arguments) is not supported by code generation; apply it to all of its arguments (eta-expand it, e.g. (lam n T ((rec {}) ... n)))",
                ind_name,
                args.len(),
                expected_args,
                ind_name
            )));
        }

        let major_premise = &args[args.len() - 1];

        let params = &args[..n_params];
        let motive_term = &args[n_params];
        let minors_start = n_params + n_motives;
        let minor_terms = &args[minors_start..minors_start + n_minors];
        let indices_start = minors_start + n_minors;
        let index_terms = &args[indices_start..indices_start + n_indices];

        // Constructor fields with the parameters instantiated. Every binder after the
        // parameters is a field (implicit binders included): it is stored in the runtime
        // value (see `ctor_field_templates`) and bound by the kernel's minor premise.
        let ctor_insts: Vec<Rc<Term>> = decl
            .ctors
            .iter()
            .map(|ctor| instantiate_params(ctor.ty.clone(), params))
            .collect();
        let ctor_field_types: Vec<Vec<Rc<Term>>> = ctor_insts
            .iter()
            .map(|ctor_inst| peel_pi_binders(ctor_inst).0)
            .collect();
        let ctor_has_recursive_field: Vec<bool> = ctor_field_types
            .iter()
            .map(|fields| fields.iter().any(|f| is_recursive_head(f, ind_name)))
            .collect();
        let unreachable_arms =
            self.unreachable_rec_arms(ind_name, n_params, &ctor_insts, index_terms);

        if !ctor_has_recursive_field.iter().any(|has_rec| *has_rec) {
            let constant_motive = motive_is_constant(motive_term, n_indices + 1);
            return self.lower_rec_alternatives(
                &ctor_field_types,
                minor_terms,
                &unreachable_arms,
                constant_motive,
                major_premise,
                destination,
                target,
            );
        }

        let mut param_locals = Vec::new();
        for param in params {
            param_locals.push(self.lower_term_to_local(param)?);
        }
        let motive_local = self.lower_term_to_local(motive_term)?;
        let mut minor_locals = Vec::new();
        for (ctor_idx, minor) in minor_terms.iter().enumerate() {
            // The minor of a constructor with a recursive field is passed to the recursive
            // call(s) computing the induction hypotheses and then called: lower it as a
            // duplicable closure where possible (see `borrow_fn_captures_in_next_closure`).
            self.borrow_fn_captures_in_next_closure =
                ctor_has_recursive_field[ctor_idx] && matches!(&**minor, Term::Lam(..));
            let lowered = self.lower_term_to_local(minor);
            self.borrow_fn_captures_in_next_closure = false;
            minor_locals.push(lowered?);
        }
        let mut index_locals = Vec::new();
        for idx in index_terms {
            index_locals.push(self.lower_term_to_local(idx)?);
        }
        let mut shared_locals = Vec::new();
        shared_locals.extend_from_slice(&param_locals);
        shared_locals.push(motive_local);
        shared_locals.extend_from_slice(&minor_locals);
        shared_locals.extend_from_slice(&index_locals);

        let (temp_major, discr_temp, target_blocks) =
            self.lower_rec_major_and_switch(major_premise, decl.ctors.len())?;
        let major_adt = match &self.body.local_decls[temp_major.index()].ty {
            MirType::Adt(adt_id, args) => Some((adt_id.clone(), args.clone())),
            _ => None,
        };
        shared_locals.extend(discr_temp);
        shared_locals.push(temp_major);

        let base_ctx = self.checker_ctx.clone();

        for (i, arm_block) in target_blocks.iter().enumerate() {
            self.set_block(*arm_block);
            self.checker_ctx = base_ctx.clone();
            if unreachable_arms[i] {
                // The constructor's indices clash with the scrutinee's: the kernel-checked
                // type rules this constructor out, so the arm can never run.
                self.terminate(Terminator::Unreachable);
                continue;
            }

            // Only a duplicable (Copy) minor premise may be handed to the entry function, which
            // calls it once per recursive occurrence out of MIR's sight: a minor that consumes a
            // captured value is not Copy and keeps the unpacked lowering, where MIR rejects it.
            if self.local_is_copy(minor_locals[i])
                && self.rec_arm_dispatches_to_entry(
                    ind_name,
                    &ctor_field_types[i],
                    &minor_terms[i],
                )?
            {
                // A non-Copy recursive field is consumed by the computation of its induction
                // hypothesis, and the minor premise does not use it at run time (it binds it
                // only nominally, as the kernel requires). Unpacking the arm here would move the
                // field twice (into the IH call and into the minor's argument list), so the
                // whole major premise is handed to the recursor's entry function instead, which
                // performs the same dispatch (and passes the minor premise its own copy of the
                // unused field).
                let mut rec_args: Vec<Rc<Term>> = params.to_vec();
                rec_args.push(motive_term.clone());
                rec_args.extend(minor_terms.iter().cloned());
                rec_args.extend(index_terms.iter().cloned());
                let rec_local =
                    self.push_recursor_entry_local(ind_name, levels, decl, &rec_args)?;
                let mut entry_args = Vec::new();
                for &p in &param_locals {
                    entry_args.push(self.local_operand(p));
                }
                entry_args.push(self.local_operand(motive_local));
                for &m in &minor_locals {
                    entry_args.push(self.local_operand(m));
                }
                for &idx_local in &index_locals {
                    entry_args.push(self.local_operand(idx_local));
                }
                entry_args.push(self.local_operand(temp_major));
                self.call_with_args(rec_local, &entry_args, Some(destination.clone()))?;
                let mut dropped = HashSet::new();
                for local in std::iter::once(&rec_local).chain(shared_locals.iter().rev()) {
                    if dropped.insert(*local) {
                        self.push_statement(Statement::StorageDead(*local));
                    }
                }
                self.terminate(Terminator::Goto { target });
                continue;
            }

            let mut args_for_minor = Vec::new();

            let minor_local = minor_locals[i];
            let field_types = &ctor_field_types[i];
            let mut field_locals = Vec::new();
            let mut arm_locals = Vec::new();
            // Field `k`'s type may mention the fields before it: type it in the context
            // extended with them (it used to be typed in the outer context, which mis-scoped
            // dependent fields such as `i : Fin n`).
            let mut field_ctx = base_ctx.clone();

            for (field_pos, field_ty) in field_types.iter().enumerate() {
                let field_place = Place {
                    local: temp_major,
                    projection: vec![PlaceElem::Downcast(i), PlaceElem::Field(field_pos)],
                };
                self.checker_ctx = field_ctx.clone();
                let field_local =
                    self.push_rec_field_local(major_adt.as_ref(), i, field_pos, field_ty)?;
                self.checker_ctx = base_ctx.clone();
                field_ctx = field_ctx.push(field_ty.clone());
                self.push_statement(Statement::StorageLive(field_local));
                let field_operand = self.field_read_operand(
                    major_adt.as_ref(),
                    i,
                    field_pos,
                    field_place,
                    field_local,
                );
                self.push_statement(Statement::Assign(
                    Place::from(field_local),
                    Rvalue::Use(field_operand),
                ));

                let prev_len = field_locals.len();
                field_locals.push(field_local);
                arm_locals.push(field_local);

                args_for_minor.push(self.local_operand(field_local));

                if is_recursive_head(field_ty, ind_name) {
                    let rec_index_terms = extract_inductive_indices(field_ty, ind_name, n_params);
                    let mut rec_index_locals = Vec::new();
                    let mut rec_index_temps = Vec::new();
                    let mut rec_index_terms_final: Option<Vec<Rc<Term>>> = None;
                    if let Some(terms) = rec_index_terms {
                        if terms.len() == n_indices {
                            let prev_locals = &field_locals[..prev_len];
                            let prev_types = &field_types[..prev_len];
                            for term in terms.iter() {
                                let idx_local =
                                    self.eval_term_with_locals(term, prev_locals, prev_types)?;
                                rec_index_locals.push(idx_local);
                                rec_index_temps.push(idx_local);
                            }
                            rec_index_terms_final = Some(terms);
                        }
                    }

                    if rec_index_locals.len() != n_indices {
                        rec_index_locals.clone_from(&index_locals);
                        rec_index_temps.clear();
                        rec_index_terms_final = Some(index_terms.to_vec());
                    }

                    let mut rec_args: Vec<Rc<Term>> = params.to_vec();
                    rec_args.push(motive_term.clone());
                    rec_args.extend(minor_terms.iter().cloned());
                    let rec_index_terms = rec_index_terms_final.as_deref().unwrap_or(index_terms);
                    rec_args.extend(rec_index_terms.iter().cloned());
                    let rec_local =
                        self.push_recursor_entry_local(ind_name, levels, decl, &rec_args)?;
                    let mut ih_args = Vec::new();
                    for &p in &param_locals {
                        ih_args.push(self.local_operand(p));
                    }
                    ih_args.push(self.local_operand(motive_local));
                    for &m in &minor_locals {
                        ih_args.push(self.local_operand(m));
                    }
                    for &idx_local in &rec_index_locals {
                        ih_args.push(self.local_operand(idx_local));
                    }
                    ih_args.push(self.local_operand(field_local));

                    let ih_local = self.call_with_args(rec_local, &ih_args, None)?;
                    arm_locals.push(rec_local);
                    arm_locals.extend(rec_index_temps);
                    arm_locals.push(ih_local);
                    args_for_minor.push(self.local_operand(ih_local));
                }
            }
            self.checker_ctx = base_ctx.clone();

            if args_for_minor.is_empty() {
                self.push_statement(Statement::Assign(
                    destination.clone(),
                    Rvalue::Use(self.local_operand(minor_local)),
                ));
            } else {
                self.call_with_args(minor_local, &args_for_minor, Some(destination.clone()))?;
            }

            let mut dropped = HashSet::new();
            for local in arm_locals.iter().rev().chain(shared_locals.iter().rev()) {
                if dropped.insert(*local) {
                    self.push_statement(Statement::StorageDead(*local));
                }
            }

            self.terminate(Terminator::Goto { target });
        }
        self.checker_ctx = base_ctx;

        Ok(())
    }

    fn local_has_stuck_type(&self, place: &Place) -> bool {
        place.projection.is_empty()
            && self
                .body
                .local_decls
                .get(place.local.index())
                .is_some_and(|decl| decl.ty.is_stuck_type())
    }

    /// For a term to be stored in a place of a stuck type: a temporary of the term's own type,
    /// if that type is known (not stuck) and first-order (see `lower_term`).
    fn push_temp_for_known_value_into_stuck(
        &mut self,
        term: &Rc<Term>,
    ) -> LoweringResult<Option<Local>> {
        let Ok(term_ty) = self.infer_term_type(term) else {
            return Ok(None);
        };
        let Ok(mir_ty) = self.lower_type(&term_ty) else {
            return Ok(None);
        };
        if !matches!(
            mir_ty,
            MirType::Unit | MirType::Bool | MirType::Nat | MirType::Adt(..)
        ) {
            return Ok(None);
        }
        Ok(Some(self.push_temp_local(term_ty, None)?))
    }

    /// Lowers the body of an inline alternative (a minor premise of a non-recursive recursor)
    /// into `destination` when the motive is not constant. The body's type is the motive at the
    /// alternative's constructor, which for a large elimination can differ from the
    /// destination's type, the motive at the scrutinee: a stuck type (`MirType::is_stuck_type`,
    /// e.g. `BoolOrNat b` for an unknown `b`) on one side and a known type on the other, or two
    /// different known types (`Nat` and `Bool` for a scrutinee known to be `true`, in which case
    /// the alternative is never taken). The body is then lowered into a temporary of its own
    /// type and moved into the destination, through a stuck temporary in the second case, so
    /// that every assignment relates a stuck type and a known one (MIR typing accepts that for
    /// loan-free known types; see docs/spec/mir/typing.md, "Types Computed at Run Time").
    fn lower_alternative_body(
        &mut self,
        body: &Rc<Term>,
        destination: Place,
        target: BasicBlock,
    ) -> LoweringResult<()> {
        if !destination.projection.is_empty() {
            return self.lower_term(body, destination, target);
        }
        let dest_ty = self.body.local_decls[destination.local.index()].ty.clone();
        let Ok(body_kernel_ty) = self.infer_term_type(body) else {
            return self.lower_term(body, destination, target);
        };
        let Ok(body_ty) = self.lower_type(&body_kernel_ty) else {
            return self.lower_term(body, destination, target);
        };
        let route_through_stuck = match (body_ty.is_stuck_type(), dest_ty.is_stuck_type()) {
            (true, true) => return self.lower_term(body, destination, target),
            (true, false) | (false, true) => false,
            (false, false) => {
                if !known_type_heads_differ(&body_ty, &dest_ty) {
                    return self.lower_term(body, destination, target);
                }
                true
            }
        };
        let temp = self.push_temp_local(body_kernel_ty, None)?;
        self.push_statement(Statement::StorageLive(temp));
        let body_end = self.new_block();
        self.lower_term(body, Place::from(temp), body_end)?;
        self.set_block(body_end);
        let value = self.local_operand(temp);
        if route_through_stuck {
            let stuck = self.push_mir_local(
                MirType::Opaque {
                    reason: crate::types::STUCK_TYPE_REASON.to_string(),
                },
                None,
            );
            self.push_statement(Statement::StorageLive(stuck));
            self.push_statement(Statement::Assign(Place::from(stuck), Rvalue::Use(value)));
            self.push_statement(Statement::Assign(
                destination,
                Rvalue::Use(Operand::Move(Place::from(stuck))),
            ));
            self.push_statement(Statement::StorageDead(stuck));
        } else {
            self.push_statement(Statement::Assign(destination, Rvalue::Use(value)));
        }
        self.push_statement(Statement::StorageDead(temp));
        self.terminate(Terminator::Goto { target });
        Ok(())
    }

    /// A local holding the recursor entry function of `ind_name`, typed as the recursor
    /// specialised to `rec_args` (parameters, motive, minor premises and indices), so that the
    /// assignment and the local declaration agree for MIR typing.
    fn push_recursor_entry_local(
        &mut self,
        ind_name: &str,
        levels: &[Level],
        decl: &kernel::ast::InductiveDecl,
        rec_args: &[Rc<Term>],
    ) -> LoweringResult<Local> {
        let rec_term = Rc::new(Term::Rec(ind_name.to_string(), levels.to_vec()));
        let rec_ty = compute_recursor_type(decl, levels);
        if let Some(spec_ty) = self.specialize_pi_type_with_args_and_last(rec_ty, rec_args)? {
            let local = self.push_mir_local(spec_ty.clone(), None);
            self.push_statement(Statement::StorageLive(local));
            let mut constant = self.constant_for_term(rec_term)?;
            constant.ty = spec_ty;
            self.push_statement(Statement::Assign(
                Place::from(local),
                Rvalue::Use(Operand::Constant(Box::new(constant))),
            ));
            Ok(local)
        } else {
            self.lower_term_to_local(&rec_term)
        }
    }

    /// Whether the arm of a recursive recursor application for a constructor with fields
    /// `field_types` (parameters instantiated) and minor premise `minor` must be delegated to
    /// the recursor's entry function: some recursive field is not Copy (computing its
    /// induction hypothesis consumes it), and `minor` is a λ-chain binding every field and
    /// induction hypothesis whose body uses none of those non-Copy recursive fields at run
    /// time. If the body does use one, the arm is unpacked as usual and the ownership check
    /// reports the double move.
    fn rec_arm_dispatches_to_entry(
        &mut self,
        ind_name: &str,
        field_types: &[Rc<Term>],
        minor: &Rc<Term>,
    ) -> LoweringResult<bool> {
        let saved_ctx = self.checker_ctx.clone();
        let result = self.rec_arm_dispatches_to_entry_in_ctx(ind_name, field_types, minor);
        self.checker_ctx = saved_ctx;
        result
    }

    fn rec_arm_dispatches_to_entry_in_ctx(
        &mut self,
        ind_name: &str,
        field_types: &[Rc<Term>],
        minor: &Rc<Term>,
    ) -> LoweringResult<bool> {
        // Binder positions (in the minor's λ-chain) of the non-Copy recursive fields.
        let base_ctx = self.checker_ctx.clone();
        let mut non_copy_recursive_binders = Vec::new();
        let mut binder_count = 0usize;
        let mut field_ctx = base_ctx.clone();
        for field_ty in field_types {
            let recursive = is_recursive_head(field_ty, ind_name);
            if recursive {
                self.checker_ctx = field_ctx.clone();
                let is_prop = self.is_prop_type(field_ty)?;
                let mir_ty = self.lower_type(field_ty)?;
                if !self.compute_is_copy_for_local(field_ty, &mir_ty, is_prop) {
                    non_copy_recursive_binders.push(binder_count);
                }
            }
            field_ctx = field_ctx.push(field_ty.clone());
            binder_count += if recursive { 2 } else { 1 };
        }
        if non_copy_recursive_binders.is_empty() {
            return Ok(false);
        }

        // The minor premise is a term of the base context (the loop above left
        // `self.checker_ctx` at the context of a recursive field; using it here misaligned
        // the minor's de Bruijn indices whenever the field had predecessors, e.g. `t` in
        // `cons h t`, so a minor using a captured variable could not be typed).
        let mut ctx = base_ctx;
        let mut body = minor.clone();
        for _ in 0..binder_count {
            let Term::Lam(dom, inner, _, _) = &*body else {
                return Ok(false);
            };
            ctx = ctx.push(dom.clone());
            body = inner.clone();
        }
        let Ok(runtime) = kernel::checker::term_runtime_variables(self.kernel_env, &ctx, &body)
        else {
            return Ok(false);
        };
        Ok(non_copy_recursive_binders
            .iter()
            .all(|pos| !runtime.contains(&(binder_count - 1 - pos))))
    }

    /// Lowers the major premise of a recursor application into a fresh local, reads its
    /// discriminant and terminates the current block with a switch over the constructors.
    /// Returns the major local, the discriminant local and one (empty) arm block per
    /// constructor; the caller fills the arms.
    ///
    /// A proof (Prop-typed major) of a single-constructor inductive (e.g. `Eq`) is erased at
    /// run time, so it has no discriminant to read; its only arm is entered directly and no
    /// discriminant local is created.
    fn lower_rec_major_and_switch(
        &mut self,
        major_premise: &Rc<Term>,
        num_ctors: usize,
    ) -> LoweringResult<(Local, Option<Local>, Vec<BasicBlock>)> {
        let major_ty = self.infer_term_type(major_premise)?;
        let temp_major = self.push_temp_local(major_ty, None)?;
        self.push_statement(Statement::StorageLive(temp_major));
        let major_block = self.new_block();
        self.lower_term(major_premise, Place::from(temp_major), major_block)?;
        self.set_block(major_block);

        let mut target_blocks = Vec::new();
        let mut values = Vec::new();
        for ctor_idx in 0..num_ctors {
            let arm_block = self.new_block();
            target_blocks.push(arm_block);
            values.push(ctor_idx as u128);
        }

        if num_ctors == 1 && self.body.local_decls[temp_major.index()].is_prop {
            self.terminate(Terminator::Goto {
                target: target_blocks[0],
            });
            return Ok((temp_major, None, target_blocks));
        }

        let discr_temp = self.push_mir_local(MirType::Nat, None);
        self.push_statement(Statement::StorageLive(discr_temp));
        self.push_statement(Statement::Assign(
            Place::from(discr_temp),
            Rvalue::Discriminant(Place::from(temp_major)),
        ));

        self.terminate(Terminator::SwitchInt {
            discr: Operand::Move(Place::from(discr_temp)),
            targets: SwitchTargets {
                values,
                targets: target_blocks.clone(),
            },
        });
        Ok((temp_major, Some(discr_temp), target_blocks))
    }

    /// Declares the local that receives field `field_pos` of constructor `ctor_idx` when a
    /// recursor arm unpacks the scrutinee. The caller has set `checker_ctx` to the context
    /// in which `field_ty` is well scoped.
    fn push_rec_field_local(
        &mut self,
        major_adt: Option<&(AdtId, Vec<MirType>)>,
        ctor_idx: usize,
        field_pos: usize,
        field_ty: &Rc<Term>,
    ) -> LoweringResult<Local> {
        if let Some((major_adt_id, major_adt_args)) = major_adt {
            if major_adt_id.name() == "Pair" || major_adt_id.name() == "Comp" {
                let field_mir_ty = self
                    .ids
                    .adt_layouts()
                    .field_type(major_adt_id, Some(ctor_idx), field_pos, major_adt_args)
                    .ok_or_else(|| {
                        self.lowering_error(format!(
                            "Missing Pair field type for variant {} field {}",
                            ctor_idx, field_pos
                        ))
                    })?;
                return Ok(self.push_mir_local(field_mir_ty, None));
            }
        }
        self.push_temp_local(field_ty.clone(), None)
    }

    /// The operand that reads field `field_pos` of variant `ctor_idx` out of `field_place` into
    /// `field_local`: a copy when `field_local` is Copy, else a move. Exception: when the field's
    /// type in the ADT layout is a stuck type (computed at run time, e.g. `F zero` for a
    /// type-family parameter `F`, which a layout template cannot instantiate), MIR typing sees
    /// the field place at that non-Copy type, so the field is moved even if the local's known
    /// type (`K zero`, i.e. `Nat`, for `F := K`) is Copy; a stuck type and a loan-free known type
    /// meet as in any assignment (docs/spec/mir/typing.md, "Types Computed at Run Time").
    fn field_read_operand(
        &self,
        major_adt: Option<&(AdtId, Vec<MirType>)>,
        ctor_idx: usize,
        field_pos: usize,
        field_place: Place,
        field_local: Local,
    ) -> Operand {
        let place_is_stuck = major_adt.is_some_and(|(adt_id, adt_args)| {
            self.ids
                .adt_layouts()
                .field_type(adt_id, Some(ctor_idx), field_pos, adt_args)
                .is_some_and(|ty| ty.is_stuck_type())
        });
        if self.local_is_copy(field_local) && !place_is_stuck {
            Operand::Copy(field_place)
        } else {
            Operand::Move(field_place)
        }
    }

    /// `Rec` on a NON-RECURSIVE inductive (no constructor has a field of the inductive
    /// itself): the minor premises are alternatives, exactly one of which runs, once. Each
    /// minor is therefore lowered inside its own switch arm instead of being built as a
    /// closure before the switch:
    /// * a minor that is a syntactic λ-chain binding exactly the constructor's fields is
    ///   inlined: the fields are moved (or copied) out of the scrutinee into locals that play
    ///   the role of the λ-binders and the body is lowered straight into the destination;
    /// * any other minor is evaluated in its arm and applied to the fields (a minor of a
    ///   field-less constructor is just evaluated there).
    ///
    /// Consequently an owned outer value used by several minors is moved only on the path
    /// that runs, and the parameters, motive and indices (needed only by induction
    /// hypotheses, of which there are none) are not evaluated at all.
    #[allow(clippy::too_many_arguments)]
    fn lower_rec_alternatives(
        &mut self,
        ctor_field_types: &[Vec<Rc<Term>>],
        minor_terms: &[Rc<Term>],
        unreachable_arms: &[bool],
        constant_motive: bool,
        major_premise: &Rc<Term>,
        destination: Place,
        target: BasicBlock,
    ) -> LoweringResult<()> {
        let (temp_major, discr_temp, target_blocks) =
            self.lower_rec_major_and_switch(major_premise, ctor_field_types.len())?;
        let major_adt = match &self.body.local_decls[temp_major.index()].ty {
            MirType::Adt(adt_id, args) => Some((adt_id.clone(), args.clone())),
            _ => None,
        };
        let base_ctx = self.checker_ctx.clone();
        let base_len = self.debruijn_map.len();

        for (i, arm_block) in target_blocks.iter().enumerate() {
            self.set_block(*arm_block);
            self.checker_ctx = base_ctx.clone();
            if unreachable_arms[i] {
                self.terminate(Terminator::Unreachable);
                continue;
            }

            let field_types = &ctor_field_types[i];
            let minor = &minor_terms[i];

            // Peel exactly one λ per field.
            let mut binder_types = Vec::new();
            let mut minor_body = minor.clone();
            while binder_types.len() < field_types.len() {
                let next = match &*minor_body {
                    Term::Lam(dom, inner, _, _) => Some((dom.clone(), inner.clone())),
                    _ => None,
                };
                let Some((dom, inner)) = next else {
                    break;
                };
                binder_types.push(dom);
                minor_body = inner;
            }
            let inline = binder_types.len() == field_types.len();

            let mut field_locals = Vec::new();
            for field_pos in 0..field_types.len() {
                let field_ty = if inline {
                    binder_types[field_pos].clone()
                } else {
                    field_types[field_pos].clone()
                };
                let field_local =
                    self.push_rec_field_local(major_adt.as_ref(), i, field_pos, &field_ty)?;
                self.push_statement(Statement::StorageLive(field_local));
                let field_place = Place {
                    local: temp_major,
                    projection: vec![PlaceElem::Downcast(i), PlaceElem::Field(field_pos)],
                };
                let field_operand = self.field_read_operand(
                    major_adt.as_ref(),
                    i,
                    field_pos,
                    field_place,
                    field_local,
                );
                self.push_statement(Statement::Assign(
                    Place::from(field_local),
                    Rvalue::Use(field_operand),
                ));
                field_locals.push(field_local);
                self.checker_ctx = self.checker_ctx.push(field_ty);
            }

            let arm_end = self.new_block();
            let mut minor_local = None;
            if inline {
                self.debruijn_map.extend_from_slice(&field_locals);
                let lowered = if constant_motive {
                    self.lower_term(&minor_body, destination.clone(), arm_end)
                } else {
                    self.lower_alternative_body(&minor_body, destination.clone(), arm_end)
                };
                self.debruijn_map.truncate(base_len);
                lowered?;
            } else {
                self.checker_ctx = base_ctx.clone();
                let local = self.lower_term_to_local(minor)?;
                minor_local = Some(local);
                if field_locals.is_empty() {
                    self.push_statement(Statement::Assign(
                        destination.clone(),
                        Rvalue::Use(self.local_operand(local)),
                    ));
                } else {
                    let field_operands: Vec<Operand> = field_locals
                        .iter()
                        .map(|field_local| self.local_operand(*field_local))
                        .collect();
                    self.call_with_args(local, &field_operands, Some(destination.clone()))?;
                }
                self.terminate(Terminator::Goto { target: arm_end });
            }
            self.set_block(arm_end);
            self.checker_ctx = base_ctx.clone();

            if let Some(local) = minor_local {
                self.push_statement(Statement::StorageDead(local));
            }
            for local in field_locals.iter().rev() {
                self.push_statement(Statement::StorageDead(*local));
            }
            if let Some(discr_temp) = discr_temp {
                self.push_statement(Statement::StorageDead(discr_temp));
            }
            self.push_statement(Statement::StorageDead(temp_major));
            self.terminate(Terminator::Goto { target });
        }
        self.checker_ctx = base_ctx;
        Ok(())
    }

    /// For each constructor, whether its arm of a `Rec` application is unreachable because
    /// the constructor's result indices clash with the scrutinee's indices (`index_terms`,
    /// normalised): e.g. `nil : Vec A zero` can never be the scrutinee of type
    /// `Vec A (succ n)`. Only constructor-headed index terms are compared (no confusion of
    /// distinct constructors); anything else counts as possibly equal, so this is sound for
    /// kernel-checked programs and conservative otherwise. Pruning such arms matters for
    /// "large" eliminations whose motive computes a different type in the impossible case.
    fn unreachable_rec_arms(
        &self,
        ind_name: &str,
        n_params: usize,
        ctor_insts: &[Rc<Term>],
        index_terms: &[Rc<Term>],
    ) -> Vec<bool> {
        ctor_insts
            .iter()
            .map(|ctor_inst| {
                if index_terms.is_empty() {
                    return false;
                }
                let (_, ctor_result) = peel_pi_binders(ctor_inst);
                match extract_inductive_indices(&ctor_result, ind_name, n_params) {
                    Some(ctor_indices) if ctor_indices.len() == index_terms.len() => index_terms
                        .iter()
                        .zip(ctor_indices.iter())
                        .any(|(major_idx, ctor_idx)| self.index_terms_clash(major_idx, ctor_idx)),
                    _ => false,
                }
            })
            .collect()
    }

    /// `major` lives in the current context (it is normalised here); `ctor_side` is a
    /// constructor's result index under the constructor's field binders (only its
    /// constructor structure is inspected, never its variables).
    fn index_terms_clash(&self, major: &Rc<Term>, ctor_side: &Rc<Term>) -> bool {
        let (ctor_head, ctor_args) = collect_app_spine(ctor_side);
        let Term::Ctor(ctor_name, ctor_idx, _) = &*ctor_head else {
            return false;
        };
        // Normalisation failure only means "unknown": the arm is kept.
        let Ok(major_norm) = whnf_in_ctx(
            self.kernel_env,
            &self.checker_ctx,
            major.clone(),
            Transparency::Reducible,
        ) else {
            return false;
        };
        let (major_head, major_args) = collect_app_spine(&major_norm);
        let Term::Ctor(major_name, major_idx, _) = &*major_head else {
            return false;
        };
        if major_name != ctor_name || major_idx != ctor_idx {
            return true;
        }
        major_args.len() == ctor_args.len()
            && major_args
                .iter()
                .zip(ctor_args.iter())
                .any(|(major_arg, ctor_arg)| self.index_terms_clash(major_arg, ctor_arg))
    }

    fn get_ctor_arity(&self, ind_name: &str, ctor_idx: usize) -> Option<usize> {
        let decl = self.kernel_env.inductives.get(ind_name)?;
        if ctor_idx >= decl.ctors.len() {
            return None;
        }

        let ctor = &decl.ctors[ctor_idx];
        let mut ty = &ctor.ty;
        let mut pi_count = 0;
        while let Term::Pi(_, body, _, _) = &**ty {
            pi_count += 1;
            ty = body;
        }

        Some(pi_count)
    }

    fn is_type_copy(&self, ty: &Rc<Term>) -> bool {
        kernel::checker::is_copy_type_in_env(self.kernel_env, ty)
    }

    fn try_nat_literal(&self, term: &Rc<Term>) -> Option<u64> {
        match &**term {
            Term::Ctor(name, idx, _)
                if *idx == 0 && self.kernel_env.is_builtin(Builtin::Nat, name) =>
            {
                Some(0)
            }
            Term::App(fun, arg, _) => match &**fun {
                Term::Ctor(name, idx, _)
                    if *idx == 1 && self.kernel_env.is_builtin(Builtin::Nat, name) =>
                {
                    self.try_nat_literal(arg)?.checked_add(1)
                }
                _ => None,
            },
            _ => None,
        }
    }
}

fn collect_app_spine(term: &Rc<Term>) -> (Rc<Term>, Vec<Rc<Term>>) {
    let mut args = Vec::new();
    let mut current = term.clone();

    loop {
        let next = if let Term::App(f, a, _) = &*current {
            Some((f.clone(), a.clone()))
        } else {
            None
        };

        if let Some((f, a)) = next {
            args.push(a);
            current = f;
        } else {
            break;
        }
    }
    args.reverse();
    (current, args)
}

fn opaque_reason(term: &Rc<Term>) -> String {
    match &**term {
        Term::Const(name, _) => format!("const {}", name),
        Term::Var(idx) => format!("var {}", idx),
        Term::App(_, _, _) => {
            let (head, _) = collect_app_spine(term);
            match &*head {
                Term::Const(name, _) => format!("app {}", name),
                Term::Ind(name, _) => format!("app ind {}", name),
                _ => crate::types::STUCK_TYPE_REASON.to_string(),
            }
        }
        Term::Pi(_, _, _, _) => "pi".to_string(),
        Term::Rec(name, _) => format!("rec {}", name),
        Term::Ctor(name, _, _) => format!("ctor {}", name),
        _ => "unsupported".to_string(),
    }
}

fn ref_kind_for_borrow_wrapper(marker: BorrowWrapperMarker) -> Option<BorrowKind> {
    match marker {
        BorrowWrapperMarker::RefShared => Some(BorrowKind::Shared),
        BorrowWrapperMarker::RefMut => Some(BorrowKind::Mut),
        BorrowWrapperMarker::RefCell | BorrowWrapperMarker::Mutex | BorrowWrapperMarker::Atomic => {
            None
        }
    }
}

fn interior_mutability_for_borrow_wrapper(marker: BorrowWrapperMarker) -> Option<IMKind> {
    match marker {
        BorrowWrapperMarker::RefCell => Some(IMKind::RefCell),
        BorrowWrapperMarker::Mutex => Some(IMKind::Mutex),
        BorrowWrapperMarker::Atomic => Some(IMKind::Atomic),
        BorrowWrapperMarker::RefShared | BorrowWrapperMarker::RefMut => None,
    }
}

fn mir_type_contains_opaque(ty: &MirType) -> bool {
    match ty {
        MirType::Opaque { .. } => true,
        MirType::Adt(_, args) => args.iter().any(mir_type_contains_opaque),
        MirType::Ref(_, inner, _) => mir_type_contains_opaque(inner),
        MirType::Fn(_, _, args, ret)
        | MirType::FnItem(_, _, _, args, ret)
        | MirType::Closure(_, _, _, args, ret) => {
            args.iter().any(mir_type_contains_opaque) || mir_type_contains_opaque(ret)
        }
        MirType::RawPtr(inner, _) => mir_type_contains_opaque(inner),
        MirType::InteriorMutable(inner, _) => mir_type_contains_opaque(inner),
        _ => false,
    }
}

fn instantiate_params(mut ty: Rc<Term>, params: &[Rc<Term>]) -> Rc<Term> {
    for param in params {
        if let Term::Pi(_, body, _, _) = &*ty {
            ty = body.subst(0, param);
        } else {
            break;
        }
    }
    ty
}

/// Binder domains of a (parameter-instantiated) constructor type, and its result type.
/// All binders are returned, implicit ones included: they are fields of the runtime value
/// (`ctor_field_templates` in types.rs keeps them) and the kernel's minor premises bind
/// them, so skipping them would misalign field positions and minor arguments.
fn peel_pi_binders(ty: &Rc<Term>) -> (Vec<Rc<Term>>, Rc<Term>) {
    let mut binders = Vec::new();
    let mut current = ty.clone();
    while let Term::Pi(dom, body, _, _) = &*current {
        binders.push(dom.clone());
        current = body.clone();
    }
    (binders, current)
}

fn extract_inductive_args(term: &Rc<Term>, ind_name: &str) -> Option<Vec<Rc<Term>>> {
    fn go(t: &Rc<Term>, acc: &mut Vec<Rc<Term>>) -> Option<String> {
        match &**t {
            Term::App(f, a, _) => {
                acc.push(a.clone());
                go(f, acc)
            }
            Term::Ind(name, _) => Some(name.clone()),
            _ => None,
        }
    }

    let mut rev_args = Vec::new();
    let head = go(term, &mut rev_args)?;
    if head != ind_name {
        return None;
    }
    rev_args.reverse();
    Some(rev_args)
}

fn extract_inductive_indices(
    term: &Rc<Term>,
    ind_name: &str,
    num_params: usize,
) -> Option<Vec<Rc<Term>>> {
    let args = extract_inductive_args(term, ind_name)?;
    if args.len() < num_params {
        return None;
    }
    Some(args[num_params..].to_vec())
}

fn is_recursive_head(t: &Rc<Term>, name: &str) -> bool {
    match &**t {
        Term::Ind(n, _) => n == name,
        Term::App(f, _, _) => is_recursive_head(f, name),
        Term::Pi(_, _, _, _) => false,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::nll::NllChecker;
    use crate::types::{IMKind, IdRegistry, MirType, Mutability};
    use kernel::ast::{
        marker_def_id, marker_name, AxiomTag, BinderInfo, BorrowWrapperMarker, Definition,
        FunctionKind, InductiveDecl, TypeMarker,
    };
    use kernel::checker::Env;

    fn env_with_ref_primitives() -> Env {
        let mut env = Env::new();
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);

        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        env.add_definition(Definition::axiom("Shared".to_string(), sort1.clone()))
            .expect("Failed to add Shared");
        env.add_definition(Definition::axiom("Mut".to_string(), sort1.clone()))
            .expect("Failed to add Mut");
        let ref_ty = Rc::new(Term::Pi(
            sort1.clone(),
            Rc::new(Term::Pi(
                sort1.clone(),
                sort1.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        env.add_definition(Definition::axiom("Ref".to_string(), ref_ty))
            .expect("Failed to add Ref");

        env.set_allow_reserved_primitives(allow_reserved);
        env
    }

    fn add_marker_definitions(env: &mut Env) {
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let markers = [
            TypeMarker::InteriorMutable,
            TypeMarker::MayPanicOnBorrowViolation,
            TypeMarker::ConcurrencyPrimitive,
            TypeMarker::AtomicPrimitive,
            TypeMarker::Indexable,
        ];

        for marker in markers {
            let name = marker_name(marker).to_string();
            let def = Definition::axiom_with_tags(name, sort1.clone(), vec![AxiomTag::Unsafe]);
            env.add_definition(def)
                .expect("Failed to add marker definition");
        }

        env.init_marker_registry()
            .expect("Failed to init marker registry");
        env.set_allow_reserved_primitives(allow_reserved);
    }

    fn add_refcell_inductive(env: &mut Env) {
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let refcell_ty = Rc::new(Term::Pi(
            sort1.clone(),
            sort1.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let mut decl = InductiveDecl::new("RefCell".to_string(), refcell_ty, vec![]);
        decl.markers = vec![
            marker_def_id(TypeMarker::InteriorMutable),
            marker_def_id(TypeMarker::MayPanicOnBorrowViolation),
        ];
        env.add_inductive(decl)
            .expect("Failed to add RefCell inductive");
    }

    #[test]
    fn test_marker_registry_uninitialized_reports_lowering_error() {
        let mut env = Env::new();
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let refcell_ty = Rc::new(Term::Pi(
            sort1.clone(),
            sort1,
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let mut decl = InductiveDecl::new("RefCell".to_string(), refcell_ty, vec![]);
        decl.markers = vec![
            marker_def_id(TypeMarker::InteriorMutable),
            marker_def_id(TypeMarker::MayPanicOnBorrowViolation),
        ];
        // Inject directly to keep the marker registry intentionally uninitialized.
        env.inductives.insert("RefCell".to_string(), decl);

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = Term::app(
            Rc::new(Term::Ind("RefCell".to_string(), vec![])),
            Rc::new(Term::Sort(Level::Zero)),
        );
        let err = match LoweringContext::new(vec![("c".to_string(), arg_ty)], ret_ty, &env, &ids) {
            Ok(_) => panic!("missing marker registry should fail context initialization"),
            Err(err) => err,
        };
        assert!(
            err.to_string().contains("Marker registry error"),
            "expected marker registry lowering diagnostic, got: {}",
            err
        );
    }

    #[test]
    fn test_context_init_unknown_type_reports_diagnostic() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = Rc::new(Term::Const("MissingType".to_string(), vec![]));

        let err = match LoweringContext::new(vec![("x".to_string(), arg_ty)], ret_ty, &env, &ids) {
            Ok(_) => panic!("unknown constant type should fail context initialization"),
            Err(err) => err,
        };
        let message = err.to_string();
        assert!(
            message.contains("Failed to determine Prop-like status during MIR lowering")
                || message.contains("Failed to normalize type during MIR lowering"),
            "expected lowering diagnostic, got: {}",
            err
        );
        assert!(
            message.contains("Unknown Const"),
            "expected unknown constant cause in diagnostic, got: {}",
            err
        );
    }

    #[test]
    fn test_malformed_borrow_application_reports_lowering_error() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        // Not `Prop`: a destination of type `Prop` holds an erased proposition and is not lowered.
        let ret_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let malformed = Term::app(
            Rc::new(Term::Const("borrow_shared".to_string(), vec![])),
            Rc::new(Term::Const("not_a_var".to_string(), vec![])),
        );

        let expected_span = SourceSpan {
            start: 10,
            end: 24,
            line: 1,
            col: 11,
        };
        let term_id = 1;
        let term_key = Rc::as_ptr(&malformed) as usize;
        let mut spans_by_term_id = HashMap::new();
        spans_by_term_id.insert(term_id, expected_span);
        let mut term_ids_by_ptr = HashMap::new();
        term_ids_by_ptr.insert(term_key, term_id);
        let span_map = Rc::new(TermSpanMap::new(spans_by_term_id, term_ids_by_ptr));

        let mut ctx = LoweringContext::new_with_spans(vec![], ret_ty, &env, &ids, Some(span_map))
            .expect("context init should succeed");
        let target = ctx.new_block();

        let err = ctx
            .lower_term(&malformed, Place::from(Local(0)), target)
            .expect_err("malformed borrow application should return a lowering error");

        assert!(
            err.to_string().contains("Borrow expects a variable place"),
            "expected malformed borrow diagnostic, got: {}",
            err
        );
        assert_eq!(
            err.span(),
            Some(expected_span),
            "malformed borrow diagnostic should carry source span"
        );
    }

    #[test]
    fn test_capturing_closure_missing_capture_metadata_fails_closed() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        // Not `Prop`: a destination of type `Prop` holds an erased proposition and is not lowered.
        let ret_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let captured_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let term = Rc::new(Term::Lam(
            captured_ty.clone(),
            Rc::new(Term::Var(1)),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        ));

        let mut ctx = LoweringContext::new_with_metadata(
            vec![("captured".to_string(), captured_ty.clone())],
            ret_ty,
            &env,
            &ids,
            None,
            Some("metadata_test".to_string()),
            Some(Rc::new(DefCaptureModeMap::new())),
        )
        .expect("context init should succeed");
        let target = ctx.new_block();

        let err = ctx
            .lower_term(&term, Place::from(Local(0)), target)
            .expect_err("capturing closure without capture metadata must fail closed");
        assert!(
            err.to_string().contains("Missing closure capture metadata"),
            "expected dedicated capture-metadata diagnostic, got: {}",
            err
        );
    }

    #[test]
    fn test_capturing_closure_missing_span_metadata_fails_closed() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        // Not `Prop`: a destination of type `Prop` holds an erased proposition and is not lowered.
        let ret_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let captured_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let term = Rc::new(Term::Lam(
            captured_ty.clone(),
            Rc::new(Term::Var(1)),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        ));

        let closure_ids = kernel::ownership::collect_closure_ids(&term, "metadata_span_test");
        let closure_id = closure_ids
            .values()
            .next()
            .copied()
            .expect("closure id should exist");
        let mut capture_modes = DefCaptureModeMap::new();
        let mut modes = CaptureModes::new();
        modes.insert(0usize, UsageMode::Consuming);
        capture_modes.insert(closure_id, modes);

        let empty_span_map = Rc::new(TermSpanMap::new(HashMap::new(), HashMap::new()));
        let mut ctx = LoweringContext::new_with_metadata(
            vec![("captured".to_string(), captured_ty.clone())],
            ret_ty,
            &env,
            &ids,
            Some(empty_span_map),
            Some("metadata_span_test".to_string()),
            Some(Rc::new(capture_modes)),
        )
        .expect("context init should succeed");
        let target = ctx.new_block();

        let err = ctx
            .lower_term(&term, Place::from(Local(0)), target)
            .expect_err("capturing closure without span metadata must fail closed");
        assert!(
            err.to_string().contains("Missing closure span metadata"),
            "expected dedicated span-metadata diagnostic, got: {}",
            err
        );
    }

    #[test]
    fn test_lower_app() {
        let arg_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let f = Rc::new(Term::Lam(
            arg_ty.clone(),
            Rc::new(Term::Var(0)),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let a = Rc::new(Term::Sort(Level::Zero));
        let term = Term::app(f, a);

        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let mut ctx =
            LoweringContext::new(vec![], ret_ty, &env, &ids).expect("context init should succeed");
        let dest = Place::from(Local(0));
        let target = ctx.new_block();

        ctx.lower_term(&term, dest, target).unwrap();

        let body = ctx.finish();

        println!("{:?}", body);
        assert!(body.basic_blocks.len() > 1);
    }

    #[test]
    fn test_polymorphic_lambda_closure_locals_keep_param_types() {
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let term = Rc::new(Term::Lam(
            sort1,
            Rc::new(Term::Lam(
                Rc::new(Term::Var(0)),
                Rc::new(Term::Var(0)),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));

        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        // Not `Prop`: a destination of type `Prop` holds an erased proposition and is not lowered.
        let ret_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let mut ctx =
            LoweringContext::new(vec![], ret_ty, &env, &ids).expect("context init should succeed");
        let target = ctx.new_block();

        ctx.lower_term(&term, Place::from(Local(0)), target)
            .expect("lowering polymorphic lambda should succeed");

        let derived = ctx.derived_bodies.borrow();
        let has_param_typed_closure = derived.iter().any(|body| {
            body.local_decls.len() >= 3
                && body.local_decls[0].ty == MirType::Param(0)
                && body.local_decls[2].ty == MirType::Param(0)
        });
        assert!(
            has_param_typed_closure,
            "expected closure body locals to preserve Param(0) for polymorphic lambda, got {:?}",
            *derived
        );
    }

    #[test]
    fn test_erased_args_marked_copy() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let arg_ty = Rc::new(Term::Sort(Level::Zero));
        let ret_ty = arg_ty.clone();
        let ctx = LoweringContext::new(vec![("x".to_string(), arg_ty)], ret_ty, &env, &ids)
            .expect("context init should succeed");

        assert!(
            ctx.body.local_decls[0].is_copy,
            "return local should be Copy for erased types"
        );
        assert!(
            ctx.body.local_decls[1].is_copy,
            "argument local should be Copy for erased types"
        );
    }

    #[test]
    fn test_temp_local_erased_is_copy() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let mut ctx =
            LoweringContext::new(vec![], ret_ty, &env, &ids).expect("context init should succeed");
        let ty = Rc::new(Term::Sort(Level::Zero));
        let temp = ctx
            .push_temp_local(ty, None)
            .expect("temp local creation should succeed");

        assert!(
            ctx.body.local_decls[temp.index()].is_copy,
            "temp local should be Copy for erased types"
        );
    }

    #[test]
    fn test_opaque_prop_alias_marks_is_prop() {
        let mut env = Env::new();
        let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let prop = Rc::new(Term::Sort(Level::Zero));

        let mut prop_alias = Definition::total("MyProp".to_string(), type0, prop);
        prop_alias.mark_opaque();
        env.add_definition(prop_alias)
            .expect("Failed to add opaque MyProp");

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = Rc::new(Term::Const("MyProp".to_string(), vec![]));
        let ctx = LoweringContext::new(vec![("p".to_string(), arg_ty)], ret_ty, &env, &ids)
            .expect("context init should succeed");

        let arg_decl = &ctx.body.local_decls[1];
        assert!(
            arg_decl.is_prop,
            "opaque Prop alias should be marked Prop for erasure"
        );
    }

    #[test]
    fn test_alias_ref_mut_lowers_to_ref_and_not_copy() {
        let mut env = env_with_ref_primitives();
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let const_term = |name: &str| Rc::new(Term::Const(name.to_string(), vec![]));
        env.add_definition(Definition::axiom("A".to_string(), sort1.clone()))
            .expect("Failed to add A");
        let my_ref_val = Term::app(
            Term::app(const_term("Ref"), const_term("Mut")),
            const_term("A"),
        );
        let mut my_ref_def = Definition::total("MyRef".to_string(), sort1, my_ref_val);
        my_ref_def.noncomputable = true;
        env.add_definition(my_ref_def).expect("Failed to add MyRef");

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = const_term("MyRef");
        let ctx = LoweringContext::new(vec![("r".to_string(), arg_ty)], ret_ty, &env, &ids)
            .expect("context init should succeed");

        let arg_decl = &ctx.body.local_decls[1];
        assert!(
            matches!(arg_decl.ty, MirType::Ref(_, _, Mutability::Mut)),
            "alias to Ref Mut should lower to MirType::Ref Mut, got {:?}",
            arg_decl.ty
        );
        assert!(!arg_decl.is_copy, "alias to Ref Mut should not be Copy");
    }

    #[test]
    fn test_opaque_alias_ref_mut_defaults_to_opaque_and_not_copy() {
        let mut env = env_with_ref_primitives();
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let const_term = |name: &str| Rc::new(Term::Const(name.to_string(), vec![]));
        env.add_definition(Definition::axiom("A".to_string(), sort1.clone()))
            .expect("Failed to add A");
        let my_ref_val = Term::app(
            Term::app(const_term("Ref"), const_term("Mut")),
            const_term("A"),
        );
        let mut my_ref_def = Definition::total("MyOpaqueRef".to_string(), sort1, my_ref_val);
        my_ref_def.noncomputable = true;
        my_ref_def.mark_opaque();
        env.add_definition(my_ref_def)
            .expect("Failed to add MyOpaqueRef");

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = const_term("MyOpaqueRef");
        let ctx = LoweringContext::new(vec![("r".to_string(), arg_ty)], ret_ty, &env, &ids)
            .expect("context init should succeed");

        let arg_decl = &ctx.body.local_decls[1];
        assert!(
            matches!(arg_decl.ty, MirType::Opaque { .. }),
            "opaque alias without marker should lower to MirType::Opaque, got {:?}",
            arg_decl.ty
        );
        assert!(!arg_decl.is_copy, "opaque alias should not be Copy");
    }

    #[test]
    fn test_marked_opaque_alias_ref_mut_lowers_to_ref_and_not_copy() {
        let mut env = env_with_ref_primitives();
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let const_term = |name: &str| Rc::new(Term::Const(name.to_string(), vec![]));
        env.add_definition(Definition::axiom("A".to_string(), sort1.clone()))
            .expect("Failed to add A");
        let my_ref_val = Term::app(
            Term::app(const_term("Ref"), const_term("Mut")),
            const_term("A"),
        );
        let mut my_ref_def = Definition::total("MyMarkedOpaqueRef".to_string(), sort1, my_ref_val);
        my_ref_def.noncomputable = true;
        my_ref_def.mark_opaque();
        my_ref_def.mark_borrow_wrapper(BorrowWrapperMarker::RefMut);
        env.add_definition(my_ref_def)
            .expect("Failed to add MyMarkedOpaqueRef");

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = const_term("MyMarkedOpaqueRef");
        let ctx = LoweringContext::new(vec![("r".to_string(), arg_ty)], ret_ty, &env, &ids)
            .expect("context init should succeed");

        let arg_decl = &ctx.body.local_decls[1];
        assert!(
            matches!(arg_decl.ty, MirType::Ref(_, _, Mutability::Mut)),
            "marked opaque alias to Ref Mut should lower to MirType::Ref Mut, got {:?}",
            arg_decl.ty
        );
        assert!(
            !arg_decl.is_copy,
            "marked opaque alias to Ref Mut should not be Copy"
        );
    }

    #[test]
    fn test_opaque_alias_refcell_defaults_to_opaque_without_runtime_checks() {
        let mut env = Env::new();
        add_marker_definitions(&mut env);
        add_refcell_inductive(&mut env);

        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        env.add_definition(Definition::axiom("A".to_string(), sort1.clone()))
            .expect("Failed to add A");

        let refcell_app = Term::app(
            Rc::new(Term::Ind("RefCell".to_string(), vec![])),
            Rc::new(Term::Const("A".to_string(), vec![])),
        );
        let mut my_cell_def = Definition::total("MyCell".to_string(), sort1, refcell_app);
        my_cell_def.noncomputable = true;
        my_cell_def.mark_opaque();
        env.add_definition(my_cell_def)
            .expect("Failed to add MyCell");

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = Rc::new(Term::Const("MyCell".to_string(), vec![]));
        let mut ctx = LoweringContext::new(vec![("c".to_string(), arg_ty)], ret_ty, &env, &ids)
            .expect("context init should succeed");

        let arg_decl = &ctx.body.local_decls[1];
        assert!(
            matches!(arg_decl.ty, MirType::Opaque { .. }),
            "opaque alias without marker should lower to MirType::Opaque, got {:?}",
            arg_decl.ty
        );

        ctx.body.basic_blocks[0].statements.push(Statement::Assign(
            Place::from(Local(0)),
            Rvalue::Use(Operand::Move(Place::from(Local(1)))),
        ));
        ctx.body.basic_blocks[0].terminator = Some(Terminator::Return);

        let mut checker = NllChecker::new(&ctx.body);
        checker.check();
        let result = checker.into_result();
        assert!(
            !result
                .runtime_checks
                .iter()
                .any(|check| matches!(check.kind, RuntimeCheckKind::RefCellBorrow { .. })),
            "opaque alias without marker should not trigger runtime checks"
        );
    }

    #[test]
    fn test_marked_opaque_alias_refcell_lowers_to_interior_mutability_and_runtime_checks() {
        let mut env = Env::new();
        add_marker_definitions(&mut env);
        add_refcell_inductive(&mut env);

        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        env.add_definition(Definition::axiom("A".to_string(), sort1.clone()))
            .expect("Failed to add A");

        let refcell_app = Term::app(
            Rc::new(Term::Ind("RefCell".to_string(), vec![])),
            Rc::new(Term::Const("A".to_string(), vec![])),
        );
        let mut my_cell_def = Definition::total("MyMarkedCell".to_string(), sort1, refcell_app);
        my_cell_def.noncomputable = true;
        my_cell_def.mark_opaque();
        my_cell_def.mark_borrow_wrapper(BorrowWrapperMarker::RefCell);
        env.add_definition(my_cell_def)
            .expect("Failed to add MyMarkedCell");

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = Rc::new(Term::Const("MyMarkedCell".to_string(), vec![]));
        let mut ctx = LoweringContext::new(vec![("c".to_string(), arg_ty)], ret_ty, &env, &ids)
            .expect("context init should succeed");

        let arg_decl = &ctx.body.local_decls[1];
        assert!(
            matches!(arg_decl.ty, MirType::InteriorMutable(_, IMKind::RefCell)),
            "marked opaque alias to RefCell should lower to InteriorMutable RefCell, got {:?}",
            arg_decl.ty
        );

        ctx.body.basic_blocks[0].statements.push(Statement::Assign(
            Place::from(Local(0)),
            Rvalue::Use(Operand::Move(Place::from(Local(1)))),
        ));
        ctx.body.basic_blocks[0].terminator = Some(Terminator::Return);

        let mut checker = NllChecker::new(&ctx.body);
        checker.check();
        let result = checker.into_result();
        assert!(
            result
                .runtime_checks
                .iter()
                .any(|check| matches!(check.kind, RuntimeCheckKind::RefCellBorrow { .. })),
            "marked opaque alias to RefCell should still trigger runtime checks"
        );
    }

    #[test]
    fn test_opaque_type_lowers_to_opaque_and_not_copy() {
        let mut env = Env::new();
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        env.add_definition(Definition::axiom("OpaqueTy".to_string(), sort1.clone()))
            .expect("Failed to add OpaqueTy");

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let arg_ty = Rc::new(Term::Const("OpaqueTy".to_string(), vec![]));
        let ctx = LoweringContext::new(vec![("x".to_string(), arg_ty)], ret_ty, &env, &ids)
            .expect("context init should succeed");

        let arg_decl = &ctx.body.local_decls[1];
        assert!(
            matches!(arg_decl.ty, MirType::Opaque { .. }),
            "opaque type should lower to MirType::Opaque, got {:?}",
            arg_decl.ty
        );
        assert!(!arg_decl.is_copy, "opaque type should not be Copy");
    }

    #[test]
    fn test_const_function_lowers_to_fn_item_copy() {
        let mut env = Env::new();
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let fn_ty = Rc::new(Term::Pi(
            sort1.clone(),
            sort1.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        env.add_definition(Definition::axiom("f".to_string(), fn_ty))
            .expect("Failed to add f");

        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let mut ctx =
            LoweringContext::new(vec![], ret_ty, &env, &ids).expect("context init should succeed");
        let f_term = Rc::new(Term::Const("f".to_string(), vec![]));
        let f_local = ctx.lower_term_to_local(&f_term).unwrap();
        let f_decl = &ctx.body.local_decls[f_local.index()];

        assert!(
            matches!(f_decl.ty, MirType::FnItem(_, _, _, _, _)),
            "const function should lower to MirType::FnItem, got {:?}",
            f_decl.ty
        );
        assert!(f_decl.is_copy, "const function item should be Copy");
    }

    #[test]
    fn test_lambda_lowers_to_closure_copy_when_env_copy() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let mut ctx =
            LoweringContext::new(vec![], ret_ty, &env, &ids).expect("context init should succeed");
        let arg_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let lam = Rc::new(Term::Lam(
            arg_ty,
            Rc::new(Term::Var(0)),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let lam_local = ctx.lower_term_to_local(&lam).unwrap();
        let lam_decl = &ctx.body.local_decls[lam_local.index()];

        assert!(
            matches!(lam_decl.ty, MirType::Closure(_, _, _, _, _)),
            "lambda should lower to MirType::Closure, got {:?}",
            lam_decl.ty
        );
        assert!(
            lam_decl.is_copy,
            "closure with Copy environment should be Copy"
        );
    }

    // ---------------------------------------------------------------------------------
    // Recursor lowering: alternatives for non-recursive inductives, Copy minor closures
    // ---------------------------------------------------------------------------------

    fn sort1() -> Rc<Term> {
        Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))))
    }

    fn fn_pi(dom: Rc<Term>, cod: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Pi(dom, cod, BinderInfo::Default, FunctionKind::Fn))
    }

    fn konst(name: &str) -> Rc<Term> {
        Rc::new(Term::Const(name.to_string(), vec![]))
    }

    fn ind(name: &str) -> Rc<Term> {
        Rc::new(Term::Ind(name.to_string(), vec![]))
    }

    /// `Tok` is an opaque, non-Copy resource type and `close`, `finish : Tok -> R` consume
    /// it. `B` (two field-less constructors) and `Opt` (`none`, `some : R -> Opt`) are
    /// non-recursive; `L` (`lnil`, `lcons : L -> L`) is recursive.
    fn env_for_rec_lowering() -> Env {
        let mut env = Env::new();
        env.add_definition(Definition::axiom("Tok".to_string(), sort1()))
            .expect("Tok");
        env.add_definition(Definition::axiom("R".to_string(), sort1()))
            .expect("R");
        let consume_ty = fn_pi(konst("Tok"), konst("R"));
        env.add_definition(Definition::axiom("close".to_string(), consume_ty.clone()))
            .expect("close");
        env.add_definition(Definition::axiom("finish".to_string(), consume_ty))
            .expect("finish");
        let ctor = |name: &str, ty: Rc<Term>| kernel::ast::Constructor {
            name: name.to_string(),
            ty,
        };
        env.add_inductive(InductiveDecl::new(
            "B".to_string(),
            sort1(),
            vec![ctor("bt", ind("B")), ctor("bf", ind("B"))],
        ))
        .expect("B");
        env.add_inductive(InductiveDecl::new(
            "Opt".to_string(),
            sort1(),
            vec![
                ctor("none", ind("Opt")),
                ctor("some", fn_pi(konst("R"), ind("Opt"))),
            ],
        ))
        .expect("Opt");
        env.add_inductive(InductiveDecl::new(
            "L".to_string(),
            sort1(),
            vec![
                ctor("lnil", ind("L")),
                ctor("lcons", fn_pi(ind("L"), ind("L"))),
            ],
        ))
        .expect("L");
        env
    }

    /// `(rec I) (λ _:I. R) minors... major`, non-dependent motive into `R`.
    fn rec_app(ind_name: &str, minors: Vec<Rc<Term>>, major: Rc<Term>) -> Rc<Term> {
        let rec = Rc::new(Term::Rec(
            ind_name.to_string(),
            vec![Level::Succ(Box::new(Level::Zero))],
        ));
        let motive = Rc::new(Term::Lam(
            ind(ind_name),
            konst("R"),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let mut term = Term::app(rec, motive);
        for minor in minors {
            term = Term::app(term, minor);
        }
        Term::app(term, major)
    }

    /// Lowers `term : R` in the context `c : Tok, x : major_ty` and returns the ownership
    /// errors of the resulting body together with the body and its derived closure bodies.
    fn lower_with_token(
        env: &Env,
        major_ty: Rc<Term>,
        term: &Rc<Term>,
    ) -> (Vec<String>, Body, usize) {
        let ids = IdRegistry::from_env(env);
        let mut ctx = LoweringContext::new(
            vec![("c".to_string(), konst("Tok")), ("x".to_string(), major_ty)],
            konst("R"),
            env,
            &ids,
        )
        .expect("context init should succeed");
        let target = ctx.new_block();
        ctx.lower_term(term, Place::from(Local(0)), target)
            .expect("lowering should succeed");
        ctx.set_block(target);
        ctx.terminate(Terminator::Return);
        let closures = ctx.derived_bodies.borrow().len();
        let mut body = ctx.finish();
        crate::transform::storage::insert_exit_storage_deads(&mut body);
        let mut ownership = crate::analysis::ownership::OwnershipAnalysis::new(&body);
        ownership.analyze();
        let errors = ownership
            .check_structured()
            .iter()
            .map(|e| e.to_string())
            .collect();
        (errors, body, closures)
    }

    fn count_unreachable(body: &Body) -> usize {
        body.basic_blocks
            .iter()
            .filter(|bb| matches!(bb.terminator, Some(Terminator::Unreachable)))
            .count()
    }

    /// R4: the minors of a non-recursive inductive are alternatives. `c` is consumed by both
    /// field-less minors (`close c` / `finish c`); each is lowered in its own arm, so `c` is
    /// moved once on every path. (Before, both minors were evaluated before the switch:
    /// a use of a moved value.)
    #[test]
    fn test_rec_non_recursive_minors_consume_same_value_in_each_arm() {
        let env = env_for_rec_lowering();
        // Context: c = Var(1), x = Var(0).
        let close_c = Term::app(konst("close"), Rc::new(Term::Var(1)));
        let finish_c = Term::app(konst("finish"), Rc::new(Term::Var(1)));
        let term = rec_app("B", vec![close_c, finish_c], Rc::new(Term::Var(0)));
        let (errors, body, closures) = lower_with_token(&env, ind("B"), &term);
        assert!(
            errors.is_empty(),
            "expected no ownership errors, got {:?}",
            errors
        );
        assert_eq!(closures, 0, "no minor closure should be created");
        let moves_of_c = body
            .basic_blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .filter(|stmt| {
                matches!(stmt, Statement::Assign(_, Rvalue::Use(Operand::Move(place)))
                    if place.local == Local(1) && place.projection.is_empty())
            })
            .count();
        assert_eq!(
            moves_of_c, 2,
            "c must be moved once in each of the two arms"
        );
    }

    /// R4: a minor that is a λ binding exactly the constructor's fields is inlined (no
    /// closure); the field is moved out of the scrutinee into a local, and the captured
    /// token may still be consumed in both arms.
    #[test]
    fn test_rec_non_recursive_lambda_minor_is_inlined() {
        let env = env_for_rec_lowering();
        let close_c = Term::app(konst("close"), Rc::new(Term::Var(1)));
        // λ r:R. finish c   (under the binder, c = Var(2))
        let some_minor = Rc::new(Term::Lam(
            konst("R"),
            Term::app(konst("finish"), Rc::new(Term::Var(2))),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        ));
        let term = rec_app("Opt", vec![close_c, some_minor], Rc::new(Term::Var(0)));
        let (errors, body, closures) = lower_with_token(&env, ind("Opt"), &term);
        assert!(
            errors.is_empty(),
            "expected no ownership errors, got {:?}",
            errors
        );
        assert_eq!(
            closures, 0,
            "the λ minor must be inlined, not built as a closure"
        );
        let field_reads = body
            .basic_blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .filter(|stmt| {
                matches!(stmt, Statement::Assign(_, Rvalue::Use(Operand::Move(place)))
                    if place.projection == vec![PlaceElem::Downcast(1), PlaceElem::Field(0)])
            })
            .count();
        assert_eq!(field_reads, 1, "the `some` field must be bound in its arm");
    }

    /// The recursive lowering is unchanged: for `L` the minors are still built as closures
    /// before the switch, so consuming `c` in two minors is rejected (the cons minor is
    /// called once per element; only the kernel/MIR rules for repeated minors apply).
    #[test]
    fn test_rec_recursive_minors_still_built_before_switch() {
        let env = env_for_rec_lowering();
        let close_c = Term::app(konst("close"), Rc::new(Term::Var(1)));
        // λ t:L. λ ih:R. finish c   (c = Var(3))
        let cons_minor = Rc::new(Term::Lam(
            ind("L"),
            Rc::new(Term::Lam(
                konst("R"),
                Term::app(konst("finish"), Rc::new(Term::Var(3))),
                BinderInfo::Default,
                FunctionKind::FnOnce,
            )),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        ));
        let term = rec_app("L", vec![close_c, cons_minor], Rc::new(Term::Var(0)));
        let (errors, _body, closures) = lower_with_token(&env, ind("L"), &term);
        assert!(closures >= 1, "recursive minors must still be closures");
        assert!(
            errors.iter().any(|e| e.contains("moved")),
            "expected a use-after-move error for the recursive lowering, got {:?}",
            errors
        );
    }

    /// `env_for_rec_lowering` plus `TL` (`tnil | tcons (h : Tok) (t : TL)`, non-Copy because
    /// `Tok` is opaque) and `use_tl : TL -> R`.
    fn env_with_token_list() -> Env {
        let mut env = env_for_rec_lowering();
        let ctor = |name: &str, ty: Rc<Term>| kernel::ast::Constructor {
            name: name.to_string(),
            ty,
        };
        env.add_inductive(InductiveDecl::new(
            "TL".to_string(),
            sort1(),
            vec![
                ctor("tnil", ind("TL")),
                ctor("tcons", fn_pi(konst("Tok"), fn_pi(ind("TL"), ind("TL")))),
            ],
        ))
        .expect("TL");
        env.add_definition(Definition::axiom(
            "use_tl".to_string(),
            fn_pi(ind("TL"), konst("R")),
        ))
        .expect("use_tl");
        env
    }

    /// `λ h:Tok. λ t:TL. λ ih:R. body` (in `body`: h = Var(2), t = Var(1), ih = Var(0)).
    fn tcons_minor(body: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Lam(
            konst("Tok"),
            Rc::new(Term::Lam(
                ind("TL"),
                Rc::new(Term::Lam(
                    konst("R"),
                    body,
                    BinderInfo::Default,
                    FunctionKind::FnOnce,
                )),
                BinderInfo::Default,
                FunctionKind::FnOnce,
            )),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        ))
    }

    fn moves_of_projection(body: &Body, projection: &[PlaceElem]) -> usize {
        body.basic_blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .filter(|stmt| {
                matches!(stmt, Statement::Assign(_, Rvalue::Use(Operand::Move(place)))
                    if place.projection == projection)
            })
            .count()
    }

    /// A non-Copy recursive field is consumed by the computation of its induction hypothesis.
    /// When the minor premise does not use the field at run time, its arm is not unpacked in
    /// MIR (which would move the field twice): the major premise goes to the recursor's entry
    /// function, and the ownership check passes.
    #[test]
    fn test_rec_arm_with_unused_non_copy_recursive_field_dispatches_to_entry() {
        let env = env_with_token_list();
        // tnil: close c (c = Var(1)); tcons: λ h t ih. finish h
        let close_c = Term::app(konst("close"), Rc::new(Term::Var(1)));
        let cons_minor = tcons_minor(Term::app(konst("finish"), Rc::new(Term::Var(2))));
        let term = rec_app("TL", vec![close_c, cons_minor], Rc::new(Term::Var(0)));
        let (errors, body, _closures) = lower_with_token(&env, ind("TL"), &term);
        assert!(
            errors.is_empty(),
            "expected no ownership errors, got {:?}",
            errors
        );
        assert_eq!(
            moves_of_projection(&body, &[PlaceElem::Downcast(1), PlaceElem::Field(1)]),
            0,
            "the tcons arm must not unpack the recursive field"
        );
        let entry_calls = body
            .basic_blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .filter(|stmt| {
                matches!(stmt, Statement::Assign(_, Rvalue::Use(Operand::Constant(c)))
                    if matches!(c.literal, Literal::Recursor(ref name) if name == "TL"))
            })
            .count();
        assert_eq!(
            entry_calls, 1,
            "the tcons arm must call the recursor entry once"
        );
    }

    /// A minor premise that uses a non-Copy recursive field at run time is still unpacked, and
    /// MIR reports the double move itself (the field goes to the induction hypothesis and to
    /// the minor premise).
    #[test]
    fn test_rec_arm_using_non_copy_recursive_field_is_still_rejected() {
        let env = env_with_token_list();
        let close_c = Term::app(konst("close"), Rc::new(Term::Var(1)));
        let cons_minor = tcons_minor(Term::app(konst("use_tl"), Rc::new(Term::Var(1))));
        let term = rec_app("TL", vec![close_c, cons_minor], Rc::new(Term::Var(0)));
        let (errors, body, _closures) = lower_with_token(&env, ind("TL"), &term);
        assert_eq!(
            moves_of_projection(&body, &[PlaceElem::Downcast(1), PlaceElem::Field(1)]),
            1,
            "the tcons arm must unpack the recursive field"
        );
        assert!(
            errors.iter().any(|e| e.contains("moved")),
            "expected a use-after-move error, got {:?}",
            errors
        );
    }

    /// A recursive-case minor premise that consumes a captured value is not Copy: it is not
    /// handed to the recursor's entry function (which would call it once per recursive
    /// occurrence, out of MIR's sight), so MIR still sees, and rejects, the repeated use
    /// (the kernel rejects the program first, `ConsumedInRepeatedScope`).
    #[test]
    fn test_rec_arm_with_consuming_minor_is_not_dispatched() {
        let mut env = env_with_token_list();
        env.add_definition(Definition::axiom("r0".to_string(), konst("R")))
            .expect("r0");
        // tnil: r0; tcons: λ h t ih. finish c (c = Var(4) under the three binders)
        let cons_minor = tcons_minor(Term::app(konst("finish"), Rc::new(Term::Var(4))));
        let term = rec_app("TL", vec![konst("r0"), cons_minor], Rc::new(Term::Var(0)));
        let (errors, body, _closures) = lower_with_token(&env, ind("TL"), &term);
        assert_eq!(
            moves_of_projection(&body, &[PlaceElem::Downcast(1), PlaceElem::Field(1)]),
            1,
            "the tcons arm of a consuming minor must be unpacked"
        );
        assert!(
            errors.iter().any(|e| e.contains("moved")),
            "expected a use-after-move error, got {:?}",
            errors
        );
    }

    /// A local written by the arms of an inline `match` is Copy only if every closure written
    /// into it is: here one arm stores a closure that consumes the captured token `c` and the
    /// other a capture-free closure, and the local `g` is called twice. MIR must reject the
    /// second call (the kernel rejects the program first, `UseAfterMove` of `g`; before, the
    /// capture-free arm made the local Copy and MIR accepted it, stage-matrix probe g5).
    #[test]
    fn test_local_written_by_consuming_and_capture_free_closures_is_not_copy() {
        let mut env = env_for_rec_lowering();
        env.add_definition(Definition::axiom(
            "combine".to_string(),
            fn_pi(konst("R"), fn_pi(konst("R"), konst("R"))),
        ))
        .expect("combine");
        env.add_definition(Definition::axiom("r0".to_string(), konst("R")))
            .expect("r0");
        let once_pi = |dom: Rc<Term>, cod: Rc<Term>| {
            Rc::new(Term::Pi(
                dom,
                cod,
                BinderInfo::Default,
                FunctionKind::FnOnce,
            ))
        };
        let once_lam = |dom: Rc<Term>, body: Rc<Term>| {
            Rc::new(Term::Lam(
                dom,
                body,
                BinderInfo::Default,
                FunctionKind::FnOnce,
            ))
        };
        let g_ty = once_pi(konst("R"), konst("R"));
        // Context: c = Var(1), x = Var(0). Under the arm's binder k: k = Var(0), c = Var(2).
        let consuming = once_lam(
            konst("R"),
            Term::app(
                Term::app(konst("combine"), Rc::new(Term::Var(0))),
                Term::app(konst("close"), Rc::new(Term::Var(2))),
            ),
        );
        let capture_free = once_lam(konst("R"), Rc::new(Term::Var(0)));
        let motive = Rc::new(Term::Lam(
            ind("B"),
            g_ty.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let rec = Rc::new(Term::Rec(
            "B".to_string(),
            vec![Level::Succ(Box::new(Level::Zero))],
        ));
        // Both orders: the consuming closure written first, or second (then the local was
        // already made Copy by the capture-free one and must be downgraded).
        for (first, second) in [
            (consuming.clone(), capture_free.clone()),
            (capture_free, consuming),
        ] {
            let pick = Term::app(
                Term::app(
                    Term::app(Term::app(rec.clone(), motive.clone()), first),
                    second,
                ),
                Rc::new(Term::Var(0)),
            );
            // let g = pick in combine (g r0) (g r0)
            let call_g = Term::app(Rc::new(Term::Var(0)), konst("r0"));
            let body = Term::app(Term::app(konst("combine"), call_g.clone()), call_g);
            let term = Rc::new(Term::LetE(g_ty.clone(), pick, body));
            let (errors, _body, _closures) = lower_with_token(&env, ind("B"), &term);
            assert!(
                errors.iter().any(|e| e.contains("moved")),
                "expected a use-after-move error for the second call of g, got {:?}",
                errors
            );
        }
    }

    /// Arms whose constructor indices clash with the scrutinee's indices are unreachable:
    /// `Rec_Fin` on `Fin (succ zero)` cannot take a branch typed at `Fin zero`.
    #[test]
    fn test_rec_arm_with_clashing_index_is_unreachable() {
        let mut env = env_for_rec_lowering();
        let ctor = |name: &str, ty: Rc<Term>| kernel::ast::Constructor {
            name: name.to_string(),
            ty,
        };
        // inductive N : Type | nz | ns (n : N); inductive F : N -> Type | f0 : F nz | f1 : F (ns nz)
        env.add_inductive(InductiveDecl::new(
            "N".to_string(),
            sort1(),
            vec![ctor("nz", ind("N")), ctor("ns", fn_pi(ind("N"), ind("N")))],
        ))
        .expect("N");
        let nz = Rc::new(Term::Ctor("N".to_string(), 0, vec![]));
        let ns_nz = Term::app(Rc::new(Term::Ctor("N".to_string(), 1, vec![])), nz.clone());
        env.add_inductive(InductiveDecl::new(
            "F".to_string(),
            fn_pi(ind("N"), sort1()),
            vec![
                ctor("f0", Term::app(ind("F"), nz.clone())),
                ctor("f1", Term::app(ind("F"), ns_nz.clone())),
            ],
        ))
        .expect("F");
        let rec = Rc::new(Term::Rec(
            "F".to_string(),
            vec![Level::Succ(Box::new(Level::Zero))],
        ));
        // motive λ k:N. λ _:F k. R
        let motive = Rc::new(Term::Lam(
            ind("N"),
            Rc::new(Term::Lam(
                Term::app(ind("F"), Rc::new(Term::Var(0))),
                konst("R"),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let close_c = Term::app(konst("close"), Rc::new(Term::Var(1)));
        let finish_c = Term::app(konst("finish"), Rc::new(Term::Var(1)));
        let mut term = Term::app(rec, motive);
        term = Term::app(term, close_c);
        term = Term::app(term, finish_c);
        term = Term::app(term, ns_nz.clone());
        term = Term::app(term, Rc::new(Term::Var(0)));
        let (errors, body, _) = lower_with_token(&env, Term::app(ind("F"), ns_nz), &term);
        assert!(
            errors.is_empty(),
            "expected no ownership errors, got {:?}",
            errors
        );
        assert_eq!(
            count_unreachable(&body),
            1,
            "the f0 arm (index nz vs ns nz) must be unreachable"
        );
    }

    /// R3: a closure is Copy only when every capture is Copy or a shared reference. A minor
    /// premise of a recursive constructor keeps an Fn-called (read-only) function capture
    /// as a shared borrow, which makes it Copy; captures by move or by mutable borrow
    /// keep it non-Copy.
    #[test]
    fn test_minor_closure_copy_rule_for_function_captures() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let nat_like = sort1();
        let f_ty = fn_pi(nat_like.clone(), nat_like.clone());
        let plan_for = |mode: UsageMode, borrow_fn_values: bool| {
            let mut ctx = LoweringContext::new(
                vec![("f".to_string(), f_ty.clone())],
                Rc::new(Term::Sort(Level::Zero)),
                &env,
                &ids,
            )
            .expect("context init should succeed");
            let captured: HashSet<usize> = [0usize].into_iter().collect();
            let mut modes = CaptureModes::new();
            modes.insert(0usize, mode);
            ctx.collect_captures(
                FunctionKind::FnOnce,
                &captured,
                Some(&modes),
                Some(&modes),
                borrow_fn_values,
                &HashSet::new(),
            )
            .expect("capture plan")
        };

        let read = plan_for(UsageMode::Observational, true);
        assert_eq!(
            read.is_copy,
            vec![true],
            "read-only fn capture is a shared borrow"
        );
        assert_eq!(read.borrowed, vec![true]);
        assert!(matches!(
            read.mir_types[0],
            MirType::Ref(_, _, Mutability::Not)
        ));

        let moved = plan_for(UsageMode::Consuming, true);
        assert_eq!(
            moved.is_copy,
            vec![false],
            "a moved capture keeps the closure non-Copy"
        );

        let mutated = plan_for(UsageMode::MutBorrow, true);
        assert_eq!(
            mutated.is_copy,
            vec![false],
            "a mutably used capture keeps the closure non-Copy"
        );

        // Outside a recursive minor, function values are still moved into the environment.
        let ordinary = plan_for(UsageMode::Observational, false);
        assert_eq!(ordinary.is_copy, vec![false]);
        assert_eq!(ordinary.borrowed, vec![false]);
    }

    #[test]
    fn test_call_operand_respects_fn_kind() {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
        let mut ctx =
            LoweringContext::new(vec![], ret_ty, &env, &ids).expect("context init should succeed");

        let fn_ty = MirType::Fn(
            FunctionKind::Fn,
            Vec::new(),
            vec![MirType::Unit],
            Box::new(MirType::Unit),
        );
        let fn_mut_ty = MirType::Fn(
            FunctionKind::FnMut,
            Vec::new(),
            vec![MirType::Unit],
            Box::new(MirType::Unit),
        );
        let fn_once_ty = MirType::Fn(
            FunctionKind::FnOnce,
            Vec::new(),
            vec![MirType::Unit],
            Box::new(MirType::Unit),
        );

        let fn_local = ctx.push_mir_local(fn_ty.clone(), None);
        let fn_mut_local = ctx.push_mir_local(fn_mut_ty.clone(), None);
        let fn_once_local = ctx.push_mir_local(fn_once_ty.clone(), None);

        match ctx.call_operand_for_func(fn_local, &fn_ty) {
            CallOperand::Borrow(BorrowKind::Shared, _) => {}
            other => panic!("Fn should be shared borrow, got {:?}", other),
        }

        match ctx.call_operand_for_func(fn_mut_local, &fn_mut_ty) {
            CallOperand::Borrow(BorrowKind::Mut, _) => {}
            other => panic!("FnMut should be mut borrow, got {:?}", other),
        }

        match ctx.call_operand_for_func(fn_once_local, &fn_once_ty) {
            CallOperand::Operand(Operand::Move(_)) => {}
            other => panic!("FnOnce should be Move, got {:?}", other),
        }
    }
}
