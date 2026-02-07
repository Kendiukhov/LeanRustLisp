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

#[derive(Debug, Clone, Default)]
pub struct TermSpanMap {
    spans_by_term_id: HashMap<StableTermId, SourceSpan>,
    term_ids_by_ptr: HashMap<usize, StableTermId>,
}

impl TermSpanMap {
    pub fn new(
        spans_by_term_id: HashMap<StableTermId, SourceSpan>,
        term_ids_by_ptr: HashMap<usize, StableTermId>,
    ) -> Self {
        Self {
            spans_by_term_id,
            term_ids_by_ptr,
        }
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
            MirType::IndexTerm(term) => MirType::IndexTerm(term.clone()),
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

        let mut kept_args = Vec::new();
        for (idx, arg) in args.iter().enumerate() {
            if idx < param_count {
                kept_args.push(self.lower_type_general_with_scope(arg, scope)?);
            } else {
                kept_args.push(MirType::IndexTerm(arg.clone()));
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

        let mut kept_args = Vec::new();
        for (idx, arg) in args.iter().enumerate() {
            if idx < param_count {
                kept_args.push(self.lower_type_in_fn_with_scope(arg, assigner, position, scope)?);
            } else {
                kept_args.push(MirType::IndexTerm(arg.clone()));
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

            if matches!(capture_mode, UsageMode::Observational)
                && matches!(kind, FunctionKind::FnOnce)
                && !local_is_copy
            {
                capture_mode = UsageMode::Consuming;
            }
            if !local_is_copy
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
                plan.borrowed.push(false);
            } else {
                match capture_mode {
                    UsageMode::Observational => {
                        let region = self.fresh_region();
                        let ref_ty = MirType::Ref(region, Box::new(local_mir_ty), Mutability::Not);
                        let ref_local = self.push_mir_local(ref_ty.clone(), None);
                        self.push_statement(Statement::StorageLive(ref_local));
                        self.push_statement(Statement::Assign(
                            Place::from(ref_local),
                            Rvalue::Ref(BorrowKind::Shared, Place::from(*local)),
                        ));
                        plan.operands.push(Operand::Copy(Place::from(ref_local)));
                        plan.mir_types.push(ref_ty);
                        plan.is_copy.push(true);
                        plan.borrowed.push(true);
                    }
                    UsageMode::MutBorrow => {
                        let region = self.fresh_region();
                        let ref_ty = MirType::Ref(region, Box::new(local_mir_ty), Mutability::Mut);
                        let ref_local = self.push_mir_local(ref_ty.clone(), None);
                        self.push_statement(Statement::StorageLive(ref_local));
                        self.push_statement(Statement::Assign(
                            Place::from(ref_local),
                            Rvalue::Ref(BorrowKind::Mut, Place::from(*local)),
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
                        plan.borrowed.push(false);
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

    fn required_capture_modes_for_closure(
        &self,
        arg_ty: &Rc<Term>,
        body: &Rc<Term>,
    ) -> LoweringResult<Option<CaptureModes>> {
        let ctx = self.checker_ctx.push(arg_ty.clone());
        self.collect_required_capture_modes_in_term(body, &ctx, 1, UsageMode::Consuming)
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
        let is_copy = self.compute_is_copy_for_mir(&ty, &mir_ty);

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
        let is_copy = self.compute_is_copy_for_mir(&ty, &mir_ty);

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
        let is_copy = self.compute_is_copy_for_mir(&ty, &mir_ty);
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
                let arg_ty = ty.clone();
                let mut free_vars = HashSet::new();
                collect_free_vars(body, 1, &mut free_vars);
                let required_modes = self.required_capture_modes_for_closure(ty, body)?;
                let capture_modes = self.capture_modes_for_required_closure(term, &free_vars)?;
                self.ensure_capture_modes_complete(term, &free_vars, capture_modes.as_ref())?;
                let capture_plan = self.collect_captures(
                    *kind,
                    &free_vars,
                    capture_modes.as_ref(),
                    required_modes.as_ref(),
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
                    next_region: 1,
                };

                if destination.projection.is_empty() {
                    let decl = &mut self.body.local_decls[destination.local.index()];
                    decl.closure_captures.clone_from(&capture_plan.mir_types);
                    if capture_plan.is_copy.iter().all(|is_copy| *is_copy) {
                        // Closures with copyable captures can be duplicated by cloning.
                        // This keeps recursive recursor minor-premise closures reusable.
                        decl.is_copy = true;
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
                sub_ctx.lower_term(body, Place::from(Local(0)), return_block)?;
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
                let constant = Constant {
                    literal: Literal::InductiveCtor(ctor_id, arity),
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
                    next_region: 1,
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
                if !capture_plan.mir_types.is_empty() {
                    let mut env_types = Vec::with_capacity(capture_plan.mir_types.len() + 1);
                    env_types.push(self.lower_type(ty)?);
                    env_types.extend(capture_plan.mir_types.clone());
                    sub_ctx.body.local_decls[env_local.index()].closure_captures = env_types;
                }
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

                let shifted_body = body.shift(0, 1);
                let body_app = Term::app(shifted_body, Rc::new(Term::Var(0)));
                sub_ctx.lower_term(&body_app, Place::from(Local(0)), return_block)?;
                sub_ctx.set_block(return_block);
                sub_ctx.terminate_with_term_span(&body_app, Terminator::Return);

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
            let mut partial_term: Rc<Term> =
                Rc::new(Term::Rec(ind_name.to_string(), levels.to_vec()));
            for arg in args.iter() {
                partial_term = Term::app(partial_term, arg.clone());
            }
            let constant = self.constant_for_term(partial_term)?;
            self.push_statement(Statement::Assign(
                destination,
                Rvalue::Use(Operand::Constant(Box::new(constant))),
            ));
            self.terminate(Terminator::Goto { target });
            return Ok(());
        }

        let major_premise = &args[args.len() - 1];

        let params = &args[..n_params];
        let motive_term = &args[n_params];
        let minors_start = n_params + n_motives;
        let minor_terms = &args[minors_start..minors_start + n_minors];
        let indices_start = minors_start + n_minors;
        let index_terms = &args[indices_start..indices_start + n_indices];

        let mut param_locals = Vec::new();
        for param in params {
            param_locals.push(self.lower_term_to_local(param)?);
        }
        let motive_local = self.lower_term_to_local(motive_term)?;
        let mut minor_locals = Vec::new();
        for minor in minor_terms {
            minor_locals.push(self.lower_term_to_local(minor)?);
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

        let major_ty = self.infer_term_type(major_premise)?;
        let temp_major = self.push_temp_local(major_ty, None)?;
        self.push_statement(Statement::StorageLive(temp_major));
        let major_block = self.new_block();
        self.lower_term(major_premise, Place::from(temp_major), major_block)?;
        self.set_block(major_block);

        let discr_temp = self.push_mir_local(MirType::Nat, None);
        self.push_statement(Statement::StorageLive(discr_temp));
        self.push_statement(Statement::Assign(
            Place::from(discr_temp),
            Rvalue::Discriminant(Place::from(temp_major)),
        ));
        shared_locals.push(discr_temp);
        shared_locals.push(temp_major);

        let mut target_blocks = Vec::new();
        let mut values = Vec::new();

        for (ctor_idx, _) in decl.ctors.iter().enumerate() {
            let arm_block = self.new_block();
            target_blocks.push(arm_block);
            values.push(ctor_idx as u128);
        }

        self.terminate(Terminator::SwitchInt {
            discr: Operand::Move(Place::from(discr_temp)),
            targets: SwitchTargets {
                values,
                targets: target_blocks.clone(),
            },
        });

        let base_ctx = self.checker_ctx.clone();

        for (i, arm_block) in target_blocks.iter().enumerate() {
            self.set_block(*arm_block);
            let ctor = &decl.ctors[i];

            let mut args_for_minor = Vec::new();
            self.checker_ctx = base_ctx.clone();

            let minor_local = minor_locals[i];
            let ctor_inst = instantiate_params(ctor.ty.clone(), params);
            let field_types = peel_pi_binders(&ctor_inst).0;
            let mut field_locals = Vec::new();
            let mut arm_locals = Vec::new();

            for (field_pos, field_ty) in field_types.iter().enumerate() {
                let field_place = Place {
                    local: temp_major,
                    projection: vec![PlaceElem::Downcast(i), PlaceElem::Field(field_pos)],
                };
                let field_local = self.push_temp_local(field_ty.clone(), None)?;
                self.push_statement(Statement::StorageLive(field_local));
                let field_is_copy = self.body.local_decls[field_local.index()].is_copy;
                let field_operand = if field_is_copy {
                    Operand::Copy(field_place)
                } else {
                    Operand::Move(field_place)
                };
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

                    let rec_term = Rc::new(Term::Rec(ind_name.to_string(), levels.to_vec()));
                    let rec_ty = compute_recursor_type(decl, levels);
                    let mut rec_args: Vec<Rc<Term>> = params.to_vec();
                    rec_args.push(motive_term.clone());
                    rec_args.extend(minor_terms.iter().cloned());
                    let rec_index_terms = rec_index_terms_final.as_deref().unwrap_or(index_terms);
                    rec_args.extend(rec_index_terms.iter().cloned());
                    let rec_local = if let Some(spec_ty) =
                        self.specialize_pi_type_with_args_and_last(rec_ty, &rec_args)?
                    {
                        // Build the recursor value with the specialized MIR type so the
                        // assignment and local declaration stay in sync for MIR typing.
                        let local = self.push_mir_local(spec_ty.clone(), None);
                        self.push_statement(Statement::StorageLive(local));
                        let mut constant = self.constant_for_term(rec_term.clone())?;
                        constant.ty = spec_ty;
                        self.push_statement(Statement::Assign(
                            Place::from(local),
                            Rvalue::Use(Operand::Constant(Box::new(constant))),
                        ));
                        local
                    } else {
                        self.lower_term_to_local(&rec_term)?
                    };
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

        Ok(())
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
                _ => "app".to_string(),
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
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
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
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
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
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
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
        let ret_ty = Rc::new(Term::Sort(Level::Zero));
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
