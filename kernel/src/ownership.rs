use crate::ast::{BinderInfo, DefId, Term};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;
use thiserror::Error;

/// A variable named in an ownership error.
///
/// `index` is the de Bruijn index of the variable at the point of the error. `binder` is the
/// address of the term that binds it (a `Lam`, `LetE` or `Fix` node of the checked value, or a
/// lambda of a minor premise); it is diagnostic metadata only (never printed) and lets a front
/// end that recorded source names for its binder terms fill in `name`
/// (see [`OwnershipError::resolve_names`]).
#[derive(Clone, PartialEq, Eq)]
pub struct VarRef {
    pub index: usize,
    pub binder: Option<usize>,
    pub name: Option<String>,
}

impl VarRef {
    pub fn new(index: usize, binder: Option<usize>) -> Self {
        VarRef {
            index,
            binder,
            name: None,
        }
    }
}

impl fmt::Display for VarRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.name {
            Some(name) => write!(f, "'{}'", name),
            None => write!(f, "#{} (de Bruijn index)", self.index),
        }
    }
}

impl fmt::Debug for VarRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.name {
            Some(name) => write!(f, "{}", name),
            None => write!(f, "#{}", self.index),
        }
    }
}

#[derive(Error, Debug)]
pub enum OwnershipError {
    /// A non-Copy variable is used (moved, read, mutably borrowed or called) after it was moved.
    #[error("variable {0} is used after it was moved")]
    UseAfterMove(VarRef),
    #[error("implicit binder {var} of non-Copy type is used in {mode} position")]
    ImplicitNonCopyUse { var: VarRef, mode: UsageMode },
    /// A non-Copy variable bound outside a minor premise (or a fixpoint body) that may run more
    /// than once is consumed inside it: every run would consume the same value again.
    #[error(
        "non-Copy variable {0} is consumed inside a minor premise or fixpoint body that may run more than once"
    )]
    ConsumedInRepeatedScope(VarRef),
    /// A recursive constructor field of non-Copy type is used inside its minor premise. The
    /// recursor already consumed it to compute the induction hypothesis.
    #[error(
        "recursive field {0} is not Copy and was consumed to compute its induction hypothesis; use the induction hypothesis instead"
    )]
    RecursiveFieldConsumedByIh(VarRef),
    /// The minor premise of a constructor that may be eliminated more than once is not a
    /// lambda abstraction, so the kernel cannot check that running it repeatedly is safe.
    #[error(
        "minor premise for constructor '{ctor}' may run more than once and must be written as a lambda abstraction"
    )]
    RepeatedMinorNotLambda { ctor: String },
    /// The minor premise of a field-less constructor that may be eliminated more than once is a
    /// value that the recursor returns for every occurrence of the constructor; it must be Copy.
    #[error(
        "minor premise for constructor '{ctor}' is returned for every occurrence of the constructor, but its type is not Copy"
    )]
    RepeatedMinorValueNotCopy { ctor: String },
    /// A minor premise does not bind a recursive field of non-Copy type as a lambda parameter,
    /// so the kernel cannot check that it is not used besides its induction hypothesis.
    #[error(
        "minor premise for constructor '{ctor}' must bind its recursive fields (of non-Copy type) as lambda parameters"
    )]
    MinorMustBindRecursiveField { ctor: String },
    /// A recursor used as a runtime value without all of its minor premises: the missing minor
    /// premises would be supplied later, out of sight of the recursor rule.
    #[error(
        "recursor for '{ind}' must be applied to its motive and all of its minor premises where it occurs"
    )]
    RecursorWithoutMinorPremises { ind: String },
}

impl OwnershipError {
    /// Name of the error variant (stable; used in diagnostics and tests).
    pub fn variant_name(&self) -> &'static str {
        match self {
            OwnershipError::UseAfterMove(_) => "UseAfterMove",
            OwnershipError::ImplicitNonCopyUse { .. } => "ImplicitNonCopyUse",
            OwnershipError::ConsumedInRepeatedScope(_) => "ConsumedInRepeatedScope",
            OwnershipError::RecursiveFieldConsumedByIh(_) => "RecursiveFieldConsumedByIh",
            OwnershipError::RepeatedMinorNotLambda { .. } => "RepeatedMinorNotLambda",
            OwnershipError::RepeatedMinorValueNotCopy { .. } => "RepeatedMinorValueNotCopy",
            OwnershipError::MinorMustBindRecursiveField { .. } => "MinorMustBindRecursiveField",
            OwnershipError::RecursorWithoutMinorPremises { .. } => "RecursorWithoutMinorPremises",
        }
    }

    /// The variable the error is about, if any.
    pub fn var(&self) -> Option<&VarRef> {
        match self {
            OwnershipError::UseAfterMove(var)
            | OwnershipError::ConsumedInRepeatedScope(var)
            | OwnershipError::RecursiveFieldConsumedByIh(var)
            | OwnershipError::ImplicitNonCopyUse { var, .. } => Some(var),
            _ => None,
        }
    }

    /// Fills in the source name of the variable from its binder term address, using a name
    /// table recorded by the front end (binder term address -> source name).
    pub fn resolve_names(&mut self, names: &HashMap<usize, String>) {
        let var = match self {
            OwnershipError::UseAfterMove(var)
            | OwnershipError::ConsumedInRepeatedScope(var)
            | OwnershipError::RecursiveFieldConsumedByIh(var)
            | OwnershipError::ImplicitNonCopyUse { var, .. } => var,
            _ => return,
        };
        if var.name.is_none() {
            if let Some(binder) = var.binder {
                var.name = names.get(&binder).cloned();
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UsageMode {
    Consuming,
    MutBorrow,
    Observational,
}

pub type ClosureId = DefId;
pub type CaptureModes = HashMap<usize, UsageMode>;
pub type DefCaptureModeMap = HashMap<ClosureId, CaptureModes>;

pub fn collect_closure_ids(term: &Rc<Term>, def_name: &str) -> HashMap<usize, ClosureId> {
    let mut map = HashMap::new();
    let mut counter: u64 = 0;

    fn term_key(term: &Rc<Term>) -> usize {
        Rc::as_ptr(term) as usize
    }

    fn walk(
        term: &Rc<Term>,
        def_name: &str,
        counter: &mut u64,
        map: &mut HashMap<usize, ClosureId>,
    ) {
        match &**term {
            Term::Lam(ty, body, _, _) => {
                let id = DefId::new(format!("{}::closure#{}", def_name, *counter));
                *counter += 1;
                map.insert(term_key(term), id);
                walk(ty, def_name, counter, map);
                walk(body, def_name, counter, map);
            }
            Term::Fix(ty, body) => {
                let id = DefId::new(format!("{}::closure#{}", def_name, *counter));
                *counter += 1;
                map.insert(term_key(term), id);
                walk(ty, def_name, counter, map);
                walk(body, def_name, counter, map);
            }
            Term::App(f, a, _) => {
                walk(f, def_name, counter, map);
                walk(a, def_name, counter, map);
            }
            Term::Pi(ty, body, _, _) => {
                walk(ty, def_name, counter, map);
                walk(body, def_name, counter, map);
            }
            Term::LetE(ty, val, body) => {
                walk(ty, def_name, counter, map);
                walk(val, def_name, counter, map);
                walk(body, def_name, counter, map);
            }
            Term::Sort(_)
            | Term::Const(_, _)
            | Term::Ind(_, _)
            | Term::Ctor(_, _, _)
            | Term::Rec(_, _)
            | Term::Var(_)
            | Term::Meta(_) => {}
        }
    }

    walk(term, def_name, &mut counter, &mut map);
    map
}

pub fn map_capture_modes_to_closures(
    closure_ids: &HashMap<usize, ClosureId>,
    pointer_modes: &HashMap<usize, CaptureModes>,
) -> DefCaptureModeMap {
    let mut mapped = HashMap::new();
    for (term_key, modes) in pointer_modes {
        if let Some(closure_id) = closure_ids.get(term_key) {
            mapped.insert(*closure_id, modes.clone());
        }
    }
    mapped
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

pub fn collect_closure_free_vars(term: &Rc<Term>) -> HashMap<usize, HashSet<usize>> {
    let mut free_vars_by_ptr = HashMap::new();

    fn term_key(term: &Rc<Term>) -> usize {
        Rc::as_ptr(term) as usize
    }

    fn walk(term: &Rc<Term>, free_vars_by_ptr: &mut HashMap<usize, HashSet<usize>>) {
        match &**term {
            Term::Lam(ty, body, _, _) | Term::Fix(ty, body) => {
                let mut free_vars = HashSet::new();
                collect_free_vars(body, 1, &mut free_vars);
                free_vars_by_ptr.insert(term_key(term), free_vars);
                walk(ty, free_vars_by_ptr);
                walk(body, free_vars_by_ptr);
            }
            Term::App(f, a, _) => {
                walk(f, free_vars_by_ptr);
                walk(a, free_vars_by_ptr);
            }
            Term::Pi(ty, body, _, _) => {
                walk(ty, free_vars_by_ptr);
                walk(body, free_vars_by_ptr);
            }
            Term::LetE(ty, val, body) => {
                walk(ty, free_vars_by_ptr);
                walk(val, free_vars_by_ptr);
                walk(body, free_vars_by_ptr);
            }
            Term::Sort(_)
            | Term::Const(_, _)
            | Term::Ind(_, _)
            | Term::Ctor(_, _, _)
            | Term::Rec(_, _)
            | Term::Var(_)
            | Term::Meta(_) => {}
        }
    }

    walk(term, &mut free_vars_by_ptr);
    free_vars_by_ptr
}

pub fn map_capture_modes_to_closures_filtered(
    closure_ids: &HashMap<usize, ClosureId>,
    closure_free_vars: &HashMap<usize, HashSet<usize>>,
    pointer_modes: &HashMap<usize, CaptureModes>,
) -> DefCaptureModeMap {
    let mut mapped: DefCaptureModeMap = closure_ids
        .values()
        .copied()
        .map(|closure_id| (closure_id, CaptureModes::new()))
        .collect();
    for (term_key, modes) in pointer_modes {
        let Some(closure_id) = closure_ids.get(term_key) else {
            continue;
        };
        let Some(free_vars) = closure_free_vars.get(term_key) else {
            continue;
        };
        let filtered_modes: CaptureModes = modes
            .iter()
            .filter_map(|(idx, mode)| {
                if free_vars.contains(idx) {
                    Some((*idx, *mode))
                } else {
                    None
                }
            })
            .collect();
        mapped.insert(*closure_id, filtered_modes);
    }
    mapped
}

impl fmt::Display for UsageMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            UsageMode::Consuming => "consuming",
            UsageMode::MutBorrow => "mutable borrow",
            UsageMode::Observational => "observational",
        };
        write!(f, "{}", label)
    }
}

/// Usage state of the variables in scope (a stack, innermost binder last).
///
/// Usage modes of a *runtime* occurrence of a variable: [`UsageContext::read_var`] is a read
/// (call of an `Fn` function value, capture by an `Fn` closure, `borrow_shared`); `MutBorrow` is a
/// mutable use (call of an `FnMut` value, capture by an `FnMut` closure, `borrow_mut`);
/// `Consuming` is a move. Reads, mutable uses and moves of a non-Copy variable that was already
/// moved are errors, and a move marks the variable as moved. Erased occurrences (types, proofs,
/// motives, indices, parameters) are not recorded at all; `Observational` passed to
/// [`UsageContext::use_var`] means such an erased occurrence and never fails.
///
/// A *repetition barrier* marks the start of a scope that may be executed more than once (a minor
/// premise of a recursor that can be invoked several times, or a fixpoint body): non-Copy
/// variables bound outside the innermost barrier may not be moved inside it.
pub struct UsageContext {
    used: Vec<VarUsage>,
    barriers: Vec<usize>,
}

/// The moved flags of every variable in scope (outermost first), see
/// [`UsageContext::moved_state`].
pub type MovedState = Vec<bool>;

impl Default for UsageContext {
    fn default() -> Self {
        Self::new()
    }
}

impl UsageContext {
    pub fn new() -> Self {
        UsageContext {
            used: Vec::new(),
            barriers: Vec::new(),
        }
    }

    pub fn push(&mut self, is_copy: bool) {
        self.push_binder(is_copy, BinderInfo::Default, None);
    }

    pub fn push_with_binder(&mut self, is_copy: bool, info: BinderInfo) {
        self.push_binder(is_copy, info, None);
    }

    /// Pushes a variable; `binder` is the address of the binding term (for diagnostics).
    pub fn push_binder(&mut self, is_copy: bool, info: BinderInfo, binder: Option<usize>) {
        let implicit = matches!(info, BinderInfo::Implicit | BinderInfo::StrictImplicit);
        self.used.push(VarUsage {
            used: false,
            is_copy,
            implicit,
            consumed_by_ih: false,
            binder,
        });
    }

    /// Pushes a recursive constructor field bound by a minor premise. A non-Copy recursive field
    /// starts out moved: the recursor consumed it to compute the induction hypothesis.
    pub fn push_recursive_field(&mut self, is_copy: bool, info: BinderInfo, binder: Option<usize>) {
        self.push_binder(is_copy, info, binder);
        if !is_copy {
            if let Some(var) = self.used.last_mut() {
                var.used = true;
                var.consumed_by_ih = true;
            }
        }
    }

    pub fn pop(&mut self) {
        self.used.pop();
    }

    /// Number of variables in scope.
    pub fn depth(&self) -> usize {
        self.used.len()
    }

    /// Starts a scope that may run more than once (see the type documentation).
    pub fn push_barrier(&mut self) {
        self.barriers.push(self.used.len());
    }

    pub fn pop_barrier(&mut self) {
        self.barriers.pop();
    }

    /// Snapshot of the moved flags of the variables in scope.
    pub fn moved_state(&self) -> MovedState {
        self.used.iter().map(|var| var.used).collect()
    }

    /// Restores a snapshot taken by [`UsageContext::moved_state`] at the same depth.
    pub fn restore_moved_state(&mut self, state: &[bool]) {
        for (var, moved) in self.used.iter_mut().zip(state) {
            var.used = *moved;
        }
    }

    /// Joins two moved states of the same depth: a variable is moved if it is moved in either
    /// (used for alternative branches, only one of which runs).
    pub fn join_moved_states(into: &mut MovedState, other: &[bool]) {
        for (moved, other_moved) in into.iter_mut().zip(other) {
            *moved = *moved || *other_moved;
        }
    }

    fn var_ref(&self, idx: usize) -> VarRef {
        let binder = self
            .used
            .len()
            .checked_sub(1 + idx)
            .and_then(|stack_idx| self.used[stack_idx].binder);
        VarRef::new(idx, binder)
    }

    fn moved_error(&self, var: &VarUsage, idx: usize) -> OwnershipError {
        if var.consumed_by_ih {
            OwnershipError::RecursiveFieldConsumedByIh(self.var_ref(idx))
        } else {
            OwnershipError::UseAfterMove(self.var_ref(idx))
        }
    }

    /// A runtime read of a variable (not a move): fails if the variable is non-Copy and was
    /// already moved.
    pub fn read_var(&mut self, idx: usize) -> Result<(), OwnershipError> {
        if idx >= self.used.len() {
            return Ok(());
        }
        let stack_idx = self.used.len() - 1 - idx;
        let var = self.used[stack_idx];
        if !var.is_copy && var.used {
            return Err(self.moved_error(&var, idx));
        }
        Ok(())
    }

    pub fn is_implicit_non_copy(&self, idx: usize) -> bool {
        if idx >= self.used.len() {
            return false;
        }
        let stack_idx = self.used.len() - 1 - idx;
        let var = &self.used[stack_idx];
        var.implicit && !var.is_copy
    }

    /// Records an occurrence of variable `idx` in `mode`: `Consuming` is a move, `MutBorrow` a
    /// mutable use, `Observational` an erased occurrence (always succeeds; use
    /// [`UsageContext::read_var`] for a runtime read).
    pub fn use_var(&mut self, idx: usize, mode: UsageMode) -> Result<(), OwnershipError> {
        if idx >= self.used.len() {
            return Ok(());
        }
        let stack_idx = self.used.len() - 1 - idx;
        let innermost_barrier = self.barriers.last().copied().unwrap_or(0);

        let var = self.used[stack_idx];
        if var.implicit
            && (mode == UsageMode::Consuming || mode == UsageMode::MutBorrow)
            && !var.is_copy
        {
            return Err(OwnershipError::ImplicitNonCopyUse {
                var: self.var_ref(idx),
                mode,
            });
        }
        if mode == UsageMode::Observational || var.is_copy {
            return Ok(());
        }

        if var.used {
            return Err(self.moved_error(&var, idx));
        }

        if mode == UsageMode::Consuming {
            if stack_idx < innermost_barrier {
                return Err(OwnershipError::ConsumedInRepeatedScope(self.var_ref(idx)));
            }
            self.used[stack_idx].used = true;
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct VarUsage {
    used: bool,
    is_copy: bool,
    implicit: bool,
    /// Set for a non-Copy recursive field bound by a minor premise (moved by the recursor).
    consumed_by_ih: bool,
    /// Address of the binding term (diagnostics only).
    binder: Option<usize>,
}

pub fn check_ownership(
    term: &Rc<Term>,
    ctx: &mut UsageContext,
    mode: UsageMode,
) -> Result<(), OwnershipError> {
    match &**term {
        Term::Var(i) => ctx.use_var(*i, mode),
        Term::App(f, a, _) => {
            check_ownership(f, ctx, mode)?;
            check_ownership(a, ctx, mode)?;
            Ok(())
        }
        Term::Lam(ty, body, info, _) => {
            // body is evaluated with x: ty
            // ty is evaluated in current context
            check_ownership(ty, ctx, UsageMode::Observational)?; // Assuming original signature for ty
            ctx.push_with_binder(false, *info); // Untyped check assumes affine
            let res = check_ownership(body, ctx, mode); // Original call
            ctx.pop(); // Original pop
            res
        }
        Term::Pi(ty, body, info, _) => {
            // Depedent types usually don't consume resources linearly in type position,
            // but the body is a type that might depend on x
            check_ownership(ty, ctx, UsageMode::Observational)?; // Assuming original signature for ty
            ctx.push_with_binder(false, *info); // Untyped check assumes affine
            let res = check_ownership(body, ctx, UsageMode::Observational); // Original call
            ctx.pop(); // Original pop
            res
        }
        Term::LetE(ty, val, body) => {
            check_ownership(ty, ctx, UsageMode::Observational)?;
            check_ownership(val, ctx, mode)?;
            ctx.push(false);
            let res = check_ownership(body, ctx, mode);
            ctx.pop();
            res
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinderInfo, Level};

    #[test]
    fn test_affine_use_once() {
        let mut ctx = UsageContext::new();
        // (lam x. x)
        let t = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);
        assert!(check_ownership(&t, &mut ctx, UsageMode::Consuming).is_ok());
    }

    #[test]
    fn test_affine_use_twice_fail() {
        let mut ctx = UsageContext::new();
        // (lam x. (f x x))
        let t = Term::lam(
            Term::sort(Level::Zero),
            Term::app(Term::app(Term::var(1), Term::var(0)), Term::var(0)),
            BinderInfo::Default,
        );
        let res = check_ownership(&t, &mut ctx, UsageMode::Consuming);
        assert!(matches!(res, Err(OwnershipError::UseAfterMove(ref var)) if var.index == 0));
    }

    #[test]
    fn test_alternative_moved_states_are_joined() {
        let mut ctx = UsageContext::new();
        ctx.push(false); // a (index 1)
        ctx.push(false); // b (index 0)
        let before = ctx.moved_state();
        let mut joined = before.clone();
        // branch 1 moves a
        ctx.use_var(1, UsageMode::Consuming).unwrap();
        UsageContext::join_moved_states(&mut joined, &ctx.moved_state());
        // branch 2 starts from the same state and moves a and b
        ctx.restore_moved_state(&before);
        ctx.use_var(1, UsageMode::Consuming).unwrap();
        ctx.use_var(0, UsageMode::Consuming).unwrap();
        UsageContext::join_moved_states(&mut joined, &ctx.moved_state());
        ctx.restore_moved_state(&joined);
        assert!(matches!(
            ctx.read_var(0),
            Err(OwnershipError::UseAfterMove(ref var)) if var.index == 0
        ));
        assert!(ctx.read_var(1).is_err());
    }

    #[test]
    fn test_ownership_error_names_resolve_from_binder_addresses() {
        let mut ctx = UsageContext::new();
        ctx.push_binder(false, BinderInfo::Default, Some(0x1000));
        ctx.use_var(0, UsageMode::Consuming).unwrap();
        let mut err = ctx.use_var(0, UsageMode::Consuming).unwrap_err();
        assert_eq!(err.variant_name(), "UseAfterMove");
        assert_eq!(
            err.to_string(),
            "variable #0 (de Bruijn index) is used after it was moved"
        );
        let names: HashMap<usize, String> =
            [(0x1000usize, "tok".to_string())].into_iter().collect();
        err.resolve_names(&names);
        assert_eq!(err.to_string(), "variable 'tok' is used after it was moved");
        assert_eq!(format!("{:?}", err), "UseAfterMove(tok)");
    }

    #[test]
    fn test_observe_in_type() {
        let mut ctx = UsageContext::new();
        // (lam x. (pi y: x . x))
        let t = Term::lam(
            Term::sort(Level::Zero),
            Term::pi(
                Term::var(0), // Type uses x (Obs)
                Term::var(1), // Body uses x (Obs)
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        assert!(check_ownership(&t, &mut ctx, UsageMode::Consuming).is_ok());
    }

    #[test]
    fn test_map_capture_modes_to_closures_ignores_orphan_pointer_metadata() {
        let closure_ids = HashMap::new();
        let mut pointer_modes = HashMap::new();
        let mut modes = HashMap::new();
        modes.insert(0usize, UsageMode::Consuming);
        pointer_modes.insert(42usize, modes);

        let mapped = map_capture_modes_to_closures(&closure_ids, &pointer_modes);
        assert!(mapped.is_empty());
    }

    #[test]
    fn test_filtered_capture_modes_drop_invalid_indices() {
        let term = Term::lam(
            Term::sort(Level::Zero),
            Term::lam(Term::sort(Level::Zero), Term::var(1), BinderInfo::Default),
            BinderInfo::Default,
        );

        let closure_ids = collect_closure_ids(&term, "capture_test");
        let free_vars = collect_closure_free_vars(&term);
        let mut pointer_modes = HashMap::new();

        let outer_ptr = Rc::as_ptr(&term) as usize;
        let mut stale = HashMap::new();
        stale.insert(1usize, UsageMode::Consuming);
        pointer_modes.insert(outer_ptr, stale);

        let filtered =
            map_capture_modes_to_closures_filtered(&closure_ids, &free_vars, &pointer_modes);
        assert_eq!(filtered.len(), closure_ids.len());
        assert!(filtered.values().all(|modes| modes.is_empty()));
    }
}
