use crate::ast::{BinderInfo, DefId, Term};
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum OwnershipError {
    #[error("Use of moved variable at de Bruijn index {0}")]
    UseAfterMove(usize),
    #[error("Implicit binder of non-Copy type used in {mode} position at de Bruijn index {index}")]
    ImplicitNonCopyUse { index: usize, mode: UsageMode },
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

pub struct UsageContext {
    used: Vec<VarUsage>,
}

impl UsageContext {
    pub fn new() -> Self {
        UsageContext { used: Vec::new() }
    }

    pub fn push(&mut self, is_copy: bool) {
        self.push_with_binder(is_copy, BinderInfo::Default);
    }

    pub fn push_with_binder(&mut self, is_copy: bool, info: BinderInfo) {
        let implicit = matches!(info, BinderInfo::Implicit | BinderInfo::StrictImplicit);
        self.used.push(VarUsage {
            used: false,
            is_copy,
            implicit,
        });
    }

    pub fn pop(&mut self) {
        self.used.pop();
    }

    pub fn is_implicit_non_copy(&self, idx: usize) -> bool {
        if idx >= self.used.len() {
            return false;
        }
        let stack_idx = self.used.len() - 1 - idx;
        let var = &self.used[stack_idx];
        var.implicit && !var.is_copy
    }

    pub fn use_var(&mut self, idx: usize, mode: UsageMode) -> Result<(), OwnershipError> {
        if idx >= self.used.len() {
            return Ok(());
        }
        let stack_idx = self.used.len() - 1 - idx;

        let var = &mut self.used[stack_idx];
        if var.implicit
            && (mode == UsageMode::Consuming || mode == UsageMode::MutBorrow)
            && !var.is_copy
        {
            return Err(OwnershipError::ImplicitNonCopyUse { index: idx, mode });
        }
        if mode == UsageMode::Observational || mode == UsageMode::MutBorrow || var.is_copy {
            return Ok(());
        }

        if var.used {
            return Err(OwnershipError::UseAfterMove(idx));
        }

        if mode == UsageMode::Consuming {
            var.used = true;
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct VarUsage {
    used: bool,
    is_copy: bool,
    implicit: bool,
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
        assert!(matches!(res, Err(OwnershipError::UseAfterMove(0))));
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
}
