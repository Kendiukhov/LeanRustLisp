use crate::ast::Term;
use std::rc::Rc;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum OwnershipError {
    #[error("Use of moved variable at de Bruijn index {0}")]
    UseAfterMove(usize),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum UsageMode {
    Consuming,
    Observational,
}

pub struct UsageContext {
    used: Vec<VarUsage>,
}

impl UsageContext {
    pub fn new() -> Self {
        UsageContext { used: Vec::new() }
    }

    pub fn push(&mut self, is_copy: bool) {
        self.used.push(VarUsage { used: false, is_copy });
    }

    pub fn pop(&mut self) {
        self.used.pop();
    }

    pub fn use_var(&mut self, idx: usize, mode: UsageMode) -> Result<(), OwnershipError> {
        if idx >= self.used.len() {
             return Ok(());
        }
        let stack_idx = self.used.len() - 1 - idx;
        
        let var = &mut self.used[stack_idx];
        if mode == UsageMode::Observational || var.is_copy {
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
}

pub fn check_ownership(term: &Rc<Term>, ctx: &mut UsageContext, mode: UsageMode) -> Result<(), OwnershipError> {
    match &**term {
        Term::Var(i) => ctx.use_var(*i, mode),
        Term::App(f, a) => {
            check_ownership(f, ctx, mode)?;
            check_ownership(a, ctx, mode)?;
            Ok(())
        }
        Term::Lam(ty, body, _) => {
            // body is evaluated with x: ty
            // ty is evaluated in current context
            check_ownership(ty, ctx, UsageMode::Observational)?; // Assuming original signature for ty
            ctx.push(false); // Untyped check assumes affine
            let res = check_ownership(body, ctx, mode); // Original call
            ctx.pop(); // Original pop
            res
        }
        Term::Pi(ty, body, _) => {
            // Depedent types usually don't consume resources linearly in type position,
            // but the body is a type that might depend on x
            check_ownership(ty, ctx, UsageMode::Observational)?; // Assuming original signature for ty
            ctx.push(false); // Untyped check assumes affine
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
    use crate::ast::{Level, BinderInfo};

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
            Term::app(
                Term::app(Term::var(1), Term::var(0)),
                Term::var(0)
            ),
            BinderInfo::Default
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
                BinderInfo::Default
            ),
            BinderInfo::Default
        );
        assert!(check_ownership(&t, &mut ctx, UsageMode::Consuming).is_ok());
    }
}
