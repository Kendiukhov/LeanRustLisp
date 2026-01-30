use crate::ast::{Term, Level, InductiveDecl, Constructor};
use std::collections::HashMap;
use std::rc::Rc;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TypeError {
    #[error("Unknown variable: {0}")]
    UnknownVariable(usize),
    #[error("Type mismatch: expected {expected:?}, got {got:?}")]
    TypeMismatch { expected: Rc<Term>, got: Rc<Term> },
    #[error("Expected function type, got {0:?}")]
    ExpectedFunction(Rc<Term>),
    #[error("Expected sort, got {0:?}")]
    ExpectedSort(Rc<Term>),
    #[error("Unknown inductive type: {0}")]
    UnknownInductive(String),
    #[error("Unknown constructor index {1} for inductive {0}")]
    UnknownConstructor(String, usize),
    #[error("Unknown constant: {0}")]
    UnknownConst(String),
    #[error("Not implemented")]
    NotImplemented,
}

#[derive(Clone)]
pub struct Context {
    types: Vec<Rc<Term>>,
}

impl Context {
    pub fn new() -> Self {
        Context { types: Vec::new() }
    }

    pub fn push(&self, ty: Rc<Term>) -> Self {
        let mut types = self.types.clone();
        types.push(ty);
        Context { types }
    }

    pub fn get(&self, idx: usize) -> Option<Rc<Term>> {
        // de Bruijn index: 0 is the most recently pushed
        if idx < self.types.len() {
             Some(self.types[self.types.len() - 1 - idx].clone())
        } else {
            None
        }
    }
}

/// Global environment containing inductive definitions and constants
#[derive(Clone, Default)]
pub struct Env {
    pub inductives: HashMap<String, InductiveDecl>,
    pub defs: HashMap<String, (Rc<Term>, Rc<Term>)>, // name -> (type, value)
}

impl Env {
    pub fn new() -> Self {
        Env {
            inductives: HashMap::new(),
            defs: HashMap::new(),
        }
    }

    /// Register an inductive type definition
    pub fn add_inductive(&mut self, decl: InductiveDecl) {
        self.inductives.insert(decl.name.clone(), decl);
    }

    /// Register a global definition
    pub fn add_def(&mut self, name: String, ty: Rc<Term>, val: Rc<Term>) {
        self.defs.insert(name, (ty, val));
    }

    /// Get an inductive declaration by name
    pub fn get_inductive(&self, name: &str) -> Option<&InductiveDecl> {
        self.inductives.get(name)
    }

    /// Get a definition by name
    pub fn get_def(&self, name: &str) -> Option<&(Rc<Term>, Rc<Term>)> {
        self.defs.get(name)
    }
}

// =============================================================================
// Universe Level Helpers
// =============================================================================

/// Compute the successor of a universe level
pub fn level_succ(l: Level) -> Level {
    Level::Succ(Box::new(l))
}

/// Compute the maximum of two universe levels (for non-dependent functions)
pub fn level_max(l1: Level, l2: Level) -> Level {
    // Simplification: if both are concrete, compute directly
    match (&l1, &l2) {
        (Level::Zero, _) => l2,
        (_, Level::Zero) => l1,
        _ => Level::Max(Box::new(l1), Box::new(l2)),
    }
}

/// Compute imax(l1, l2) = 0 if l2 = 0, else max(l1, l2)
/// This is used for Pi types: if the codomain is Prop, the Pi is in Prop
pub fn level_imax(l1: Level, l2: Level) -> Level {
    match &l2 {
        Level::Zero => Level::Zero, // If codomain is Prop, result is Prop
        _ => level_max(l1, l2),
    }
}

/// Reduce a level to a simpler form if possible
pub fn reduce_level(l: Level) -> Level {
    match l {
        Level::Max(l1, l2) => {
            let l1r = reduce_level(*l1);
            let l2r = reduce_level(*l2);
            match (&l1r, &l2r) {
                (Level::Zero, _) => l2r,
                (_, Level::Zero) => l1r,
                (Level::Succ(a), Level::Succ(b)) => {
                     // Max(S a, S b) = S(Max(a, b))
                     // We construct a new Max(a, b) and reduce it recursively
                     let max_inner = Level::Max(a.clone(), b.clone());
                     Level::Succ(Box::new(reduce_level(max_inner)))
                }
                _ if l1r == l2r => l1r,
                _ => Level::Max(Box::new(l1r), Box::new(l2r)),
            }
        }
        Level::IMax(l1, l2) => {
            let l1r = reduce_level(*l1);
            let l2r = reduce_level(*l2);
            match &l2r {
                Level::Zero => Level::Zero,
                _ => level_max(l1r, l2r),
            }
        }
        Level::Succ(inner) => Level::Succ(Box::new(reduce_level(*inner))),
        other => other,
    }
}

/// Extract the universe level from a Sort term, or return None if not a Sort
pub fn extract_level(term: &Rc<Term>) -> Option<Level> {
    match &**term {
        Term::Sort(l) => Some(l.clone()),
        _ => None,
    }
}

/// Compute the recursor type for a simple (non-indexed) inductive type.
/// For Nat: (C : Nat → Sort u) → C zero → ((n : Nat) → C n → C (succ n)) → (t : Nat) → C t
pub fn compute_recursor_type(decl: &InductiveDecl, levels: &[Level]) -> Rc<Term> {
    let ind_ref = Rc::new(Term::Ind(decl.name.clone(), vec![]));
    
    // Motive: C : I -> Sort u
    // If levels provided, use levels[0] as u. Else Type 0 (Sort 1).
    // Actually, for Value elimination, we want u=0 (Sort 0).
    // If we want Type elimination, u=1 (Sort 1).
    // Default to 1 (Type 0) to match previous behavior? Or 0?
    // Let's use levels[0] if present, otherwise default to Level::Zero?
    
    let result_sort_level = if let Some(l) = levels.first() {
        l.clone()
    } else {
        // Default to Type 0 (Sort 1) if unspecified?
        // Or default to Prop/Set (Sort 0)?
        // Given LRL is value-oriented, defaulting to Sort 0 might be better for `Rec`.
        // But `Rec` usually defaults to elim-to-Type.
        // Let's check what `Rec` usage in `match` provides.
        // `match` provides empty levels currently.
        // So I should default to Level::Zero (Sort 0) to support `not`.
        Level::Zero
    };
    
    let motive_ty = Term::pi(
        ind_ref.clone(),
        Term::sort(result_sort_level), // Sort u
    );
    
    // Start building from the result type backwards
    // Result: (t : I) → C t
    let major_premise = Term::pi(
        ind_ref.clone(),
        Term::app(Term::var(decl.ctors.len() + 1), Term::var(0)), // C applied to t
    );
    
    // Build minor premises for each constructor
    let mut result = major_premise;
    
    for (ctor_idx, ctor) in decl.ctors.iter().enumerate().rev() {
        // For each constructor, build its minor premise type
        // For zero : Nat, minor is: C zero
        // For succ : Nat → Nat, minor is: (n : Nat) → C n → C (succ n)
        let minor_premise = compute_minor_premise_type(&decl.name, ctor_idx, ctor, decl.ctors.len());
        result = Term::pi(minor_premise, result);
    }
    
    // Wrap with motive binder
    Term::pi(motive_ty, result)
}

/// Compute the type of a minor premise for a constructor.
/// Simplified: handles non-recursive args only for now.
fn compute_minor_premise_type(ind_name: &str, ctor_idx: usize, ctor: &Constructor, num_ctors: usize) -> Rc<Term> {
    let ind_ref = Rc::new(Term::Ind(ind_name.to_string(), vec![]));
    
    // Count recursive arguments in constructor type
    let (num_args, is_recursive) = count_ctor_args(&ctor.ty, ind_name);
    
    if num_args == 0 {
        // Non-recursive constructor like zero : Nat
        // Minor premise type: C (ctor)
        let ctor_term = Rc::new(Term::Ctor(ind_name.to_string(), ctor_idx, vec![]));
        // C is at de Bruijn index ctor_idx (0 for first minor, 1 for second, etc.)
        Term::app(Term::var(ctor_idx), ctor_term)
    } else if num_args == 1 && is_recursive[0] {
        // Recursive constructor like succ : Nat → Nat
        // Minor premise: (n : Nat) → C n → C (succ n)
        let ctor_term = Rc::new(Term::Ctor(ind_name.to_string(), ctor_idx, vec![]));
        Term::pi(
            ind_ref.clone(),
            Term::pi(
                Term::app(Term::var(ctor_idx + 1), Term::var(0)), // C n
                Term::app(
                    Term::var(ctor_idx + 2),
                    Term::app(ctor_term, Term::var(1)), // C (succ n)
                ),
            ),
        )
    } else {
        // Fallback: just return C applied to the constructor
        let ctor_term = Rc::new(Term::Ctor(ind_name.to_string(), ctor_idx, vec![]));
        Term::app(Term::var(num_ctors - ctor_idx), ctor_term)
    }
}

/// Count arguments and track which are recursive (return to the inductive type)
fn count_ctor_args(ty: &Rc<Term>, ind_name: &str) -> (usize, Vec<bool>) {
    let mut current = ty.clone();
    let mut count = 0;
    let mut recursive = Vec::new();
    
    loop {
        match &*current {
            Term::Pi(arg_ty, body) => {
                count += 1;
                // Check if arg type is the inductive type
                let is_rec = matches!(&**arg_ty, Term::Ind(name, _) if name == ind_name);
                recursive.push(is_rec);
                current = body.clone();
            }
            _ => break,
        }
    }
    
    (count, recursive)
}

/// Try to extract constructor info from application spine: returns (ctor_name, ctor_idx, args)
fn try_extract_ctor_app(env: &Env, t: &Rc<Term>) -> Option<(String, usize, Vec<Rc<Term>>)> {
    let mut args = Vec::new();
    let mut current = t.clone();
    
    // Collect arguments in reverse order
    while let Term::App(f, a) = &*current {
        args.push(a.clone());
        current = f.clone();
    }
    
    if let Term::Ctor(ind_name, idx, _) = &*current {
        args.reverse();
        Some((ind_name.clone(), *idx, args))
    } else {
        None
    }
}

/// Weak Head Normal Form reduction with iota reduction
pub fn whnf(env: &Env, t: Rc<Term>) -> Rc<Term> {
    match &*t {
        Term::App(f, a) => {
            let f_norm = whnf(env, f.clone());
            if let Term::Lam(_, body) = &*f_norm {
                whnf(env, body.subst(0, a))
            } else {
                // Check for iota reduction: recursor applied to constructor
                let result = Term::app(f_norm.clone(), a.clone());
                try_iota_reduce(env, &result).unwrap_or(result)
            }
        }
        Term::LetE(_, val, body) => {
            whnf(env, body.subst(0, val))
        }
        Term::Const(name, _) => {
            // Unfold definitions
            if let Some((_, val)) = env.get_def(name) {
                whnf(env, val.clone())
            } else {
                t
            }
        }
        _ => t,
    }
}

/// Try to perform iota reduction on a term
fn try_iota_reduce(env: &Env, t: &Rc<Term>) -> Option<Rc<Term>> {
    // Collect the application spine to find the recursor
    let mut args = Vec::new();
    let mut current = t.clone();
    
    while let Term::App(f, a) = &*current {
        args.push(a.clone());
        current = f.clone();
    }
    args.reverse();
    
    // Check if head is a recursor
    if let Term::Rec(ind_name, _) = &*current {
        if let Some(decl) = env.get_inductive(ind_name) {
            let num_ctors = decl.ctors.len();
            // Expected args: motive, minor_1, ..., minor_n, major
            let expected_args = 1 + num_ctors + 1;
            
            if args.len() >= expected_args {
                let _motive = &args[0];
                let minors = &args[1..1 + num_ctors];
                let major = whnf(env, args[1 + num_ctors].clone());
                
                // Check if major is a constructor application
                if let Some((ctor_ind, ctor_idx, ctor_args)) = try_extract_ctor_app(env, &major) {
                    if ctor_ind == *ind_name && ctor_idx < num_ctors {
                        let minor = &minors[ctor_idx];
                        
                        // Apply minor to constructor arguments and recursive calls
                        let mut result = minor.clone();
                        for (i, arg) in ctor_args.iter().enumerate() {
                            result = Term::app(result.clone(), arg.clone());
                            
                            // If this is a recursive argument, also apply the IH
                            let (_, is_recursive) = count_ctor_args(&decl.ctors[ctor_idx].ty, ind_name);
                            if i < is_recursive.len() && is_recursive[i] {
                                // Build recursive call: rec motive minors arg
                                let mut rec_call = Rc::new(Term::Rec(ind_name.clone(), vec![]));
                                rec_call = Term::app(rec_call, args[0].clone()); // motive
                                for m in minors {
                                    rec_call = Term::app(rec_call, m.clone());
                                }
                                rec_call = Term::app(rec_call, arg.clone());
                                result = Term::app(result, rec_call);
                            }
                        }
                        
                        // Apply remaining arguments after major
                        for arg in args.iter().skip(expected_args) {
                            result = Term::app(result, arg.clone());
                        }
                        
                        return Some(whnf(env, result));
                    }
                }
            }
        }
    }
    
    None
}

/// Definitional equality checking
pub fn is_def_eq(env: &Env, t1: Rc<Term>, t2: Rc<Term>) -> bool {
    let t1 = whnf(env, t1);
    let t2 = whnf(env, t2);
    
    if t1 == t2 {
        return true;
    }
    
    match (&*t1, &*t2) {
        (Term::Sort(l1), Term::Sort(l2)) => l1 == l2,
        (Term::Var(i1), Term::Var(i2)) => i1 == i2,
        (Term::App(f1, a1), Term::App(f2, a2)) => {
            is_def_eq(env, f1.clone(), f2.clone()) && is_def_eq(env, a1.clone(), a2.clone())
        }
        (Term::Lam(ty1, b1), Term::Lam(ty2, b2)) => {
            is_def_eq(env, ty1.clone(), ty2.clone()) && is_def_eq(env, b1.clone(), b2.clone())
        }
        (Term::Pi(ty1, b1), Term::Pi(ty2, b2)) => {
            is_def_eq(env, ty1.clone(), ty2.clone()) && is_def_eq(env, b1.clone(), b2.clone())
        }
        (Term::Ind(n1, _), Term::Ind(n2, _)) => n1 == n2,
        (Term::Ctor(n1, i1, _), Term::Ctor(n2, i2, _)) => n1 == n2 && i1 == i2,
        (Term::Rec(n1, _), Term::Rec(n2, _)) => n1 == n2,
        _ => false,
    }
}

pub fn check(env: &Env, ctx: &Context, term: Rc<Term>, expected_type: Rc<Term>) -> Result<(), TypeError> {
    let inferred = infer(env, ctx, term.clone())?;
    if !is_def_eq(env, inferred.clone(), expected_type.clone()) {
        return Err(TypeError::TypeMismatch { expected: expected_type, got: inferred });
    }
    Ok(())
}

pub fn infer(env: &Env, ctx: &Context, term: Rc<Term>) -> Result<Rc<Term>, TypeError> {
    match &*term {
        Term::Var(idx) => {
            if let Some(ty) = ctx.get(*idx) {
                Ok(ty.shift(0, idx + 1)) 
            } else {
                Err(TypeError::UnknownVariable(*idx))
            }
        }
        Term::Sort(l) => {
            // Sort u : Sort (u+1)
            // Prop (Level::Zero) : Type 0
            // Type u : Type (u+1)
            Ok(Term::sort(level_succ(l.clone())))
        }
        Term::Lam(ty, body) => {
            infer(env, ctx, ty.clone())?;
            let new_ctx = ctx.push(ty.clone());
            let body_ty = infer(env, &new_ctx, body.clone())?;
            Ok(Term::pi(ty.clone(), body_ty))
        }
        Term::Pi(ty, body) => {
            // Pi (x : A) -> B has type Sort(imax(level(A), level(B)))
            let s1 = infer(env, ctx, ty.clone())?;
            let s1_norm = whnf(env, s1);
            
            let new_ctx = ctx.push(ty.clone());
            let s2 = infer(env, &new_ctx, body.clone())?;
            let s2_norm = whnf(env, s2);
            
            // Extract levels from sorts
            if let (Some(l1), Some(l2)) = (extract_level(&s1_norm), extract_level(&s2_norm)) {
                // Use imax for impredicative Prop: if codomain is Prop, result is Prop
                let result_level = reduce_level(level_imax(l1, l2));
                Ok(Term::sort(result_level))
            } else {
                // If either isn't a sort, just return the codomain's sort (fallback)
                Ok(s2_norm)
            }
        }
        Term::App(f, a) => {
            let f_ty = infer(env, ctx, f.clone())?;
            let f_ty_norm = whnf(env, f_ty);
            
            if let Term::Pi(arg_ty, body_ty) = &*f_ty_norm {
                check(env, ctx, a.clone(), arg_ty.clone())?;
                Ok(body_ty.subst(0, a))
            } else {
                Err(TypeError::ExpectedFunction(f_ty_norm))
            }
        }
        Term::Const(name, _levels) => {
            if let Some((ty, _)) = env.get_def(name) {
                Ok(ty.clone())
            } else {
                Err(TypeError::UnknownConst(name.clone()))
            }
        }
        Term::LetE(ty, v, b) => {
            check(env, ctx, v.clone(), ty.clone())?;
            let new_ctx = ctx.push(ty.clone());
            let b_ty = infer(env, &new_ctx, b.clone())?;
            Ok(b_ty.subst(0, v))
        }
        Term::Ind(name, _levels) => {
            // Return the arity of the inductive type
            if let Some(decl) = env.get_inductive(name) {
                Ok(decl.ty.clone())
            } else {
                Err(TypeError::UnknownInductive(name.clone()))
            }
        }
        Term::Ctor(ind_name, idx, _levels) => {
            // Return the type of the constructor
            if let Some(decl) = env.get_inductive(ind_name) {
                if let Some(ctor) = decl.ctors.get(*idx) {
                    Ok(ctor.ty.clone())
                } else {
                    Err(TypeError::UnknownConstructor(ind_name.clone(), *idx))
                }
            } else {
                Err(TypeError::UnknownInductive(ind_name.clone()))
            }
        }
        Term::Rec(ind_name, _levels) => {
            // Compute and return the recursor type
            if let Some(decl) = env.get_inductive(ind_name) {
                Ok(compute_recursor_type(decl, _levels))
            } else {
                Err(TypeError::UnknownInductive(ind_name.clone()))
            }
        }
    }
}

