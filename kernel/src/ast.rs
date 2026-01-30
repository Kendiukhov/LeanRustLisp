use std::rc::Rc;
use std::fmt;

/// Universe levels
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    Param(String),
}

/// The core terms of the calculus, using de Bruijn indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Bound variable (de Bruijn index)
    Var(usize),
    /// Universe
    Sort(Level),
    /// Constant (global definition)
    Const(String, Vec<Level>),
    /// Application: (f a)
    App(Rc<Term>, Rc<Term>),
    /// Lambda abstraction: \x:A. b
    Lam(Rc<Term>, Rc<Term>),
    /// Pi type: (x:A) -> B
    Pi(Rc<Term>, Rc<Term>),
    /// Let binding: let x:A = v in b
    LetE(Rc<Term>, Rc<Term>, Rc<Term>),
    /// Inductive type reference: (Ind "Nat" [levels])
    Ind(String, Vec<Level>),
    /// Constructor: (Ctor "Nat" 0 [levels]) = Nat.zero
    Ctor(String, usize, Vec<Level>),
    /// Recursor/eliminator: (Rec "Nat" [levels])
    Rec(String, Vec<Level>),
}

/// A single constructor of an inductive type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: String,
    pub ty: Rc<Term>,  // Type relative to inductive params
}

/// Inductive type definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveDecl {
    pub name: String,
    pub univ_params: Vec<String>,
    pub ty: Rc<Term>,            // The "arity" (e.g., Type 0 for Nat)
    pub ctors: Vec<Constructor>,
}

// Helper constructors for convenience
impl Term {
    pub fn var(n: usize) -> Rc<Self> {
        Rc::new(Term::Var(n))
    }
    
    pub fn sort(l: Level) -> Rc<Self> {
        Rc::new(Term::Sort(l))
    }
    
    pub fn app(f: Rc<Term>, a: Rc<Term>) -> Rc<Self> {
        Rc::new(Term::App(f, a))
    }
    
    pub fn lam(ty: Rc<Term>, body: Rc<Term>) -> Rc<Self> {
        Rc::new(Term::Lam(ty, body))
    }
    
    pub fn pi(ty: Rc<Term>, body: Rc<Term>) -> Rc<Self> {
        Rc::new(Term::Pi(ty, body))
    }

    pub fn ind(name: String) -> Rc<Self> {
        Rc::new(Term::Ind(name, vec![]))
    }

    pub fn ctor(ind_name: String, idx: usize) -> Rc<Self> {
        Rc::new(Term::Ctor(ind_name, idx, vec![]))
    }

    pub fn rec(ind_name: String) -> Rc<Self> {
        Rc::new(Term::Rec(ind_name, vec![]))
    }

    /// Shift indices in a term by `d` above cutoff `c`.
    pub fn shift(&self, c: usize, d: usize) -> Rc<Term> {
        match self {
            Term::Var(k) => {
                if *k < c {
                    Rc::new(Term::Var(*k))
                } else {
                    Rc::new(Term::Var(k + d))
                }
            }
            Term::Sort(l) => Rc::new(Term::Sort(l.clone())),
            Term::Const(n, ls) => Rc::new(Term::Const(n.clone(), ls.clone())),
            Term::App(f, a) => Rc::new(Term::App(f.shift(c, d), a.shift(c, d))),
            Term::Lam(ty, body) => Rc::new(Term::Lam(ty.shift(c, d), body.shift(c + 1, d))),
            Term::Pi(ty, body) => Rc::new(Term::Pi(ty.shift(c, d), body.shift(c + 1, d))),
            Term::LetE(ty, v, b) => Rc::new(Term::LetE(
                ty.shift(c, d),
                v.shift(c, d),
                b.shift(c + 1, d),
            )),
            // Ind, Ctor, Rec have no bound variables to shift
            Term::Ind(n, ls) => Rc::new(Term::Ind(n.clone(), ls.clone())),
            Term::Ctor(n, idx, ls) => Rc::new(Term::Ctor(n.clone(), *idx, ls.clone())),
            Term::Rec(n, ls) => Rc::new(Term::Rec(n.clone(), ls.clone())),
        }
    }

    /// Substitute `s` for variable `k` in `t`.
    pub fn subst(&self, k: usize, s: &Rc<Term>) -> Rc<Term> {
        match self {
            Term::Var(i) => {
                if *i == k {
                    s.clone()
                } else if *i > k {
                    Rc::new(Term::Var(i - 1))
                } else {
                    Rc::new(Term::Var(*i))
                }
            }
            Term::Sort(l) => Rc::new(Term::Sort(l.clone())),
            Term::Const(n, ls) => Rc::new(Term::Const(n.clone(), ls.clone())),
            Term::App(f, a) => Rc::new(Term::App(f.subst(k, s), a.subst(k, s))),
            Term::Lam(ty, body) => Rc::new(Term::Lam(
                ty.subst(k, s),
                body.subst(k + 1, &s.shift(0, 1)),
            )),
            Term::Pi(ty, body) => Rc::new(Term::Pi(
                ty.subst(k, s),
                body.subst(k + 1, &s.shift(0, 1)),
            )),
            Term::LetE(ty, v, b) => Rc::new(Term::LetE(
                ty.subst(k, s),
                v.subst(k, s),
                b.subst(k + 1, &s.shift(0, 1)),
            )),
            // Ind, Ctor, Rec have no bound variables
            Term::Ind(n, ls) => Rc::new(Term::Ind(n.clone(), ls.clone())),
            Term::Ctor(n, idx, ls) => Rc::new(Term::Ctor(n.clone(), *idx, ls.clone())),
            Term::Rec(n, ls) => Rc::new(Term::Rec(n.clone(), ls.clone())),
        }
    }
}

