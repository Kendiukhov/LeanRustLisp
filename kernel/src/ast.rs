use std::rc::Rc;

// =============================================================================
// Totality - Phase 1D: Distinguishing total from partial definitions
// =============================================================================

/// Totality marker for definitions.
/// This is critical for the Lean-grade correctness: only Total definitions
/// can appear in types and participate in definitional equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Totality {
    /// Proven to terminate via structural recursion.
    /// Can appear in types and definitional equality.
    Total,
    /// Proven to terminate via well-founded recursion.
    /// Requires an explicit accessibility proof.
    WellFounded,
    /// May not terminate. Cannot appear in types.
    /// Lives in the computational fragment (Comp).
    Partial,
    /// Assumed without proof. Tracked separately.
    /// Can appear in types but marked as trusted/axiom.
    Axiom,
    /// Uses unsafe features. Explicitly marked and gated.
    Unsafe,
}

/// Transparency levels for reduction
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Transparency {
    None,       // Opaque / Irreducible
    Instances,  // Type class instances
    Reducible,  // Standard definitions (Transparent)
    All,        // Unfold everything (including Opaque if forced)
}

/// Specification for well-founded recursion
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WellFoundedInfo {
    /// Name of the well-founded relation
    pub relation: String,
    /// Which argument position decreases
    pub decreasing_arg: usize,
}

/// A global definition with totality tracking.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Definition {
    pub name: String,
    pub ty: Rc<Term>,
    pub value: Option<Rc<Term>>,  // None for axioms/extern declarations
    pub totality: Totality,
    /// For structural recursion: which parameter is the decreasing argument (if any)
    pub rec_arg: Option<usize>,
    /// For well-founded recursion: the WF specification
    pub wf_info: Option<WellFoundedInfo>,
    /// Unfolding transparency hint
    pub transparency: Transparency,
    /// Axioms used by this definition (transitive closure)
    pub axioms: Vec<String>,
}

impl Definition {
    /// Create a new total definition (must pass termination check)
    pub fn total(name: String, ty: Rc<Term>, value: Rc<Term>) -> Self {
        Definition {
            name, ty, value: Some(value),
            totality: Totality::Total,
            rec_arg: None,
            wf_info: None,
            transparency: Transparency::Reducible, // Default: Transparent
            axioms: vec![],
        }
    }

    /// Create a total definition with explicit decreasing argument
    pub fn total_with_rec_arg(name: String, ty: Rc<Term>, value: Rc<Term>, rec_arg: usize) -> Self {
        Definition {
            name, ty, value: Some(value),
            totality: Totality::Total,
            rec_arg: Some(rec_arg),
            wf_info: None,
            transparency: Transparency::Reducible,
            axioms: vec![],
        }
    }

    /// Create a well-founded recursive definition
    pub fn wellfounded(name: String, ty: Rc<Term>, value: Rc<Term>, wf_info: WellFoundedInfo) -> Self {
        Definition {
            name, ty, value: Some(value),
            totality: Totality::WellFounded,
            rec_arg: Some(wf_info.decreasing_arg),
            wf_info: Some(wf_info),
            transparency: Transparency::Reducible,
            axioms: vec![],
        }
    }

    /// Create a partial definition (general recursion allowed)
    pub fn partial(name: String, ty: Rc<Term>, value: Rc<Term>) -> Self {
        Definition {
            name, ty, value: Some(value),
            totality: Totality::Partial,
            rec_arg: None,
            wf_info: None,
            transparency: Transparency::Reducible,
            axioms: vec![],
        }
    }

    /// Create an axiom (assumed without proof)
    pub fn axiom(name: String, ty: Rc<Term>) -> Self {
        let axiom_name = name.clone();
        Definition {
            name, ty, value: None,
            totality: Totality::Axiom,
            rec_arg: None,
            wf_info: None,
            transparency: Transparency::None, // Axioms don't unfold
            axioms: vec![axiom_name], // Axiom depends on itself
        }
    }

    /// Create an unsafe definition
    pub fn unsafe_def(name: String, ty: Rc<Term>, value: Rc<Term>) -> Self {
        Definition {
            name, ty, value: Some(value),
            totality: Totality::Unsafe,
            rec_arg: None,
            wf_info: None,
            transparency: Transparency::Reducible,
            axioms: vec![],
        }
    }

    /// Check if this definition can be unfolded in type contexts
    pub fn is_type_safe(&self) -> bool {
        matches!(self.totality, Totality::Total | Totality::WellFounded | Totality::Axiom)
    }

    /// Check if this definition is total (terminates)
    pub fn is_total(&self) -> bool {
        matches!(self.totality, Totality::Total | Totality::WellFounded)
    }

    /// Mark this definition as Opaque (Irreducible)
    pub fn mark_opaque(&mut self) {
        self.transparency = Transparency::None;
    }
}

// =============================================================================
// Universe Levels
// =============================================================================

/// Universe levels
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    Param(String),
}

/// Binder information (explicit, implicit, strict implicit)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
}

/// The core terms of the calculus, using de Bruijn indices.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    Lam(Rc<Term>, Rc<Term>, BinderInfo),
    /// Pi type: (x:A) -> B
    Pi(Rc<Term>, Rc<Term>, BinderInfo),
    /// Let binding: let x:A = v in b
    LetE(Rc<Term>, Rc<Term>, Rc<Term>),
    /// Inductive type reference: (Ind "Nat" [levels])
    Ind(String, Vec<Level>),
    /// Constructor: (Ctor "Nat" 0 [levels]) = Nat.zero
    Ctor(String, usize, Vec<Level>),
    /// Recursor/eliminator: (Rec "Nat" [levels])
    Rec(String, Vec<Level>),
    /// Metavariable (hole) to be solved by unification
    Meta(usize),
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
    pub num_params: usize,
    pub ty: Rc<Term>,            // The "arity" (e.g., Type 0 for Nat)
    pub ctors: Vec<Constructor>,
    /// Whether this type has Copy semantics (can be used multiple times without moving).
    /// Types like Nat, Bool are Copy; linear/resource types are not.
    pub is_copy: bool,
}

impl InductiveDecl {
    /// Create a new inductive declaration with default (non-Copy) semantics
    pub fn new(name: String, ty: Rc<Term>, ctors: Vec<Constructor>) -> Self {
        InductiveDecl {
            name,
            univ_params: vec![],
            num_params: 0,
            ty,
            ctors,
            is_copy: false,
        }
    }

    /// Create a Copy inductive (like Nat, Bool)
    pub fn new_copy(name: String, ty: Rc<Term>, ctors: Vec<Constructor>) -> Self {
        InductiveDecl {
            name,
            univ_params: vec![],
            num_params: 0,
            ty,
            ctors,
            is_copy: true,
        }
    }
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
    
    pub fn lam(ty: Rc<Term>, body: Rc<Term>, info: BinderInfo) -> Rc<Self> {
        Rc::new(Term::Lam(ty, body, info))
    }
    
    pub fn pi(ty: Rc<Term>, body: Rc<Term>, info: BinderInfo) -> Rc<Self> {
        Rc::new(Term::Pi(ty, body, info))
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
            Term::Lam(ty, body, info) => Rc::new(Term::Lam(ty.shift(c, d), body.shift(c + 1, d), *info)),
            Term::Pi(ty, body, info) => Rc::new(Term::Pi(ty.shift(c, d), body.shift(c + 1, d), *info)),
            Term::LetE(ty, v, b) => Rc::new(Term::LetE(
                ty.shift(c, d),
                v.shift(c, d),
                b.shift(c + 1, d),
            )),
            Term::Ind(n, ls) => Rc::new(Term::Ind(n.clone(), ls.clone())),
            Term::Ctor(n, idx, ls) => Rc::new(Term::Ctor(n.clone(), *idx, ls.clone())),
            Term::Rec(n, ls) => Rc::new(Term::Rec(n.clone(), ls.clone())),
            Term::Meta(id) => Rc::new(Term::Meta(*id)),
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
            Term::Lam(ty, body, info) => Rc::new(Term::Lam(
                ty.subst(k, s),
                body.subst(k + 1, &s.shift(0, 1)),
                *info,
            )),
            Term::Pi(ty, body, info) => Rc::new(Term::Pi(
                ty.subst(k, s),
                body.subst(k + 1, &s.shift(0, 1)),
                *info,
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
            Term::Meta(id) => Rc::new(Term::Meta(*id)),
        }
    }
}

