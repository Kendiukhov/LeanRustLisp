use crate::ownership::DefCaptureModeMap;
use std::collections::HashSet;
use std::fmt;
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

/// Classification of definitions for axiom/primitive tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionKind {
    /// Ordinary definition.
    Def,
    /// Logical axiom (noncomputable requirement for dependents).
    AxiomLogical,
    /// Trusted runtime primitive (does not force noncomputable).
    Primitive,
}

/// Transparency levels for reduction
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Transparency {
    None,      // Opaque / Irreducible
    Instances, // Type class instances
    Reducible, // Standard definitions (Transparent)
    All,       // Unfold everything (including Opaque if forced)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CopyInstanceSource {
    Derived,
    Explicit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CopyInstance {
    pub ind_name: String,
    pub param_count: usize,
    pub requirements: Vec<Rc<Term>>,
    pub source: CopyInstanceSource,
    pub is_unsafe: bool,
}

/// Tags for axioms to track logical and safety assumptions explicitly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum AxiomTag {
    Classical,
    Unsafe,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub u64);

impl DefId {
    pub fn new(name: impl AsRef<str>) -> Self {
        DefId(stable_hash64("def", name.as_ref()))
    }
}

/// Marker attributes for types/inductives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeMarker {
    /// Indicates a type uses interior mutability.
    InteriorMutable,
    /// RefCell-like: may panic on dynamic borrow violation.
    MayPanicOnBorrowViolation,
    /// Concurrency primitive family (Mutex/Atomic).
    ConcurrencyPrimitive,
    /// Atomic-specific marker.
    AtomicPrimitive,
    /// Marks container types that support indexing sugar.
    Indexable,
}

/// Explicit opt-in for MIR borrow-shape classification on opaque aliases.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BorrowWrapperMarker {
    RefShared,
    RefMut,
    RefCell,
    Mutex,
    Atomic,
}

/// Marker identifier (points at a trusted marker definition).
pub type MarkerId = DefId;

/// Canonical marker name for a given marker kind.
pub fn marker_name(marker: TypeMarker) -> &'static str {
    match marker {
        TypeMarker::InteriorMutable => "interior_mutable",
        TypeMarker::MayPanicOnBorrowViolation => "may_panic_on_borrow_violation",
        TypeMarker::ConcurrencyPrimitive => "concurrency_primitive",
        TypeMarker::AtomicPrimitive => "atomic_primitive",
        TypeMarker::Indexable => "indexable",
    }
}

/// Compute the canonical marker DefId for a marker kind.
pub fn marker_def_id(marker: TypeMarker) -> MarkerId {
    DefId::new(marker_name(marker))
}

/// Names reserved for primitive operations that must not be shadowed.
pub const RESERVED_PRIMITIVE_NAMES: [&str; 8] = [
    "Ref",
    "Shared",
    "Mut",
    "borrow_shared",
    "borrow_mut",
    "index_vec_dyn",
    "index_slice",
    "index_array",
];

pub fn is_reserved_primitive_name(name: &str) -> bool {
    RESERVED_PRIMITIVE_NAMES
        .iter()
        .any(|reserved| *reserved == name)
}

/// Names reserved for type marker axioms (must not be shadowed).
pub const RESERVED_MARKER_NAMES: [&str; 5] = [
    "interior_mutable",
    "may_panic_on_borrow_violation",
    "concurrency_primitive",
    "atomic_primitive",
    "indexable",
];

pub fn is_reserved_marker_name(name: &str) -> bool {
    RESERVED_MARKER_NAMES
        .iter()
        .any(|reserved| *reserved == name)
}

/// Core prelude names that are part of the TCB and must not be shadowed by user code.
pub const RESERVED_CORE_NAMES: [&str; 6] = ["Comp", "Eq", "Nat", "Bool", "List", "False"];

pub fn is_reserved_core_name(name: &str) -> bool {
    RESERVED_CORE_NAMES.iter().any(|reserved| *reserved == name)
}

fn stable_hash64(tag: &str, name: &str) -> u64 {
    const FNV_OFFSET: u64 = 14695981039346656037;
    const FNV_PRIME: u64 = 1099511628211;

    let mut hash = FNV_OFFSET;
    for b in tag.as_bytes() {
        hash ^= *b as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash ^= b':' as u64;
    hash = hash.wrapping_mul(FNV_PRIME);
    for b in name.as_bytes() {
        hash ^= *b as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub name: String,
    pub ty: Rc<Term>,
    pub value: Option<Rc<Term>>, // None for axioms/extern declarations
    pub totality: Totality,
    /// Axiom/primitive classification for dependency tracking.
    pub kind: DefinitionKind,
    /// For structural recursion: which parameter is the decreasing argument (if any)
    pub rec_arg: Option<usize>,
    /// For well-founded recursion: the WF specification
    pub wf_info: Option<WellFoundedInfo>,
    /// Whether well-founded recursion has been verified (guard for unfolding)
    pub wf_checked: bool,
    /// Unfolding transparency hint
    pub transparency: Transparency,
    /// Explicit axiom tags (e.g., classical) when this definition is an axiom.
    pub axiom_tags: Vec<AxiomTag>,
    /// Logical axioms used by this definition (transitive closure).
    pub axioms: Vec<String>,
    /// Runtime primitives used by this definition (transitive closure).
    pub primitive_deps: Vec<String>,
    /// Explicit noncomputable marker (opt-in for axiom-dependent code).
    pub noncomputable: bool,
    /// Per-closure capture mode annotations keyed by closure id.
    pub capture_modes: DefCaptureModeMap,
    /// Optional explicit borrow-shape marker for opaque wrapper aliases.
    pub borrow_wrapper_marker: Option<BorrowWrapperMarker>,
}

impl Definition {
    /// Create a new total definition (must pass termination check)
    pub fn total(name: String, ty: Rc<Term>, value: Rc<Term>) -> Self {
        Definition {
            name,
            ty,
            value: Some(value),
            totality: Totality::Total,
            kind: DefinitionKind::Def,
            rec_arg: None,
            wf_info: None,
            wf_checked: true,
            transparency: Transparency::Reducible, // Default: Transparent
            axiom_tags: vec![],
            axioms: vec![],
            primitive_deps: vec![],
            noncomputable: false,
            capture_modes: DefCaptureModeMap::new(),
            borrow_wrapper_marker: None,
        }
    }

    /// Create a total definition with explicit decreasing argument
    pub fn total_with_rec_arg(name: String, ty: Rc<Term>, value: Rc<Term>, rec_arg: usize) -> Self {
        Definition {
            name,
            ty,
            value: Some(value),
            totality: Totality::Total,
            kind: DefinitionKind::Def,
            rec_arg: Some(rec_arg),
            wf_info: None,
            wf_checked: true,
            transparency: Transparency::Reducible,
            axiom_tags: vec![],
            axioms: vec![],
            primitive_deps: vec![],
            noncomputable: false,
            capture_modes: DefCaptureModeMap::new(),
            borrow_wrapper_marker: None,
        }
    }

    /// Create a well-founded recursive definition
    pub fn wellfounded(
        name: String,
        ty: Rc<Term>,
        value: Rc<Term>,
        wf_info: WellFoundedInfo,
    ) -> Self {
        Definition {
            name,
            ty,
            value: Some(value),
            totality: Totality::WellFounded,
            kind: DefinitionKind::Def,
            rec_arg: Some(wf_info.decreasing_arg),
            wf_info: Some(wf_info),
            wf_checked: false,
            transparency: Transparency::Reducible,
            axiom_tags: vec![],
            axioms: vec![],
            primitive_deps: vec![],
            noncomputable: false,
            capture_modes: DefCaptureModeMap::new(),
            borrow_wrapper_marker: None,
        }
    }

    /// Create a partial definition (general recursion allowed)
    pub fn partial(name: String, ty: Rc<Term>, value: Rc<Term>) -> Self {
        Definition {
            name,
            ty,
            value: Some(value),
            totality: Totality::Partial,
            kind: DefinitionKind::Def,
            rec_arg: None,
            wf_info: None,
            wf_checked: true,
            transparency: Transparency::Reducible,
            axiom_tags: vec![],
            axioms: vec![],
            primitive_deps: vec![],
            noncomputable: false,
            capture_modes: DefCaptureModeMap::new(),
            borrow_wrapper_marker: None,
        }
    }

    /// Create an axiom (assumed without proof)
    pub fn axiom(name: String, ty: Rc<Term>) -> Self {
        Self::axiom_with_tags(name, ty, vec![])
    }

    /// Create a classical axiom (e.g., EM/Choice)
    pub fn axiom_classical(name: String, ty: Rc<Term>) -> Self {
        Self::axiom_with_tags(name, ty, vec![AxiomTag::Classical])
    }

    /// Create an axiom with explicit tags.
    pub fn axiom_with_tags(name: String, ty: Rc<Term>, mut tags: Vec<AxiomTag>) -> Self {
        tags.sort();
        tags.dedup();
        let axiom_name = name.clone();
        Definition {
            name,
            ty,
            value: None,
            totality: Totality::Axiom,
            kind: DefinitionKind::AxiomLogical,
            rec_arg: None,
            wf_info: None,
            wf_checked: true,
            transparency: Transparency::None, // Axioms don't unfold
            axiom_tags: tags,
            axioms: vec![axiom_name], // Axiom depends on itself
            primitive_deps: vec![],
            noncomputable: false,
            capture_modes: DefCaptureModeMap::new(),
            borrow_wrapper_marker: None,
        }
    }

    /// Create an unsafe definition
    pub fn unsafe_def(name: String, ty: Rc<Term>, value: Rc<Term>) -> Self {
        Definition {
            name,
            ty,
            value: Some(value),
            totality: Totality::Unsafe,
            kind: DefinitionKind::Def,
            rec_arg: None,
            wf_info: None,
            wf_checked: true,
            transparency: Transparency::Reducible,
            axiom_tags: vec![],
            axioms: vec![],
            primitive_deps: vec![],
            noncomputable: false,
            capture_modes: DefCaptureModeMap::new(),
            borrow_wrapper_marker: None,
        }
    }

    /// Check if this definition can be unfolded in type contexts
    pub fn is_type_safe(&self) -> bool {
        let totality = self.effective_totality();
        matches!(totality, Totality::Total | Totality::Axiom)
            || (totality == Totality::WellFounded && self.wf_checked)
    }

    /// Check if this definition is total (terminates)
    pub fn is_total(&self) -> bool {
        matches!(self.totality, Totality::Total)
            || (self.totality == Totality::WellFounded && self.wf_checked)
    }

    /// Check if this definition is noncomputable (explicit or axiom-dependent).
    pub fn is_noncomputable(&self) -> bool {
        self.noncomputable || !self.axioms.is_empty()
    }

    /// Effective totality accounting for unsafe-tagged axioms.
    pub fn effective_totality(&self) -> Totality {
        if self.totality == Totality::Axiom && self.axiom_tags.contains(&AxiomTag::Unsafe) {
            Totality::Unsafe
        } else {
            self.totality
        }
    }

    /// Mark this definition as Opaque (Irreducible)
    pub fn mark_opaque(&mut self) {
        self.transparency = Transparency::None;
    }

    pub fn mark_borrow_wrapper(&mut self, marker: BorrowWrapperMarker) {
        self.borrow_wrapper_marker = Some(marker);
    }

    /// Check if this definition is tagged as a classical axiom.
    pub fn is_classical_axiom(&self) -> bool {
        self.axiom_tags.contains(&AxiomTag::Classical)
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

fn level_key(level: &Level) -> String {
    match level {
        Level::Zero => "0".to_string(),
        Level::Param(name) => format!("P({})", name),
        Level::Succ(inner) => format!("S({})", level_key(inner)),
        Level::Max(a, b) => format!("M({}, {})", level_key(a), level_key(b)),
        Level::IMax(a, b) => format!("I({}, {})", level_key(a), level_key(b)),
    }
}

fn collect_max(level: Level, out: &mut Vec<Level>) {
    match level {
        Level::Max(a, b) => {
            collect_max(*a, out);
            collect_max(*b, out);
        }
        other => out.push(other),
    }
}

fn normalize_max(levels: Vec<Level>) -> Level {
    let mut flat = Vec::new();
    for level in levels {
        collect_max(level, &mut flat);
    }

    flat.retain(|level| !matches!(level, Level::Zero));

    if flat.is_empty() {
        return Level::Zero;
    }

    if flat.len() == 1 {
        return flat.pop().expect("non-empty");
    }

    if flat.iter().all(|level| matches!(level, Level::Succ(_))) {
        let inners: Vec<Level> = flat
            .into_iter()
            .map(|level| match level {
                Level::Succ(inner) => *inner,
                _ => unreachable!("all entries are Succ"),
            })
            .collect();
        return Level::Succ(Box::new(normalize_max(inners)));
    }

    let mut seen = HashSet::new();
    flat.retain(|level| seen.insert(level.clone()));
    flat.sort_by(|a, b| level_key(a).cmp(&level_key(b)));

    let mut iter = flat.into_iter();
    let first = iter.next().expect("non-empty");
    iter.fold(first, |acc, level| {
        Level::Max(Box::new(acc), Box::new(level))
    })
}

pub fn normalize_level(level: Level) -> Level {
    match level {
        Level::Zero | Level::Param(_) => level,
        Level::Succ(inner) => Level::Succ(Box::new(normalize_level(*inner))),
        Level::IMax(a, b) => {
            let a_norm = normalize_level(*a);
            let b_norm = normalize_level(*b);
            if matches!(b_norm, Level::Zero) {
                Level::Zero
            } else {
                normalize_max(vec![a_norm, b_norm])
            }
        }
        Level::Max(a, b) => {
            let a_norm = normalize_level(*a);
            let b_norm = normalize_level(*b);
            normalize_max(vec![a_norm, b_norm])
        }
    }
}

pub fn normalize_levels(levels: &[Level]) -> Vec<Level> {
    levels.iter().cloned().map(normalize_level).collect()
}

pub fn level_eq(l1: &Level, l2: &Level) -> bool {
    normalize_level(l1.clone()) == normalize_level(l2.clone())
}

pub fn levels_eq(ls1: &[Level], ls2: &[Level]) -> bool {
    if ls1.len() != ls2.len() {
        return false;
    }
    ls1.iter().zip(ls2.iter()).all(|(l1, l2)| level_eq(l1, l2))
}

/// Binder information (explicit, implicit, strict implicit)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
}

/// Function/closure kind for Pi/Lam.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionKind {
    Fn,
    FnMut,
    FnOnce,
}

/// The core terms of the calculus, using de Bruijn indices.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// Bound variable (de Bruijn index)
    Var(usize),
    /// Universe
    Sort(Level),
    /// Constant (global definition)
    Const(String, Vec<Level>),
    /// Application: (f a)
    /// Optional label is used for Ref lifetime annotations on the outer Ref application.
    App(Rc<Term>, Rc<Term>, Option<String>),
    /// Lambda abstraction: \x:A. b
    Lam(Rc<Term>, Rc<Term>, BinderInfo, FunctionKind),
    /// Pi type: (x:A) -> B
    Pi(Rc<Term>, Rc<Term>, BinderInfo, FunctionKind),
    /// Let binding: let x:A = v in b
    LetE(Rc<Term>, Rc<Term>, Rc<Term>),
    /// Inductive type reference: (Ind "Nat" [levels])
    Ind(String, Vec<Level>),
    /// Constructor: (Ctor "Nat" 0 [levels]) = Nat.zero
    Ctor(String, usize, Vec<Level>),
    /// Recursor/eliminator: (Rec "Nat" [levels])
    Rec(String, Vec<Level>),
    /// Fixpoint combinator: fix x:T. body
    Fix(Rc<Term>, Rc<Term>),
    /// Metavariable (hole) to be solved by unification
    Meta(usize),
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(idx) => f.debug_tuple("Var").field(idx).finish(),
            Term::Sort(level) => f.debug_tuple("Sort").field(level).finish(),
            Term::Const(name, levels) => f.debug_tuple("Const").field(name).field(levels).finish(),
            Term::App(fun, arg, label) => {
                let mut dbg = f.debug_tuple("App");
                dbg.field(fun).field(arg);
                if let Some(label) = label {
                    dbg.field(&format_args!("#{}", label));
                }
                dbg.finish()
            }
            Term::Lam(ty, body, info, kind) => f
                .debug_tuple("Lam")
                .field(ty)
                .field(body)
                .field(info)
                .field(kind)
                .finish(),
            Term::Pi(ty, body, info, kind) => f
                .debug_tuple("Pi")
                .field(ty)
                .field(body)
                .field(info)
                .field(kind)
                .finish(),
            Term::LetE(ty, val, body) => f
                .debug_tuple("LetE")
                .field(ty)
                .field(val)
                .field(body)
                .finish(),
            Term::Ind(name, levels) => f.debug_tuple("Ind").field(name).field(levels).finish(),
            Term::Ctor(name, idx, levels) => f
                .debug_tuple("Ctor")
                .field(name)
                .field(idx)
                .field(levels)
                .finish(),
            Term::Rec(name, levels) => f.debug_tuple("Rec").field(name).field(levels).finish(),
            Term::Fix(ty, body) => f.debug_tuple("Fix").field(ty).field(body).finish(),
            Term::Meta(id) => f.debug_tuple("Meta").field(id).finish(),
        }
    }
}

/// A single constructor of an inductive type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: String,
    pub ty: Rc<Term>, // Type relative to inductive params
}

/// Inductive type definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveDecl {
    pub name: String,
    pub univ_params: Vec<String>,
    pub num_params: usize,
    pub ty: Rc<Term>, // The "arity" (e.g., Type 0 for Nat)
    pub ctors: Vec<Constructor>,
    /// Whether Copy derivation was explicitly requested (e.g., `(inductive copy ...)`).
    pub is_copy: bool,
    /// Marker identifiers attached to this type.
    pub markers: Vec<MarkerId>,
    /// Logical axioms used by this inductive (transitive closure).
    pub axioms: Vec<String>,
    /// Runtime primitives used by this inductive (transitive closure).
    pub primitive_deps: Vec<String>,
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
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
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
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        }
    }

    pub fn has_marker_id(&self, marker: MarkerId) -> bool {
        self.markers.contains(&marker)
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
        Rc::new(Term::App(f, a, None))
    }

    pub fn app_with_label(f: Rc<Term>, a: Rc<Term>, label: Option<String>) -> Rc<Self> {
        Rc::new(Term::App(f, a, label))
    }

    pub fn lam(ty: Rc<Term>, body: Rc<Term>, info: BinderInfo) -> Rc<Self> {
        Rc::new(Term::Lam(ty, body, info, FunctionKind::Fn))
    }

    pub fn pi(ty: Rc<Term>, body: Rc<Term>, info: BinderInfo) -> Rc<Self> {
        Rc::new(Term::Pi(ty, body, info, FunctionKind::Fn))
    }

    pub fn lam_with_kind(
        ty: Rc<Term>,
        body: Rc<Term>,
        info: BinderInfo,
        kind: FunctionKind,
    ) -> Rc<Self> {
        Rc::new(Term::Lam(ty, body, info, kind))
    }

    pub fn pi_with_kind(
        ty: Rc<Term>,
        body: Rc<Term>,
        info: BinderInfo,
        kind: FunctionKind,
    ) -> Rc<Self> {
        Rc::new(Term::Pi(ty, body, info, kind))
    }

    pub fn ind(name: String) -> Rc<Self> {
        Rc::new(Term::Ind(name, vec![]))
    }

    pub fn ctor(ind_name: String, idx: usize) -> Rc<Self> {
        Rc::new(Term::Ctor(ind_name, idx, vec![]))
    }

    pub fn rec(ind_name: String, levels: Vec<Level>) -> Rc<Self> {
        Rc::new(Term::Rec(ind_name, levels))
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
            Term::App(f, a, label) => {
                Rc::new(Term::App(f.shift(c, d), a.shift(c, d), label.clone()))
            }
            Term::Lam(ty, body, info, kind) => Rc::new(Term::Lam(
                ty.shift(c, d),
                body.shift(c + 1, d),
                *info,
                *kind,
            )),
            Term::Pi(ty, body, info, kind) => {
                Rc::new(Term::Pi(ty.shift(c, d), body.shift(c + 1, d), *info, *kind))
            }
            Term::LetE(ty, v, b) => {
                Rc::new(Term::LetE(ty.shift(c, d), v.shift(c, d), b.shift(c + 1, d)))
            }
            Term::Ind(n, ls) => Rc::new(Term::Ind(n.clone(), ls.clone())),
            Term::Ctor(n, idx, ls) => Rc::new(Term::Ctor(n.clone(), *idx, ls.clone())),
            Term::Rec(n, ls) => Rc::new(Term::Rec(n.clone(), ls.clone())),
            Term::Fix(ty, body) => Rc::new(Term::Fix(ty.shift(c, d), body.shift(c + 1, d))),
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
            Term::App(f, a, label) => {
                Rc::new(Term::App(f.subst(k, s), a.subst(k, s), label.clone()))
            }
            Term::Lam(ty, body, info, kind) => Rc::new(Term::Lam(
                ty.subst(k, s),
                body.subst(k + 1, &s.shift(0, 1)),
                *info,
                *kind,
            )),
            Term::Pi(ty, body, info, kind) => Rc::new(Term::Pi(
                ty.subst(k, s),
                body.subst(k + 1, &s.shift(0, 1)),
                *info,
                *kind,
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
            Term::Fix(ty, body) => {
                Rc::new(Term::Fix(ty.subst(k, s), body.subst(k + 1, &s.shift(0, 1))))
            }
            Term::Meta(id) => Rc::new(Term::Meta(*id)),
        }
    }
}
