use crate::ast::{
    is_reserved_core_name, is_reserved_marker_name, is_reserved_primitive_name,
    level_is_never_zero, marker_name, AxiomTag, BinderInfo, Constructor, CopyInstance,
    CopyInstanceSource, Definition, DefinitionKind, FunctionKind, InductiveDecl, Level, Term,
    Totality, Transparency, TypeMarker,
};
use crate::nbe;
use crate::ownership::{CaptureModes, DefCaptureModeMap, OwnershipError, UsageContext, UsageMode};
use crate::DefId;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;
use thiserror::Error;

type TotalDefWithHint = (String, Rc<Term>, Rc<Term>, Option<usize>);
type RefLabelMismatch = (Option<String>, Option<String>);

#[derive(Debug, Clone, Default)]
pub struct DefEqFuelDetail {
    pub last_event: Option<String>,
    pub recent_defs: Vec<String>,
}

impl DefEqFuelDetail {
    fn from_nbe(info: &nbe::FuelExhaustion) -> Self {
        Self {
            last_event: info.last_event_label(),
            recent_defs: info.recent_definitions().to_vec(),
        }
    }

    fn summary(&self) -> Option<String> {
        let mut parts = Vec::new();
        if let Some(last_event) = &self.last_event {
            parts.push(format!("last step: {}", last_event));
        }
        if !self.recent_defs.is_empty() {
            parts.push(format!("defs: {}", self.recent_defs.join(", ")));
        }
        if parts.is_empty() {
            None
        } else {
            Some(parts.join(", "))
        }
    }
}

#[derive(Debug, Clone)]
pub enum DefEqFuelContext {
    Unknown,
    DefEq {
        left: Rc<Term>,
        right: Rc<Term>,
        transparency: Transparency,
        fuel: usize,
        fuel_detail: Option<DefEqFuelDetail>,
    },
    DefEqInCtx {
        left: Rc<Term>,
        right: Rc<Term>,
        transparency: Transparency,
        ctx_len: usize,
        fuel: usize,
        fuel_detail: Option<DefEqFuelDetail>,
    },
}

impl DefEqFuelContext {
    pub fn fuel(&self) -> Option<usize> {
        match self {
            DefEqFuelContext::Unknown => None,
            DefEqFuelContext::DefEq { fuel, .. } => Some(*fuel),
            DefEqFuelContext::DefEqInCtx { fuel, .. } => Some(*fuel),
        }
    }

    pub fn diagnostic_detail(&self) -> Option<String> {
        match self {
            DefEqFuelContext::Unknown => None,
            DefEqFuelContext::DefEq {
                left,
                right,
                transparency,
                fuel,
                fuel_detail,
            } => Some(format!(
                "comparing {:?} and {:?} (transparency: {:?}, fuel: {}{})",
                left,
                right,
                transparency,
                fuel,
                format_fuel_detail_suffix(fuel_detail)
            )),
            DefEqFuelContext::DefEqInCtx {
                left,
                right,
                transparency,
                ctx_len,
                fuel,
                fuel_detail,
            } => Some(format!(
                "comparing {:?} and {:?} in context (len = {}) (transparency: {:?}, fuel: {}{})",
                left,
                right,
                ctx_len,
                transparency,
                fuel,
                format_fuel_detail_suffix(fuel_detail)
            )),
        }
    }

    fn with_fuel_detail(mut self, detail: DefEqFuelDetail) -> Self {
        match &mut self {
            DefEqFuelContext::DefEq { fuel_detail, .. }
            | DefEqFuelContext::DefEqInCtx { fuel_detail, .. } => {
                *fuel_detail = Some(detail);
            }
            DefEqFuelContext::Unknown => {}
        }
        self
    }
}

impl std::fmt::Display for DefEqFuelContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DefEqFuelContext::Unknown => Ok(()),
            DefEqFuelContext::DefEq {
                left,
                right,
                transparency,
                fuel,
                fuel_detail,
            } => write!(
                f,
                " while comparing {:?} and {:?} (transparency: {:?}, fuel: {}{})",
                left,
                right,
                transparency,
                fuel,
                format_fuel_detail_suffix(fuel_detail)
            ),
            DefEqFuelContext::DefEqInCtx {
                left,
                right,
                transparency,
                ctx_len,
                fuel,
                fuel_detail,
            } => write!(
                f,
                " while comparing {:?} and {:?} in context (len = {}) (transparency: {:?}, fuel: {}{})",
                left,
                right,
                ctx_len,
                transparency,
                fuel,
                format_fuel_detail_suffix(fuel_detail)
            ),
        }
    }
}

fn format_fuel_detail_suffix(fuel_detail: &Option<DefEqFuelDetail>) -> String {
    match fuel_detail.as_ref().and_then(DefEqFuelDetail::summary) {
        Some(summary) => format!(", {}", summary),
        None => String::new(),
    }
}

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
    #[error("Unknown Const: {0}")]
    UnknownConst(String),
    #[error("Reserved primitive name cannot be defined: {0}")]
    ReservedPrimitiveName(String),
    #[error("Reserved primitive '{0}' must use the standard prelude signature")]
    ReservedPrimitiveSignature(String),
    #[error("Reserved marker name cannot be defined: {0}")]
    ReservedMarkerName(String),
    #[error("Reserved marker '{0}' must use the standard marker signature")]
    ReservedMarkerSignature(String),
    #[error("Reserved core name cannot be defined: {0}")]
    ReservedCoreName(String),
    #[error("Definition already exists: {0}")]
    DefinitionAlreadyExists(String),
    #[error("Inductive already exists: {0}")]
    InductiveAlreadyExists(String),
    #[error("Non-strictly positive occurrence of {0} in constructor {1} argument {2}")]
    NonPositiveOccurrence(String, String, usize),
    #[error(
        "Non-positive occurrence of {ind} in argument {arg} of the result type of constructor {ctor}: the result type of a constructor may not mention the inductive being declared in its parameters or indices"
    )]
    InductiveInCtorResultArg {
        ind: String,
        ctor: String,
        arg: usize,
    },
    #[error(
        "Nested inductive occurrence of {ind} in constructor {ctor} field {field} is not supported"
    )]
    NestedInductive {
        ind: String,
        ctor: String,
        field: usize,
    },
    #[error("Universe level too small: Inductive {0} is {1}, but constructor {2} argument is {3}")]
    UniverseLevelTooSmall(String, String, String, String),
    #[error("Non-terminating recursion in definition {0}: recursive call not on structurally smaller argument")]
    NonTerminating(String),
    #[error("Termination check failed in {def_name}: {details}")]
    TerminationError {
        def_name: String,
        details: TerminationErrorDetails,
    },
    #[error("Partial definition {0} used in type context")]
    PartialInType(String),
    #[error("Ownership violation: {0}")]
    OwnershipError(#[from] OwnershipError),
    #[error("Effect violation: {0} definition calls {1} definition {2}")]
    EffectError(String, String, String),
    #[error(
        "Definition {name} depends on {kinds} axioms: {axioms:?}. Mark it noncomputable or unsafe"
    )]
    AxiomDependencyRequiresNoncomputable {
        name: String,
        kinds: String,
        axioms: Vec<String>,
    },
    #[error("Partial definition {name} must return Comp A, got {ty:?}")]
    PartialReturnType { name: String, ty: Rc<Term> },
    #[error("Well-founded definition {0} is missing well-foundedness info")]
    MissingWellFoundedInfo(String),
    #[error("Well-founded definition {name} has invalid decreasing argument index {index}")]
    InvalidWellFoundedDecreasingArg { name: String, index: usize },
    #[error("Large elimination from Prop inductive {0} to Type is not allowed (note: Prop classification does not unfold `opaque` aliases unless explicitly enabled)")]
    LargeElimination(String),
    #[error("Inductive {ind} constructor {ctor} field {field} is in Prop (note: Prop classification does not unfold `opaque` aliases unless explicitly enabled)")]
    PropFieldInData {
        ind: String,
        ctor: String,
        field: usize,
    },
    #[error("Cannot derive Copy for inductive {ind}: {reason}")]
    CopyDeriveFailure { ind: String, reason: String },
    #[error("Explicit Copy instance for inductive {ind} requires unsafe")]
    ExplicitCopyInstanceRequiresUnsafe { ind: String },
    #[error("Explicit Copy instance for interior-mutable inductive {ind} is not allowed")]
    ExplicitCopyInstanceInteriorMutable { ind: String },
    #[error("Type marker '{0}' is missing from the environment")]
    MissingTypeMarkerDefinition(String),
    #[error("Capture annotation for {def_name} refers to unknown closure {closure_id}")]
    UnknownCaptureAnnotation { def_name: String, closure_id: u64 },
    #[error(
        "Capture annotation for {def_name} closure {closure_id} references non-free var {index}"
    )]
    InvalidCaptureAnnotation {
        def_name: String,
        closure_id: u64,
        index: usize,
    },
    #[error("Type marker '{0}' must be defined as an unsafe axiom")]
    InvalidTypeMarkerDefinition(String),
    #[error("Marker registry has not been initialized")]
    MarkerRegistryUninitialized,
    #[error("Marker registry is already initialized")]
    MarkerRegistryAlreadyInitialized,
    #[error("Unknown marker id {0}")]
    UnknownMarkerId(u64),
    #[error("Recursor for inductive {0} requires an explicit universe level")]
    MissingRecursorLevel(String),
    #[error("Recursor for inductive {ind} expects {expected} universe levels, got {got}")]
    RecursorLevelCount {
        ind: String,
        expected: usize,
        got: usize,
    },
    #[error("Constructor {ctor} does not return inductive {ind}")]
    CtorNotReturningInductive { ind: String, ctor: String },
    #[error("Constructor {ctor} for inductive {ind} returns {got} arguments, expected {expected}")]
    CtorArityMismatch {
        ind: String,
        ctor: String,
        expected: usize,
        got: usize,
    },
    #[error("Annotated function kind {annotated:?} is too small; requires {required:?}")]
    FunctionKindTooSmall {
        annotated: FunctionKind,
        required: FunctionKind,
    },
    #[error("Lifetime labels may only annotate Ref Shared/Mut applications, got {term:?}")]
    InvalidRefLifetimeLabel { term: Rc<Term> },
    #[error("Ambiguous lifetime in return type; add explicit Ref #[label] annotations")]
    AmbiguousRefLifetime,
    #[error("Ref lifetime label mismatch: expected {expected_label}, got {got_label}")]
    RefLifetimeLabelMismatch {
        expected_label: String,
        got_label: String,
        expected: Rc<Term>,
        got: Rc<Term>,
    },
    #[error("Unresolved metavariable ?{0}")]
    UnresolvedMeta(usize),
    #[error("Definitional equality fuel exhausted{context}")]
    DefEqFuelExhausted { context: DefEqFuelContext },
    #[error("Definitional equality cannot unfold `fix` (general recursion)")]
    DefEqFixUnfold,
    #[error("NbE application of non-function value")]
    NbeNonFunctionApplication,
    #[error("Not implemented")]
    NotImplemented,
    #[error("Inductive {ind} is marked affine and cannot be Copy (declared copy, given an explicit Copy instance, or a proposition)")]
    AffineCopyConflict { ind: String },
    #[error("Definition {name} has no value: only an axiom may be declared without a value (totality {totality:?})")]
    MissingDefinitionValue { name: String, totality: Totality },
    #[error("Cannot redefine {name}: {dependents:?} refer to it and were checked against its current meaning")]
    RedefinitionWithDependents {
        name: String,
        dependents: Vec<String>,
    },
    #[error("A fixpoint may not return a proof: its type ends in the proposition {codomain:?} (proofs are erased, so a looping fixpoint would stand for a proof that does not exist)")]
    FixProofCodomain { codomain: Rc<Term> },
    #[error("Normalization exceeded the evaluation depth limit ({limit} nested steps); the kernel cannot decide this")]
    NormalizationDepthExceeded { limit: usize },
}

impl TypeError {
    pub fn diagnostic_code(&self) -> &'static str {
        match self {
            TypeError::UnknownVariable(_) => "K0001",
            TypeError::TypeMismatch { .. } => "K0002",
            TypeError::ExpectedFunction(_) => "K0003",
            TypeError::ExpectedSort(_) => "K0004",
            TypeError::UnknownInductive(_) => "K0005",
            TypeError::UnknownConstructor(_, _) => "K0006",
            TypeError::UnknownConst(_) => "K0007",
            TypeError::ReservedPrimitiveName(_) => "K0008",
            TypeError::ReservedPrimitiveSignature(_) => "K0009",
            TypeError::ReservedMarkerName(_) => "K0010",
            TypeError::ReservedMarkerSignature(_) => "K0011",
            TypeError::ReservedCoreName(_) => "K0012",
            TypeError::DefinitionAlreadyExists(_) => "K0013",
            TypeError::InductiveAlreadyExists(_) => "K0014",
            TypeError::NonPositiveOccurrence(_, _, _) => "K0015",
            TypeError::InductiveInCtorResultArg { .. } => "K0015",
            TypeError::NestedInductive { .. } => "K0016",
            TypeError::UniverseLevelTooSmall(_, _, _, _) => "K0017",
            TypeError::NonTerminating(_) => "K0018",
            TypeError::TerminationError { .. } => "K0019",
            TypeError::PartialInType(_) => "K0020",
            TypeError::OwnershipError(_) => "K0021",
            TypeError::EffectError(_, _, _) => "K0022",
            TypeError::AxiomDependencyRequiresNoncomputable { .. } => "K0023",
            TypeError::PartialReturnType { .. } => "K0024",
            TypeError::MissingWellFoundedInfo(_) => "K0025",
            TypeError::InvalidWellFoundedDecreasingArg { .. } => "K0026",
            TypeError::LargeElimination(_) => "K0027",
            TypeError::PropFieldInData { .. } => "K0028",
            TypeError::CopyDeriveFailure { .. } => "K0029",
            TypeError::ExplicitCopyInstanceRequiresUnsafe { .. } => "K0030",
            TypeError::ExplicitCopyInstanceInteriorMutable { .. } => "K0031",
            TypeError::MissingTypeMarkerDefinition(_) => "K0032",
            TypeError::UnknownCaptureAnnotation { .. } => "K0033",
            TypeError::InvalidCaptureAnnotation { .. } => "K0034",
            TypeError::InvalidTypeMarkerDefinition(_) => "K0035",
            TypeError::MarkerRegistryUninitialized => "K0036",
            TypeError::MarkerRegistryAlreadyInitialized => "K0037",
            TypeError::UnknownMarkerId(_) => "K0038",
            TypeError::MissingRecursorLevel(_) => "K0039",
            TypeError::RecursorLevelCount { .. } => "K0040",
            TypeError::CtorNotReturningInductive { .. } => "K0041",
            TypeError::CtorArityMismatch { .. } => "K0042",
            TypeError::FunctionKindTooSmall { .. } => "K0043",
            TypeError::InvalidRefLifetimeLabel { .. } => "K0044",
            TypeError::AmbiguousRefLifetime => "K0045",
            TypeError::RefLifetimeLabelMismatch { .. } => "K0046",
            TypeError::UnresolvedMeta(_) => "K0047",
            TypeError::DefEqFuelExhausted { .. } => "K0048",
            TypeError::DefEqFixUnfold => "K0049",
            TypeError::NbeNonFunctionApplication => "K0050",
            TypeError::NotImplemented => "K0051",
            TypeError::AffineCopyConflict { .. } => "K0052",
            TypeError::MissingDefinitionValue { .. } => "K0053",
            TypeError::RedefinitionWithDependents { .. } => "K0054",
            TypeError::FixProofCodomain { .. } => "K0055",
            TypeError::NormalizationDepthExceeded { .. } => "K0056",
        }
    }
}

/// Detailed information about termination check failures
#[derive(Debug, Clone)]
pub enum TerminationErrorDetails {
    /// Recursive call with non-smaller argument
    NonSmallerArgument {
        /// The argument that should have been smaller
        arg_term: Rc<Term>,
        /// Position of the decreasing argument
        arg_position: usize,
        /// Variables that were known to be smaller at this point
        smaller_vars: Vec<usize>,
    },
    /// No inductive argument found for recursion
    NoDecreasingArgument,
    /// Decreasing argument hint is invalid (not an inductive parameter)
    InvalidDecreasingArgument {
        /// Position of the requested decreasing argument
        arg_position: usize,
    },
    /// Recursive call in non-decreasing position (e.g., as a type argument)
    RecursiveCallInType,
    /// Recursive reference without application
    BareRecursiveReference,
    /// Recursive call that does not supply the decreasing argument (a partial application of
    /// the function could later be applied to any value)
    MissingDecreasingArgument {
        /// Position of the decreasing argument
        arg_position: usize,
        /// Number of arguments the call supplies
        supplied: usize,
    },
    /// Mutual recursion detected but not all functions decrease
    MutualRecursionError {
        /// Functions involved in the mutual recursion
        functions: Vec<String>,
    },
    /// General recursion without structural decrease
    GeneralRecursion,
    /// Well-founded recursion violation
    WellFoundedError(WellFoundedError),
}

impl std::fmt::Display for TerminationErrorDetails {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TerminationErrorDetails::NonSmallerArgument {
                arg_term,
                arg_position,
                smaller_vars,
            } => {
                write!(
                    f,
                    "recursive call at argument position {} is not structurally smaller. ",
                    arg_position
                )?;
                write!(f, "Argument: {:?}. ", arg_term)?;
                if smaller_vars.is_empty() {
                    write!(f, "No variables are known to be smaller at this point.")
                } else {
                    write!(f, "Variables known to be smaller: {:?}", smaller_vars)
                }
            }
            TerminationErrorDetails::NoDecreasingArgument => {
                write!(f, "no decreasing argument found for structural recursion")
            }
            TerminationErrorDetails::InvalidDecreasingArgument { arg_position } => {
                write!(
                    f,
                    "invalid decreasing argument hint at position {}",
                    arg_position
                )
            }
            TerminationErrorDetails::RecursiveCallInType => {
                write!(f, "recursive call appears in type position")
            }
            TerminationErrorDetails::BareRecursiveReference => {
                write!(f, "recursive reference appears without application")
            }
            TerminationErrorDetails::MissingDecreasingArgument {
                arg_position,
                supplied,
            } => {
                write!(
                    f,
                    "recursive call supplies {} argument(s), so the decreasing argument at position {} is not given",
                    supplied, arg_position
                )
            }
            TerminationErrorDetails::MutualRecursionError { functions } => {
                write!(
                    f,
                    "mutual recursion between {} does not decrease",
                    functions.join(", ")
                )
            }
            TerminationErrorDetails::GeneralRecursion => {
                write!(f, "general recursion detected without structural decrease")
            }
            TerminationErrorDetails::WellFoundedError(err) => {
                write!(f, "well-founded recursion check failed: {}", err)
            }
        }
    }
}

#[derive(Clone)]
pub struct Context {
    types: Vec<Rc<Term>>,
}

impl Context {
    pub fn new() -> Self {
        Context { types: Vec::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }

    pub fn push(&self, ty: Rc<Term>) -> Self {
        let mut types = self.types.clone();
        types.push(ty);
        Context { types }
    }

    pub fn len(&self) -> usize {
        self.types.len()
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

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

/// Global environment containing inductive definitions and constants
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Builtin {
    Nat,
    Bool,
    List,
}

#[derive(Clone)]
pub struct MarkerRegistry {
    initialized: bool,
    interior_mutable: Option<crate::ast::MarkerId>,
    may_panic_on_borrow_violation: Option<crate::ast::MarkerId>,
    concurrency_primitive: Option<crate::ast::MarkerId>,
    atomic_primitive: Option<crate::ast::MarkerId>,
    indexable: Option<crate::ast::MarkerId>,
    affine: Option<crate::ast::MarkerId>,
}

impl MarkerRegistry {
    fn new() -> Self {
        MarkerRegistry {
            initialized: false,
            interior_mutable: None,
            may_panic_on_borrow_violation: None,
            concurrency_primitive: None,
            atomic_primitive: None,
            indexable: None,
            affine: None,
        }
    }

    fn ensure_initialized(&self) -> Result<(), TypeError> {
        if self.initialized {
            Ok(())
        } else {
            Err(TypeError::MarkerRegistryUninitialized)
        }
    }

    fn set_marker(&mut self, marker: TypeMarker, id: crate::ast::MarkerId) {
        match marker {
            TypeMarker::InteriorMutable => self.interior_mutable = Some(id),
            TypeMarker::MayPanicOnBorrowViolation => self.may_panic_on_borrow_violation = Some(id),
            TypeMarker::ConcurrencyPrimitive => self.concurrency_primitive = Some(id),
            TypeMarker::AtomicPrimitive => self.atomic_primitive = Some(id),
            TypeMarker::Indexable => self.indexable = Some(id),
            TypeMarker::Affine => self.affine = Some(id),
        }
    }

    fn id_for(&self, marker: TypeMarker) -> Result<crate::ast::MarkerId, TypeError> {
        self.ensure_initialized()?;
        let id = match marker {
            TypeMarker::InteriorMutable => self.interior_mutable,
            TypeMarker::MayPanicOnBorrowViolation => self.may_panic_on_borrow_violation,
            TypeMarker::ConcurrencyPrimitive => self.concurrency_primitive,
            TypeMarker::AtomicPrimitive => self.atomic_primitive,
            TypeMarker::Indexable => self.indexable,
            TypeMarker::Affine => self.affine,
        };
        id.ok_or(TypeError::MarkerRegistryUninitialized)
    }

    fn has_marker(
        &self,
        markers: &[crate::ast::MarkerId],
        marker: TypeMarker,
    ) -> Result<bool, TypeError> {
        if markers.is_empty() {
            return Ok(false);
        }
        let id = self.id_for(marker)?;
        Ok(markers.contains(&id))
    }

    fn validate_marker_ids(&self, markers: &[crate::ast::MarkerId]) -> Result<(), TypeError> {
        if markers.is_empty() {
            return Ok(());
        }
        self.ensure_initialized()?;
        for marker_id in markers {
            if !self.is_known_id(*marker_id) {
                return Err(TypeError::UnknownMarkerId(marker_id.0));
            }
        }
        Ok(())
    }

    fn is_known_id(&self, id: crate::ast::MarkerId) -> bool {
        Some(id) == self.interior_mutable
            || Some(id) == self.may_panic_on_borrow_violation
            || Some(id) == self.concurrency_primitive
            || Some(id) == self.atomic_primitive
            || Some(id) == self.indexable
            || Some(id) == self.affine
    }
}

#[derive(Clone)]
pub struct Env {
    definitions: HashMap<String, Definition>,
    pub inductives: HashMap<String, InductiveDecl>,
    pub axioms: HashMap<String, Rc<Term>>,
    extra_axiom_tags: HashMap<String, Vec<AxiomTag>>,
    axiom_tag_snapshot: HashMap<String, Vec<AxiomTag>>,
    pub known_inductives: HashMap<Builtin, String>,
    allow_reserved_primitives: bool,
    allow_redefinition: bool,
    copy_instances: HashMap<String, Vec<crate::ast::CopyInstance>>,
    marker_registry: MarkerRegistry,
    constructor_index: BTreeMap<String, Vec<ConstructorRef>>,
    /// Total definitions whose value refers to the definition itself (structural recursion
    /// through a constant; kernel API, or a redefinition under `allow_redefinition`). Their δ
    /// unfolding is guarded by the decreasing argument (see `nbe::guarded_rec_arg`).
    self_recursive: HashSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstructorRef {
    pub ind_name: String,
    pub index: usize,
}

#[derive(Debug, Clone)]
pub struct InductiveInfo {
    pub name: String,
    pub recursor: RecursorInfo,
}

#[derive(Debug, Clone)]
pub struct RecursorInfo {
    pub num_params: usize,
    pub num_indices: usize,
    pub num_ctors: usize,
    pub expected_args: usize,
    pub ctor_infos: Vec<RecursorCtorInfo>,
}

#[derive(Debug, Clone)]
pub struct RecursorCtorInfo {
    pub name: String,
    pub arity: usize,
    pub rec_indices: Vec<Option<Vec<Rc<Term>>>>,
}

impl RecursorInfo {
    pub fn major_index(&self) -> usize {
        self.num_params + 1 + self.num_ctors + self.num_indices
    }

    pub fn minor_index(&self, ctor_idx: usize) -> Option<usize> {
        if ctor_idx < self.num_ctors {
            Some(self.num_params + 1 + ctor_idx)
        } else {
            None
        }
    }
}

impl InductiveInfo {
    fn from_decl(decl: &InductiveDecl) -> Self {
        let num_params = decl.num_params;
        let total_binders = count_pi_binders(&decl.ty);
        let num_indices = total_binders.saturating_sub(num_params);
        let num_ctors = decl.ctors.len();
        let expected_args = num_params + 1 + num_ctors + num_indices + 1;

        let ctor_infos = decl
            .ctors
            .iter()
            .map(|ctor| {
                let (binders, _) = extract_pi_binders(&ctor.ty);
                let binder_tys: Vec<Rc<Term>> = binders.into_iter().map(|(ty, _)| ty).collect();
                let arity = binder_tys.len();
                let rec_indices = extract_ctor_rec_indices(&binder_tys, &decl.name, num_params);
                RecursorCtorInfo {
                    name: ctor.name.clone(),
                    arity,
                    rec_indices,
                }
            })
            .collect();

        InductiveInfo {
            name: decl.name.clone(),
            recursor: RecursorInfo {
                num_params,
                num_indices,
                num_ctors,
                expected_args,
                ctor_infos,
            },
        }
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl Env {
    pub fn new() -> Self {
        Env {
            definitions: HashMap::new(),
            inductives: HashMap::new(),
            axioms: HashMap::new(),
            extra_axiom_tags: HashMap::new(),
            axiom_tag_snapshot: HashMap::new(),
            known_inductives: HashMap::new(),
            allow_reserved_primitives: false,
            allow_redefinition: false,
            copy_instances: HashMap::new(),
            marker_registry: MarkerRegistry::new(),
            constructor_index: BTreeMap::new(),
            self_recursive: HashSet::new(),
        }
    }

    /// Whether the total definition `name` refers to itself (recursion through its own constant).
    pub fn is_self_recursive(&self, name: &str) -> bool {
        self.self_recursive.contains(name)
    }

    pub fn set_allow_reserved_primitives(&mut self, allow: bool) {
        self.allow_reserved_primitives = allow;
    }

    pub fn allows_reserved_primitives(&self) -> bool {
        self.allow_reserved_primitives
    }

    pub fn set_allow_redefinition(&mut self, allow: bool) {
        self.allow_redefinition = allow;
    }

    pub fn allows_redefinition(&self) -> bool {
        self.allow_redefinition
    }

    fn snapshot_axiom_tags(&mut self, axiom_name: &str, tags: &[AxiomTag]) {
        if tags.is_empty() {
            return;
        }
        let entry = self
            .axiom_tag_snapshot
            .entry(axiom_name.to_string())
            .or_default();
        for tag in tags {
            if !entry.contains(tag) {
                entry.push(*tag);
            }
        }
        entry.sort();
        entry.dedup();
    }

    pub fn definitions(&self) -> &HashMap<String, Definition> {
        &self.definitions
    }

    pub fn marker_registry(&self) -> &MarkerRegistry {
        &self.marker_registry
    }

    pub fn has_marker(
        &self,
        markers: &[crate::ast::MarkerId],
        marker: TypeMarker,
    ) -> Result<bool, TypeError> {
        self.marker_registry.has_marker(markers, marker)
    }

    pub fn init_marker_registry(&mut self) -> Result<(), TypeError> {
        if self.marker_registry.initialized {
            return Ok(());
        }

        let markers = [
            TypeMarker::InteriorMutable,
            TypeMarker::MayPanicOnBorrowViolation,
            TypeMarker::ConcurrencyPrimitive,
            TypeMarker::AtomicPrimitive,
            TypeMarker::Indexable,
        ];

        for marker in markers {
            let name = crate::ast::marker_name(marker);
            let def = self
                .get_definition(name)
                .ok_or_else(|| TypeError::MissingTypeMarkerDefinition(name.to_string()))?;
            if def.totality != Totality::Axiom
                || def.value.is_some()
                || !def.axiom_tags.contains(&AxiomTag::Unsafe)
                || !marker_signature_ok(&def.ty)
            {
                return Err(TypeError::InvalidTypeMarkerDefinition(name.to_string()));
            }
            self.marker_registry
                .set_marker(marker, crate::ast::marker_def_id(marker));
        }
        // `affine` is built into the kernel: it only restricts Copy, so it needs no trusted
        // marker definition.
        self.marker_registry.set_marker(
            TypeMarker::Affine,
            crate::ast::marker_def_id(TypeMarker::Affine),
        );

        self.marker_registry.initialized = true;
        Ok(())
    }

    /// The Copy instances registered for each inductive. Read-only: instances are added only by
    /// [`Env::add_copy_instance`] (checked) and by the kernel's own derivation when an inductive
    /// is declared.
    pub fn copy_instances(&self) -> &HashMap<String, Vec<CopyInstance>> {
        &self.copy_instances
    }

    /// Register a Copy instance submitted by a client of the kernel API.
    ///
    /// An `Explicit` instance must be `unsafe`, may not target an interior-mutable or `affine`
    /// inductive, and is recorded as the unsafe axiom `copy_instance(T)`. A `Derived` instance is
    /// a conclusion the kernel draws from the declaration's fields, so it is accepted only if it
    /// is exactly the instance the kernel derives itself for the registered declaration (fields
    /// Copy or required Copy, no interior-mutable or `affine` marker); anything else is
    /// `CopyDeriveFailure` (K0029), and an unknown inductive is `UnknownInductive`. (Before, a
    /// `Derived` instance was registered unchecked, so a client could make any type Copy with no
    /// axiom recorded.)
    pub fn add_copy_instance(&mut self, inst: CopyInstance) -> Result<(), TypeError> {
        if matches!(inst.source, CopyInstanceSource::Derived) {
            let decl = self
                .inductives
                .get(&inst.ind_name)
                .cloned()
                .ok_or_else(|| TypeError::UnknownInductive(inst.ind_name.clone()))?;
            let derived = compute_derived_copy_instance(self, &decl).map_err(|reason| {
                TypeError::CopyDeriveFailure {
                    ind: inst.ind_name.clone(),
                    reason,
                }
            })?;
            if derived != inst {
                return Err(TypeError::CopyDeriveFailure {
                    ind: inst.ind_name.clone(),
                    reason:
                        "the submitted derived instance is not the instance the kernel derives \
                             from the declaration"
                            .to_string(),
                });
            }
        }
        if matches!(inst.source, CopyInstanceSource::Explicit) {
            if !inst.is_unsafe {
                return Err(TypeError::ExplicitCopyInstanceRequiresUnsafe {
                    ind: inst.ind_name.clone(),
                });
            }
            if let Some(decl) = self.inductives.get(&inst.ind_name) {
                if self
                    .marker_registry
                    .has_marker(&decl.markers, TypeMarker::InteriorMutable)?
                {
                    return Err(TypeError::ExplicitCopyInstanceInteriorMutable {
                        ind: inst.ind_name.clone(),
                    });
                }
                if self
                    .marker_registry
                    .has_marker(&decl.markers, TypeMarker::Affine)?
                {
                    return Err(TypeError::AffineCopyConflict {
                        ind: inst.ind_name.clone(),
                    });
                }
            } else {
                return Err(TypeError::UnknownInductive(inst.ind_name.clone()));
            }
            self.register_copy_instance_axiom(&inst.ind_name);
            self.refresh_axiom_dependencies();
        }

        self.push_copy_instance(inst);
        Ok(())
    }

    /// Store an already-checked Copy instance.
    fn push_copy_instance(&mut self, inst: CopyInstance) {
        let entry = self
            .copy_instances
            .entry(inst.ind_name.clone())
            .or_default();
        // Prefer explicit instances over derived ones.
        if matches!(inst.source, CopyInstanceSource::Explicit) {
            entry.insert(0, inst);
        } else {
            entry.push(inst);
        }
    }

    fn register_copy_instance_axiom(&mut self, ind_name: &str) {
        let axiom_name = copy_instance_axiom_name(ind_name);

        let entry = self.extra_axiom_tags.entry(axiom_name.clone()).or_default();
        if !entry.contains(&AxiomTag::Unsafe) {
            entry.push(AxiomTag::Unsafe);
        }
        entry.sort();
        entry.dedup();
        self.snapshot_axiom_tags(&axiom_name, &[AxiomTag::Unsafe]);

        if let Some(decl) = self.inductives.get_mut(ind_name) {
            if !decl.axioms.contains(&axiom_name) {
                decl.axioms.push(axiom_name);
                decl.axioms.sort();
                decl.axioms.dedup();
            }
        }
    }

    fn refresh_axiom_dependencies(&mut self) {
        let mut inductive_names: Vec<String> = self.inductives.keys().cloned().collect();
        inductive_names.sort();
        let mut def_names: Vec<String> = self.definitions.keys().cloned().collect();
        def_names.sort();

        let mut changed = true;
        while changed {
            changed = false;

            let mut inductive_updates: Vec<(String, Vec<String>, Vec<String>)> = Vec::new();
            for name in &inductive_names {
                let (ty, ctors, base_axioms, base_primitives) = match self.inductives.get(name) {
                    Some(decl) => (
                        decl.ty.clone(),
                        decl.ctors.clone(),
                        decl.axioms.clone(),
                        decl.primitive_deps.clone(),
                    ),
                    None => continue,
                };
                let mut used_axioms = HashSet::new();
                let mut used_primitives = HashSet::new();
                for ax in &base_axioms {
                    used_axioms.insert(ax.clone());
                }
                for prim in &base_primitives {
                    used_primitives.insert(prim.clone());
                }
                collect_axioms_rec(self, &ty, &mut used_axioms, &mut used_primitives);
                for ctor in &ctors {
                    collect_axioms_rec(self, &ctor.ty, &mut used_axioms, &mut used_primitives);
                }
                let mut axioms: Vec<String> = used_axioms.into_iter().collect();
                axioms.sort();
                let mut primitives: Vec<String> = used_primitives.into_iter().collect();
                primitives.sort();
                inductive_updates.push((name.clone(), axioms, primitives));
            }

            let mut def_updates: Vec<(String, Vec<String>, Vec<String>)> = Vec::new();
            for name in &def_names {
                let (ty, val, base_axioms, base_primitives) = match self.definitions.get(name) {
                    Some(def) => (
                        def.ty.clone(),
                        def.value.clone(),
                        def.axioms.clone(),
                        def.primitive_deps.clone(),
                    ),
                    None => continue,
                };
                let mut used_axioms = HashSet::new();
                let mut used_primitives = HashSet::new();
                for ax in &base_axioms {
                    used_axioms.insert(ax.clone());
                }
                for prim in &base_primitives {
                    used_primitives.insert(prim.clone());
                }
                collect_axioms_rec(self, &ty, &mut used_axioms, &mut used_primitives);
                if let Some(val) = val {
                    collect_axioms_rec(self, &val, &mut used_axioms, &mut used_primitives);
                }
                let mut axioms: Vec<String> = used_axioms.into_iter().collect();
                axioms.sort();
                let mut primitives: Vec<String> = used_primitives.into_iter().collect();
                primitives.sort();
                def_updates.push((name.clone(), axioms, primitives));
            }

            for (name, axioms, primitives) in inductive_updates {
                if let Some(decl) = self.inductives.get_mut(&name) {
                    if decl.axioms != axioms || decl.primitive_deps != primitives {
                        decl.axioms = axioms;
                        decl.primitive_deps = primitives;
                        changed = true;
                    }
                }
            }

            for (name, axioms, primitives) in def_updates {
                if let Some(def) = self.definitions.get_mut(&name) {
                    if def.axioms != axioms || def.primitive_deps != primitives {
                        def.axioms = axioms;
                        def.primitive_deps = primitives;
                        changed = true;
                    }
                }
            }
        }
    }

    /// The other definitions and inductives whose stored terms (type, value, constructor types)
    /// refer to the definition `name`, sorted.
    ///
    /// Under `allow_redefinition` (CLI `--allow-redefine`) a name may be given a new meaning, but
    /// only while nothing refers to it: every entry was checked against the meaning its
    /// references had at the time, and the kernel neither re-checks nor invalidates entries
    /// afterwards. Replacing a referenced name would keep entries that no longer check — a proof
    /// `p : Eq Nat zero c` made with `c := zero` would prove `Eq Nat zero (succ zero)` after
    /// `c := succ zero` (δ uses the current body), and a value of an inductive that is then
    /// redeclared empty would inhabit the empty type, both closed proofs of `False` without an
    /// axiom; axiom and effect information recorded for dependents would also go stale.
    fn dependents_of_definition(&self, name: &str) -> Vec<String> {
        self.dependents_where(name, &|t| {
            term_mentions(t, &|node| matches!(node, Term::Const(n, _) if n == name))
        })
    }

    /// Like [`Env::dependents_of_definition`], for the inductive `name` (its type, constructors
    /// and recursor).
    fn dependents_of_inductive(&self, name: &str) -> Vec<String> {
        self.dependents_where(name, &|t| {
            term_mentions(t, &|node| match node {
                Term::Ind(n, _) | Term::Rec(n, _) | Term::Ctor(n, _, _) => n == name,
                _ => false,
            })
        })
    }

    fn dependents_where(&self, name: &str, refers: &dyn Fn(&Rc<Term>) -> bool) -> Vec<String> {
        let mut dependents: Vec<String> = Vec::new();
        for (def_name, def) in &self.definitions {
            if def_name == name {
                continue;
            }
            if refers(&def.ty) || def.value.as_ref().is_some_and(refers) {
                dependents.push(def_name.clone());
            }
        }
        for (ind_name, decl) in &self.inductives {
            if ind_name == name {
                continue;
            }
            if refers(&decl.ty) || decl.ctors.iter().any(|ctor| refers(&ctor.ty)) {
                dependents.push(ind_name.clone());
            }
        }
        dependents.sort();
        dependents.dedup();
        dependents
    }

    /// Register an inductive type definition
    pub fn add_inductive(&mut self, mut decl: InductiveDecl) -> Result<(), TypeError> {
        if is_reserved_primitive_name(&decl.name) {
            return Err(TypeError::ReservedPrimitiveName(decl.name));
        }
        if is_reserved_core_name(&decl.name)
            && !self.allow_reserved_primitives
            && !self.allow_redefinition
        {
            return Err(TypeError::ReservedCoreName(decl.name));
        }
        if self.inductives.contains_key(&decl.name) {
            if !self.allow_redefinition {
                return Err(TypeError::InductiveAlreadyExists(decl.name));
            }
            // Redeclaration (`allow_redefinition`): nothing that was checked against the old
            // declaration may survive it (see `dependents_of_inductive`).
            let dependents = self.dependents_of_inductive(&decl.name);
            if !dependents.is_empty() {
                return Err(TypeError::RedefinitionWithDependents {
                    name: decl.name.clone(),
                    dependents,
                });
            }
        }
        // Validate core invariants early (no metas, explicit recursor levels, etc.)
        validate_core_term(&decl.ty)?;
        for ctor in &decl.ctors {
            validate_core_term(&ctor.ty)?;
        }
        // The arity and the constructor types are read syntactically from here on (parameter
        // inference, strict positivity, nested occurrences, recursive arguments of the recursor
        // and of ι-reduction, Copy derivation, MIR lowering). Expand every `let` first (zeta is
        // definitional, so the declaration means the same) so that a let-bound variable cannot
        // hide an occurrence of the inductive from these checks.
        decl.ty = zeta_expand(&decl.ty);
        for ctor in &mut decl.ctors {
            ctor.ty = zeta_expand(&ctor.ty);
        }
        validate_marker_definitions(self, &decl.markers)?;
        if decl.is_copy && self.has_marker(&decl.markers, TypeMarker::Affine)? {
            return Err(TypeError::AffineCopyConflict {
                ind: decl.name.clone(),
            });
        }
        // Proofs are erased at run time and always duplicable, so an `affine` proposition would
        // silently stay Copy: reject the marker on an inductive in `Prop`.
        if self.has_marker(&decl.markers, TypeMarker::Affine)?
            && matches!(
                result_sort_with_transparency(self, &Context::new(), &decl.ty, Transparency::Reducible),
                Ok(Some(level)) if level_is_zero(&level)
            )
        {
            return Err(TypeError::AffineCopyConflict {
                ind: decl.name.clone(),
            });
        }

        if let Some(partial_name) = contains_partial_def(self, &decl.ty) {
            return Err(TypeError::PartialInType(partial_name));
        }
        // Infer parameter count from constructors for consistency with recursors/elimination.
        // If the caller specified params, honor them but don't exceed what constructors support.
        let inferred_params = infer_num_params_from_ctors(&decl)?;
        if decl.num_params == 0 || decl.num_params > inferred_params {
            decl.num_params = inferred_params;
        }

        // Insert a temporary placeholder so the inductive can reference itself
        // during soundness checks (e.g., constructor domains mentioning the type).
        let name = decl.name.clone();
        let placeholder = InductiveDecl {
            ctors: vec![],
            ..decl.clone()
        };
        let previous = self.inductives.insert(name.clone(), placeholder);
        // Copy instances (derived or explicit) belong to the declaration they were checked
        // against. A re-declaration (`allow_redefinition`) starts without them; the new
        // declaration derives its own below. (Keeping them let an `affine` re-declaration stay
        // Copy, so the kernel accepted a duplicated affine value.)
        let previous_copy_instances = self.copy_instances.remove(&name);

        // Every step from here to the final registration can fail. On failure the placeholder
        // must not stay behind: it would be a zero-constructor type of that name that later forms
        // could use, and it would block a corrected re-declaration. Restore the previous entry
        // and its Copy instances.
        if let Err(e) = self.check_and_complete_inductive(&mut decl) {
            match previous {
                Some(prev) => {
                    self.inductives.insert(name.clone(), prev);
                }
                None => {
                    self.inductives.remove(&name);
                }
            }
            self.copy_instances.remove(&name);
            if let Some(instances) = previous_copy_instances {
                self.copy_instances.insert(name.clone(), instances);
            }
            return Err(e);
        }

        if decl.name == "Nat" {
            self.known_inductives
                .insert(Builtin::Nat, decl.name.clone());
        }
        if decl.name == "Bool" {
            self.known_inductives
                .insert(Builtin::Bool, decl.name.clone());
        }
        if decl.name == "List" {
            self.known_inductives
                .insert(Builtin::List, decl.name.clone());
        }
        if let Some(ref prev) = previous {
            self.remove_constructor_index_for(prev);
        }
        self.add_constructor_index_for(&decl);
        self.inductives.insert(decl.name.clone(), decl);
        Ok(())
    }

    /// The fallible part of `add_inductive`, run while the placeholder for `decl` is in the
    /// environment: soundness checks, axiom/primitive dependencies, markers and the Copy
    /// derivation. Completes `decl.axioms` and `decl.primitive_deps`.
    fn check_and_complete_inductive(&mut self, decl: &mut InductiveDecl) -> Result<(), TypeError> {
        check_inductive_soundness(self, decl)?;

        // Compute axiom/primitive dependencies for the inductive (type + constructors).
        let mut used_axioms = HashSet::new();
        let mut used_primitives = HashSet::new();
        for ax in &decl.axioms {
            used_axioms.insert(ax.clone());
        }
        for prim in &decl.primitive_deps {
            used_primitives.insert(prim.clone());
        }
        collect_axioms_rec(self, &decl.ty, &mut used_axioms, &mut used_primitives);
        for ctor in &decl.ctors {
            collect_axioms_rec(self, &ctor.ty, &mut used_axioms, &mut used_primitives);
        }

        // Interior mutability primitives currently rely on unimplemented runtime checks.
        // Treat RefCell/Mutex/Atomic-like markers as unsafe axioms so safe definitions must opt in.
        if !decl.markers.is_empty() {
            self.init_marker_registry()?;
            let has_may_panic =
                self.has_marker(&decl.markers, TypeMarker::MayPanicOnBorrowViolation)?;
            let has_concurrency =
                self.has_marker(&decl.markers, TypeMarker::ConcurrencyPrimitive)?;
            let has_atomic = self.has_marker(&decl.markers, TypeMarker::AtomicPrimitive)?;

            if has_may_panic {
                used_axioms.insert(marker_name(TypeMarker::MayPanicOnBorrowViolation).to_string());
            }
            if has_concurrency && !has_atomic {
                used_axioms.insert(marker_name(TypeMarker::ConcurrencyPrimitive).to_string());
            }
            if has_atomic {
                used_axioms.insert(marker_name(TypeMarker::AtomicPrimitive).to_string());
            }
        }

        decl.axioms = used_axioms.into_iter().collect();
        decl.axioms.sort();
        decl.primitive_deps = used_primitives.into_iter().collect();
        decl.primitive_deps.sort();

        // Auto-derive Copy instance when possible; if explicitly requested, surface failures.
        // (Last fallible step: a derived instance is registered only when derivation succeeds.)
        if let Err(reason) = derive_copy_instance(self, decl) {
            if decl.is_copy {
                return Err(TypeError::CopyDeriveFailure {
                    ind: decl.name.clone(),
                    reason,
                });
            }
        }
        Ok(())
    }

    pub fn register_builtin(&mut self, builtin: Builtin, name: String) {
        self.known_inductives.insert(builtin, name);
    }

    pub fn is_builtin(&self, builtin: Builtin, name: &str) -> bool {
        self.known_inductives
            .get(&builtin)
            .map(|s| s == name)
            .unwrap_or(false)
    }

    /// Register a definition with explicit totality.
    /// Automatically sets `rec_arg` for total definitions based on termination analysis.
    pub fn add_definition(&mut self, mut def: Definition) -> Result<(), TypeError> {
        let is_reserved = is_reserved_primitive_name(&def.name);
        let is_reserved_marker = is_reserved_marker_name(&def.name);
        let is_reserved_core = is_reserved_core_name(&def.name);
        if is_reserved {
            if !self.allow_reserved_primitives || self.definitions.contains_key(&def.name) {
                return Err(TypeError::ReservedPrimitiveName(def.name.clone()));
            }
            if def.totality != Totality::Axiom || def.value.is_some() {
                return Err(TypeError::ReservedPrimitiveName(def.name.clone()));
            }
            if reserved_primitive_requires_unsafe(&def.name)
                && !def.axiom_tags.contains(&AxiomTag::Unsafe)
            {
                return Err(TypeError::ReservedPrimitiveName(def.name.clone()));
            }
        }
        if is_reserved_marker {
            if !self.allow_reserved_primitives || self.definitions.contains_key(&def.name) {
                return Err(TypeError::ReservedMarkerName(def.name.clone()));
            }
            if def.totality != Totality::Axiom || def.value.is_some() {
                return Err(TypeError::ReservedMarkerName(def.name.clone()));
            }
            if !def.axiom_tags.contains(&AxiomTag::Unsafe) {
                return Err(TypeError::ReservedMarkerName(def.name.clone()));
            }
        }
        if is_reserved {
            def.kind = DefinitionKind::Primitive;
            def.axioms.clear();
            if !def.primitive_deps.contains(&def.name) {
                def.primitive_deps.push(def.name.clone());
            }
        }
        // Only an axiom may come without a value: every other definition is admitted on the
        // strength of its checked value (a Total/WellFounded/Partial/Unsafe definition without
        // one would be an unchecked postulate that is not tracked as an axiom).
        if def.value.is_none() && def.totality != Totality::Axiom {
            return Err(TypeError::MissingDefinitionValue {
                name: def.name.clone(),
                totality: def.totality,
            });
        }
        if def.totality == Totality::Axiom && !is_reserved {
            // An axiom depends on itself. This is recorded by the kernel, not taken from the
            // client-supplied `axioms` list or `kind` (only the reserved runtime primitives,
            // handled above, are tracked as primitives instead).
            def.kind = DefinitionKind::AxiomLogical;
            if !def.axioms.contains(&def.name) {
                def.axioms.push(def.name.clone());
            }
        }
        if is_reserved_core && !self.allow_reserved_primitives && !self.allow_redefinition {
            return Err(TypeError::ReservedCoreName(def.name.clone()));
        }
        if self.definitions.contains_key(&def.name) {
            if !self.allow_redefinition {
                return Err(TypeError::DefinitionAlreadyExists(def.name.clone()));
            }
            // Redefinition (`allow_redefinition`) replaces the entry; nothing that was checked
            // against the old meaning may survive it (see `dependents_of_definition`).
            let dependents = self.dependents_of_definition(&def.name);
            if !dependents.is_empty() {
                return Err(TypeError::RedefinitionWithDependents {
                    name: def.name.clone(),
                    dependents,
                });
            }
        }
        // Validate core invariants early (no metas, explicit recursor levels, etc.)
        validate_core_term(&def.ty)?;
        if let Some(ref val) = def.value {
            validate_core_term(val)?;
        }
        if is_reserved && !reserved_primitive_signature_ok(&def.name, &def.ty) {
            return Err(TypeError::ReservedPrimitiveSignature(def.name.clone()));
        }
        if is_reserved_marker && !marker_signature_ok(&def.ty) {
            return Err(TypeError::ReservedMarkerSignature(def.name.clone()));
        }

        // Check that the TYPE doesn't contain partial definitions
        // Types must only reference type-safe (Total/Axiom) definitions
        if let Some(partial_name) = contains_partial_def(self, &def.ty) {
            return Err(TypeError::PartialInType(partial_name));
        }
        if def.totality == Totality::WellFounded {
            def.wf_checked = false;
        }

        // Insert a placeholder for recursive references during type-checking.
        // The placeholder has no value, so it will not unfold during defeq.
        let name = def.name.clone();
        let placeholder = Definition {
            name: name.clone(),
            ty: def.ty.clone(),
            value: None,
            totality: def.totality,
            kind: def.kind,
            rec_arg: def.rec_arg,
            wf_info: def.wf_info.clone(),
            wf_checked: false,
            transparency: Transparency::None,
            axiom_tags: def.axiom_tags.clone(),
            axioms: def.axioms.clone(),
            primitive_deps: def.primitive_deps.clone(),
            noncomputable: def.noncomputable,
            capture_modes: def.capture_modes.clone(),
            borrow_wrapper_marker: def.borrow_wrapper_marker,
        };
        let mut previous = self.definitions.insert(name.clone(), placeholder);
        let mut restore_previous = |defs: &mut HashMap<String, Definition>| {
            if let Some(prev) = previous.take() {
                defs.insert(name.clone(), prev);
            } else {
                defs.remove(&name);
            }
        };

        let result = (|| {
            let ctx = Context::new();

            // Ensure the declared type itself is well-typed and is a Sort.
            let ty_ty = infer(self, &ctx, def.ty.clone())?;
            let ty_ty_norm = whnf_in_ctx(self, &ctx, ty_ty, crate::Transparency::Reducible)?;
            if !matches!(&*ty_ty_norm, Term::Sort(_)) {
                return Err(TypeError::ExpectedSort(ty_ty_norm));
            }

            if def.totality == Totality::Partial {
                let is_comp = is_comp_return_type(self, &ctx, &def.ty)?;
                if !is_comp {
                    return Err(TypeError::PartialReturnType {
                        name: def.name.clone(),
                        ty: def.ty.clone(),
                    });
                }
            }

            // Ensure the value checks against the declared type (if provided).
            if let Some(ref val) = def.value {
                check(self, &ctx, val.clone(), def.ty.clone())?;
            }

            // Enforce ownership/linearity on values in the kernel.
            if let Some(ref val) = def.value {
                let mut usage = UsageContext::new();
                check_ownership_in_term(self, &ctx, val, &mut usage, UsageMode::Consuming)?;
            }

            if let Some(ref val) = def.value {
                validate_capture_modes(&def.name, val, &def.capture_modes)?;
            }

            // Check Effect Boundaries (Phase 5)
            if let Some(ref val) = def.value {
                check_effects(self, def.totality, val)?;
            }

            // For Total definitions, verify termination and record decreasing argument
            if def.totality == Totality::Total {
                if let Some(ref val) = def.value {
                    // Collect all existing total definitions (with bodies) plus the new definition.
                    let mut total_defs: Vec<TotalDefWithHint> = self
                        .definitions
                        .iter()
                        .filter_map(|(name, existing)| {
                            if existing.totality == Totality::Total {
                                existing.value.as_ref().map(|body| {
                                    (
                                        name.clone(),
                                        existing.ty.clone(),
                                        body.clone(),
                                        existing.rec_arg,
                                    )
                                })
                            } else {
                                None
                            }
                        })
                        .collect();
                    total_defs.push((def.name.clone(), def.ty.clone(), val.clone(), def.rec_arg));

                    // Find mutual recursion group containing the new definition.
                    let def_names: Vec<&str> =
                        total_defs.iter().map(|(n, _, _, _)| n.as_str()).collect();
                    let call_graph = build_call_graph(
                        &total_defs
                            .iter()
                            .map(|(n, ty, body, _)| (n.clone(), ty.clone(), body.clone()))
                            .collect::<Vec<_>>(),
                    );
                    let mutual_groups = find_mutual_groups(&call_graph, &def_names);

                    let mut rec_arg = None;
                    if let Some(group) = mutual_groups
                        .iter()
                        .find(|g| g.contains(&def.name.as_str()))
                    {
                        if group.len() > 1 {
                            let group_defs: Vec<TotalDefWithHint> = group
                                .iter()
                                .filter_map(|name| {
                                    total_defs.iter().find(|(n, _, _, _)| n == *name).cloned()
                                })
                                .collect();
                            let results = check_mutual_termination_with_hints(self, &group_defs)?;
                            rec_arg = results
                                .iter()
                                .find(|(name, _)| name == &def.name)
                                .and_then(|(_, arg)| *arg);
                        }
                    }

                    // If not in a mutual recursion group, use the standard termination check.
                    if rec_arg.is_none() {
                        rec_arg = check_termination_with_hint(
                            self,
                            &def.name,
                            &def.ty,
                            val,
                            def.rec_arg,
                        )?;
                    }

                    // Automatically set rec_arg if not already specified
                    if def.rec_arg.is_none() && rec_arg.is_some() {
                        def.rec_arg = rec_arg;
                    }
                }
            }

            // For WellFounded definitions, verify termination via well-founded recursion.
            if def.totality == Totality::WellFounded {
                if let Some(ref val) = def.value {
                    let wf_info = def
                        .wf_info
                        .clone()
                        .ok_or_else(|| TypeError::MissingWellFoundedInfo(def.name.clone()))?;

                    // Extract parameter types to determine the decreasing argument's type.
                    let mut param_types = Vec::new();
                    let mut curr_ty = def.ty.clone();
                    while let Term::Pi(dom, cod, _, _) = &*curr_ty {
                        param_types.push(dom.clone());
                        curr_ty = cod.clone();
                    }

                    if wf_info.decreasing_arg >= param_types.len() {
                        return Err(TypeError::InvalidWellFoundedDecreasingArg {
                            name: def.name.clone(),
                            index: wf_info.decreasing_arg,
                        });
                    }

                    let spec = WellFoundedSpec {
                        relation: wf_info.relation.clone(),
                        value_type: param_types[wf_info.decreasing_arg].clone(),
                        wf_proof: None,
                        decreasing_arg: wf_info.decreasing_arg,
                    };

                    check_wellfounded_termination(self, &def.name, &def.ty, val, &spec)?;

                    if def.rec_arg.is_none() {
                        def.rec_arg = Some(wf_info.decreasing_arg);
                    }
                    def.wf_checked = true;
                }
            }

            Ok(())
        })();

        // Restore previous definition (if any) on failure.
        if let Err(e) = result {
            restore_previous(&mut self.definitions);
            return Err(e);
        }

        // Compute axiom/primitive dependencies.
        let mut used_axioms = HashSet::new();
        let mut used_primitives = HashSet::new();
        // Include self-declared dependencies.
        for ax in &def.axioms {
            used_axioms.insert(ax.clone());
        }
        for prim in &def.primitive_deps {
            used_primitives.insert(prim.clone());
        }
        // Collect from type/value.
        collect_axioms_rec(self, &def.ty, &mut used_axioms, &mut used_primitives);
        if let Some(ref val) = def.value {
            collect_axioms_rec(self, val, &mut used_axioms, &mut used_primitives);
        }
        def.axioms = used_axioms.into_iter().collect();
        def.axioms.sort();
        def.primitive_deps = used_primitives.into_iter().collect();
        def.primitive_deps.sort();

        if !def.axiom_tags.is_empty() {
            self.snapshot_axiom_tags(&def.name, &def.axiom_tags);
        }

        let classical = axiom_dependencies_with_tag(self, &def.axioms, AxiomTag::Classical);
        let unsafe_axioms = axiom_dependencies_with_tag(self, &def.axioms, AxiomTag::Unsafe);
        if def.totality != Totality::Axiom
            && def.totality != Totality::Unsafe
            && !def.noncomputable
            && !def.axioms.is_empty()
        {
            let mut kinds = Vec::new();
            if !classical.is_empty() {
                kinds.push("classical");
            }
            if !unsafe_axioms.is_empty() {
                kinds.push("unsafe");
            }
            let has_untagged = def
                .axioms
                .iter()
                .any(|ax| !classical.contains(ax) && !unsafe_axioms.contains(ax));
            if has_untagged {
                kinds.push("axiom");
            }
            restore_previous(&mut self.definitions);
            return Err(TypeError::AxiomDependencyRequiresNoncomputable {
                name: def.name.clone(),
                kinds: kinds.join("/"),
                axioms: def.axioms.clone(),
            });
        }

        let refers_to_itself = def.totality == Totality::Total
            && def.value.as_ref().is_some_and(|val| {
                term_mentions(
                    val,
                    &|node| matches!(node, Term::Const(n, _) if *n == def.name),
                )
            });
        if refers_to_itself {
            self.self_recursive.insert(def.name.clone());
        } else {
            self.self_recursive.remove(&def.name);
        }

        // Also add to legacy defs for backward compatibility
        self.definitions.insert(def.name.clone(), def);
        Ok(())
    }

    /// Get an inductive declaration by name
    pub fn get_inductive(&self, name: &str) -> Option<&InductiveDecl> {
        self.inductives.get(name)
    }

    /// Compute shared inductive metadata for recursor reduction/lowering.
    pub fn inductive_info(&self, name: &str) -> Option<InductiveInfo> {
        let decl = self.inductives.get(name)?;
        Some(InductiveInfo::from_decl(decl))
    }

    pub fn constructor_candidates(&self, name: &str) -> &[ConstructorRef] {
        self.constructor_index
            .get(name)
            .map(|entries| entries.as_slice())
            .unwrap_or(&[])
    }

    /// Get a full definition with totality info
    pub fn get_definition(&self, name: &str) -> Option<&Definition> {
        self.definitions.get(name)
    }

    /// Check if a definition can be safely unfolded in type contexts
    pub fn is_type_safe(&self, name: &str) -> bool {
        self.definitions
            .get(name)
            .map_or(true, |d| d.is_type_safe())
    }

    /// Temporarily register a constructor-less `placeholder` for an inductive that is about to
    /// be declared (the elaborator needs the name in scope while it elaborates the constructor
    /// types). Returns the entry it replaces, if any.
    ///
    /// Replacing an existing inductive is a redeclaration: like [`Env::add_inductive`] it is
    /// refused when other definitions or inductives refer to that inductive
    /// (`RedefinitionWithDependents`, K0054), since they were checked against the old
    /// declaration.
    pub fn insert_inductive_placeholder(
        &mut self,
        placeholder: InductiveDecl,
    ) -> Result<Option<InductiveDecl>, TypeError> {
        let name = placeholder.name.clone();
        if self.inductives.contains_key(&name) {
            let dependents = self.dependents_of_inductive(&name);
            if !dependents.is_empty() {
                return Err(TypeError::RedefinitionWithDependents { name, dependents });
            }
        }
        let previous = self.inductives.insert(name, placeholder);
        if let Some(ref prev) = previous {
            self.remove_constructor_index_for(prev);
        }
        Ok(previous)
    }

    pub fn restore_inductive(&mut self, decl: InductiveDecl) {
        if let Some(prev) = self.inductives.insert(decl.name.clone(), decl.clone()) {
            self.remove_constructor_index_for(&prev);
        }
        self.add_constructor_index_for(&decl);
    }

    fn add_constructor_index_for(&mut self, decl: &InductiveDecl) {
        for (idx, ctor) in decl.ctors.iter().enumerate() {
            let entry = self.constructor_index.entry(ctor.name.clone()).or_default();
            entry.push(ConstructorRef {
                ind_name: decl.name.clone(),
                index: idx,
            });
            entry.sort();
            entry.dedup();
        }
    }

    fn remove_constructor_index_for(&mut self, decl: &InductiveDecl) {
        for (idx, ctor) in decl.ctors.iter().enumerate() {
            if let Some(entries) = self.constructor_index.get_mut(&ctor.name) {
                entries.retain(|entry| entry.ind_name != decl.name || entry.index != idx);
                if entries.is_empty() {
                    self.constructor_index.remove(&ctor.name);
                }
            }
        }
    }
}

fn copy_instance_axiom_name(ind_name: &str) -> String {
    format!("copy_instance({})", ind_name)
}

// =============================================================================
// Termination Checking - Structural Recursion & Well-Founded Recursion
// =============================================================================

/// Termination context for tracking smaller variables
#[derive(Clone, Debug)]
struct TerminationCtx {
    /// Variables known to be strictly smaller than the decreasing argument
    smaller_vars: Vec<usize>,
    /// Variables known to be aliases of the recursive function
    recursive_aliases: Vec<usize>,
    /// The argument position (0-based) of the decreasing argument
    rec_arg_pos: usize,
    /// The de Bruijn index (at the current depth) of the decreasing argument, when the body
    /// binds it with a lambda; `None` when the body does not bind it (an eta-reduced body) and
    /// during inference.
    decreasing_var: Option<usize>,
    /// Inference of the decreasing argument (`collect_recursion_info`): the argument is not
    /// known yet, so the recursive fields of a recursor applied to any variable are taken as
    /// smaller. Only a candidate that passes the checking pass (`inferring == false`) is used.
    inferring: bool,
    /// Name of the inductive type being recursed on
    ind_name: String,
    /// Current binding depth
    depth: usize,
}

impl TerminationCtx {
    /// Checking context for the decreasing argument at `rec_arg_pos`, for a body opened under
    /// its first `bound_params` parameters (`open_binders`).
    fn new(rec_arg_pos: usize, ind_name: String, bound_params: usize) -> Self {
        let decreasing_var = if rec_arg_pos < bound_params {
            Some(bound_params - 1 - rec_arg_pos)
        } else {
            None
        };
        TerminationCtx {
            smaller_vars: Vec::new(),
            recursive_aliases: Vec::new(),
            rec_arg_pos,
            decreasing_var,
            inferring: false,
            ind_name,
            depth: 0,
        }
    }

    /// Context for inferring the decreasing argument.
    fn inference() -> Self {
        TerminationCtx {
            smaller_vars: Vec::new(),
            recursive_aliases: Vec::new(),
            rec_arg_pos: 0,
            decreasing_var: None,
            inferring: true,
            ind_name: String::new(),
            depth: 0,
        }
    }

    /// Shift context when entering a binder
    fn shift(&self) -> Self {
        TerminationCtx {
            smaller_vars: self.smaller_vars.iter().map(|v| v + 1).collect(),
            recursive_aliases: self.recursive_aliases.iter().map(|v| v + 1).collect(),
            rec_arg_pos: self.rec_arg_pos,
            decreasing_var: self.decreasing_var.map(|v| v + 1),
            inferring: self.inferring,
            ind_name: self.ind_name.clone(),
            depth: self.depth + 1,
        }
    }

    /// Add a variable as smaller (e.g., from pattern matching)
    fn add_smaller(&self, var: usize) -> Self {
        let mut ctx = self.clone();
        ctx.smaller_vars.push(var);
        ctx
    }

    /// Add a variable as a recursive alias (e.g., from let-binding the function)
    fn add_recursive_alias(&self, var: usize) -> Self {
        let mut ctx = self.clone();
        if !ctx.recursive_aliases.contains(&var) {
            ctx.recursive_aliases.push(var);
        }
        ctx
    }

    fn is_recursive_alias(&self, var: usize) -> bool {
        self.recursive_aliases.contains(&var)
    }
}

#[derive(Debug, Clone)]
struct RecArgInference {
    saw_recursive_call: bool,
    call_candidates: Vec<bool>,
    saw_recursor: bool,
    recursor_candidates: Vec<bool>,
}

impl RecArgInference {
    fn new(num_params: usize) -> Self {
        RecArgInference {
            saw_recursive_call: false,
            call_candidates: vec![true; num_params],
            saw_recursor: false,
            recursor_candidates: vec![false; num_params],
        }
    }

    fn record_call(&mut self, args: &[Rc<Term>], ctx: &TerminationCtx) {
        self.saw_recursive_call = true;
        for (idx, candidate) in self.call_candidates.iter_mut().enumerate() {
            if idx < args.len() {
                let is_smaller_arg = is_smaller(&args[idx], ctx);
                *candidate = *candidate && is_smaller_arg;
            }
        }
    }

    fn record_recursor_major(&mut self, var_idx: usize, ctx: &TerminationCtx, num_params: usize) {
        if let Some(param_pos) = param_pos_from_var(var_idx, ctx, num_params) {
            if let Some(slot) = self.recursor_candidates.get_mut(param_pos) {
                *slot = true;
            }
        }
        self.saw_recursor = true;
    }

    fn record_recursor(&mut self) {
        self.saw_recursor = true;
    }
}

fn param_pos_from_var(var_idx: usize, ctx: &TerminationCtx, num_params: usize) -> Option<usize> {
    if var_idx < ctx.depth || var_idx >= ctx.depth + num_params {
        return None;
    }
    let param_idx = var_idx - ctx.depth;
    Some(num_params - 1 - param_idx)
}

fn inductive_param_names(env: &Env, param_types: &[Rc<Term>]) -> Vec<Option<String>> {
    param_types
        .iter()
        .map(|param_ty| get_inductive_name(env, param_ty))
        .collect()
}

fn first_true(candidates: &[bool]) -> Option<usize> {
    candidates.iter().position(|v| *v)
}

fn collect_recursion_info(
    env: &Env,
    def_name: &str,
    recursive_names: &[&str],
    t: &Rc<Term>,
    ctx: &TerminationCtx,
    num_params: usize,
    info: &mut RecArgInference,
) -> Result<(), TypeError> {
    match &**t {
        Term::Const(name, _) if recursive_names.contains(&name.as_str()) => {
            Err(TypeError::TerminationError {
                def_name: def_name.to_string(),
                details: TerminationErrorDetails::BareRecursiveReference,
            })
        }
        Term::Var(idx) if ctx.is_recursive_alias(*idx) => Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::BareRecursiveReference,
        }),
        Term::App(_, _, _) => {
            if let Some((ind_name, rec_args)) = extract_rec_app(t) {
                if let Some(decl) = env.get_inductive(&ind_name) {
                    info.record_recursor();
                    if let Some(major_arg) = recursor_major_arg(decl, &rec_args) {
                        if let Term::Var(var_idx) = &*major_arg {
                            info.record_recursor_major(*var_idx, ctx, num_params);
                        }
                    }

                    let minor_start = decl.num_params + 1;
                    let minor_end = minor_start + decl.ctors.len();
                    let fields_smaller = recursor_fields_are_smaller(decl, &rec_args, ctx);

                    for (ctor_idx, minor) in rec_args
                        .iter()
                        .take(minor_end.min(rec_args.len()))
                        .skip(minor_start)
                        .enumerate()
                    {
                        if let Some((body, new_ctx)) =
                            build_minor_premise_ctx(decl, ctor_idx, minor, ctx, fields_smaller)
                        {
                            collect_recursion_info(
                                env,
                                def_name,
                                recursive_names,
                                &body,
                                &new_ctx,
                                num_params,
                                info,
                            )?;
                        }
                    }

                    if rec_args.len() > minor_end {
                        for arg in &rec_args[minor_end..] {
                            collect_recursion_info(
                                env,
                                def_name,
                                recursive_names,
                                arg,
                                ctx,
                                num_params,
                                info,
                            )?;
                        }
                    }

                    return Ok(());
                }
            }

            for recursive_name in recursive_names {
                if let Some(args) = extract_app_to_const(t, recursive_name) {
                    info.record_call(&args, ctx);
                    for arg in &args {
                        collect_recursion_info(
                            env,
                            def_name,
                            recursive_names,
                            arg,
                            ctx,
                            num_params,
                            info,
                        )?;
                    }
                    return Ok(());
                }
            }

            if let Some((var_idx, args)) = extract_app_to_var(t) {
                if ctx.is_recursive_alias(var_idx) {
                    info.record_call(&args, ctx);
                    for arg in &args {
                        collect_recursion_info(
                            env,
                            def_name,
                            recursive_names,
                            arg,
                            ctx,
                            num_params,
                            info,
                        )?;
                    }
                    return Ok(());
                }
            }

            let (f, args) = collect_app_spine(t);
            collect_recursion_info(env, def_name, recursive_names, &f, ctx, num_params, info)?;
            for arg in &args {
                collect_recursion_info(
                    env,
                    def_name,
                    recursive_names,
                    &arg.arg,
                    ctx,
                    num_params,
                    info,
                )?;
            }
            Ok(())
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) | Term::Fix(ty, body) => {
            collect_recursion_info(env, def_name, recursive_names, ty, ctx, num_params, info)?;
            let body_ctx = ctx.shift();
            collect_recursion_info(
                env,
                def_name,
                recursive_names,
                body,
                &body_ctx,
                num_params,
                info,
            )
        }
        Term::LetE(ty, val, body) => {
            collect_recursion_info(env, def_name, recursive_names, ty, ctx, num_params, info)?;
            let is_alias = is_recursive_alias_value_for_set(val, recursive_names, ctx);
            if !is_alias {
                collect_recursion_info(env, def_name, recursive_names, val, ctx, num_params, info)?;
            }
            let mut body_ctx = if is_smaller(val, ctx) {
                ctx.shift().add_smaller(0)
            } else {
                ctx.shift()
            };
            if is_alias {
                body_ctx = body_ctx.add_recursive_alias(0);
            }
            collect_recursion_info(
                env,
                def_name,
                recursive_names,
                body,
                &body_ctx,
                num_params,
                info,
            )
        }
        Term::Meta(_) => Ok(()),
        _ => Ok(()),
    }
}

/// Check that a definition terminates via structural recursion.
///
/// A function terminates if all recursive calls are on structurally smaller
/// arguments. "Smaller" means: after pattern matching on an inductive value,
/// the bound variables for subterms are smaller than the matched value.
///
/// This checker handles:
/// - Direct structural recursion
/// - Nested pattern matching
/// - Recursor (Rec) applications which encode guarded recursion
///
/// This is a conservative check - it may reject some terminating functions.
pub fn check_termination(
    env: &Env,
    def_name: &str,
    ty: &Rc<Term>,
    body: &Rc<Term>,
) -> Result<Option<usize>, TypeError> {
    check_termination_with_hint(env, def_name, ty, body, None)
}

pub fn check_termination_with_hint(
    env: &Env,
    def_name: &str,
    ty: &Rc<Term>,
    body: &Rc<Term>,
    rec_arg_hint: Option<usize>,
) -> Result<Option<usize>, TypeError> {
    if contains_fix(body) {
        return Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::GeneralRecursion,
        });
    }

    let mut param_types = Vec::new();
    let mut curr_ty = ty.clone();
    while let Term::Pi(dom, cod, _, _) = &*curr_ty {
        param_types.push(dom.clone());
        curr_ty = cod.clone();
    }

    let num_params = param_types.len();
    let inner_body = open_binders(body, num_params);
    let ind_names = inductive_param_names(env, &param_types);

    if let Some(hint) = rec_arg_hint {
        if hint >= num_params || ind_names.get(hint).and_then(|v| v.clone()).is_none() {
            return Err(TypeError::TerminationError {
                def_name: def_name.to_string(),
                details: TerminationErrorDetails::InvalidDecreasingArgument { arg_position: hint },
            });
        }
    }

    let mut info = RecArgInference::new(num_params);
    let ctx = TerminationCtx::inference();
    collect_recursion_info(
        env,
        def_name,
        &[def_name],
        &inner_body,
        &ctx,
        num_params,
        &mut info,
    )?;

    let check_at = |pos: usize| -> Result<(), TypeError> {
        let ind_name = ind_names[pos].clone().unwrap_or_default();
        let check_ctx = TerminationCtx::new(pos, ind_name, num_params);
        check_recursive_calls_ctx(env, def_name, &inner_body, &check_ctx)
    };

    let mut rec_arg = None;
    if info.saw_recursive_call {
        let mut candidates = info.call_candidates.clone();
        for (idx, candidate) in candidates.iter_mut().enumerate() {
            if idx >= ind_names.len() || ind_names[idx].is_none() {
                *candidate = false;
            }
        }
        if let Some(hint) = rec_arg_hint {
            if hint < candidates.len() && candidates[hint] {
                rec_arg = Some(hint);
            } else {
                if hint < ind_names.len() && ind_names[hint].is_some() {
                    return check_at(hint).map(|_| Some(hint));
                }
                return Err(TypeError::TerminationError {
                    def_name: def_name.to_string(),
                    details: TerminationErrorDetails::NoDecreasingArgument,
                });
            }
        } else if first_true(&candidates).is_some() {
            // Inference over-approximates (it does not know which argument decreases); the
            // first candidate that passes the checking pass is the decreasing argument. When
            // none passes, report the first candidate's error.
            let mut first_err = None;
            for pos in (0..candidates.len()).filter(|pos| candidates[*pos]) {
                match check_at(pos) {
                    Ok(()) => return Ok(Some(pos)),
                    Err(err) => {
                        if first_err.is_none() {
                            first_err = Some(err);
                        }
                    }
                }
            }
            if let Some(err) = first_err {
                return Err(err);
            }
        } else {
            if let Some(first_ind) = ind_names.iter().position(|n| n.is_some()) {
                check_at(first_ind)?;
            }
            return Err(TypeError::TerminationError {
                def_name: def_name.to_string(),
                details: TerminationErrorDetails::NoDecreasingArgument,
            });
        }
    } else if info.saw_recursor {
        let mut candidates = info.recursor_candidates.clone();
        for (idx, candidate) in candidates.iter_mut().enumerate() {
            if idx >= ind_names.len() || ind_names[idx].is_none() {
                *candidate = false;
            }
        }
        if let Some(hint) = rec_arg_hint {
            rec_arg = Some(hint);
        } else {
            rec_arg = first_true(&candidates);
        }
    }

    if let Some(rec_arg_pos) = rec_arg {
        check_at(rec_arg_pos)?;
        Ok(Some(rec_arg_pos))
    } else {
        Ok(None)
    }
}

/// Check termination for a group of mutually recursive definitions.
/// Returns a Vec of (name, rec_arg) pairs for each definition.
///
/// For mutual recursion to be valid:
/// All functions must decrease on the same argument position and inductive type.
pub fn check_mutual_termination(
    env: &Env,
    defs: &[(String, Rc<Term>, Rc<Term>)], // (name, type, body)
) -> Result<Vec<(String, Option<usize>)>, TypeError> {
    let defs_with_hints: Vec<TotalDefWithHint> = defs
        .iter()
        .map(|(name, ty, body)| (name.clone(), ty.clone(), body.clone(), None))
        .collect();
    check_mutual_termination_with_hints(env, &defs_with_hints)
}

fn check_mutual_termination_with_hints(
    env: &Env,
    defs: &[TotalDefWithHint], // (name, type, body, rec_arg_hint)
) -> Result<Vec<(String, Option<usize>)>, TypeError> {
    if defs.is_empty() {
        return Ok(vec![]);
    }

    // Build the call graph: which functions call which
    let def_names: Vec<&str> = defs.iter().map(|(n, _, _, _)| n.as_str()).collect();
    let call_graph = build_call_graph(
        &defs
            .iter()
            .map(|(name, ty, body, _)| (name.clone(), ty.clone(), body.clone()))
            .collect::<Vec<_>>(),
    );

    // Find mutually recursive groups (functions that call each other)
    let mutual_groups = find_mutual_groups(&call_graph, &def_names);

    let mut results = Vec::new();

    // Check each mutual group
    for group in &mutual_groups {
        if group.len() == 1 {
            // Single function - use regular termination check
            let name = group[0];
            if let Some((_, ty, body, rec_arg_hint)) = defs.iter().find(|(n, _, _, _)| n == name) {
                let rec_arg = check_termination_with_hint(env, name, ty, body, *rec_arg_hint)?;
                results.push((name.to_string(), rec_arg));
            }
        } else {
            // Mutual recursion - require a shared, explicit decreasing measure.
            struct GroupDefInfo {
                name: String,
                body: Rc<Term>,
                num_params: usize,
                ind_names: Vec<Option<String>>,
                candidates: Vec<bool>,
                rec_arg_hint: Option<usize>,
            }

            let group_defs: Vec<_> = group
                .iter()
                .filter_map(|name| defs.iter().find(|(n, _, _, _)| n == *name))
                .collect();

            let mut infos: Vec<GroupDefInfo> = Vec::new();
            let mut max_params = 0usize;

            for (def_name, ty, body, rec_arg_hint) in &group_defs {
                let mut param_types = Vec::new();
                let mut curr_ty = (*ty).clone();
                while let Term::Pi(dom, cod, _, _) = &*curr_ty {
                    param_types.push(dom.clone());
                    curr_ty = cod.clone();
                }
                let num_params = param_types.len();
                let ind_names = inductive_param_names(env, &param_types);

                if let Some(hint) = *rec_arg_hint {
                    if hint >= num_params || ind_names.get(hint).and_then(|v| v.clone()).is_none() {
                        return Err(TypeError::TerminationError {
                            def_name: def_name.clone(),
                            details: TerminationErrorDetails::InvalidDecreasingArgument {
                                arg_position: hint,
                            },
                        });
                    }
                }

                let inner_body = open_binders(body, num_params);
                let mut info = RecArgInference::new(num_params);
                let ctx = TerminationCtx::inference();
                collect_recursion_info(
                    env,
                    def_name,
                    group.as_slice(),
                    &inner_body,
                    &ctx,
                    num_params,
                    &mut info,
                )?;

                let mut candidates = vec![false; num_params];
                if info.saw_recursive_call {
                    candidates.clone_from(&info.call_candidates);
                }
                for (idx, candidate) in candidates.iter_mut().enumerate() {
                    if idx >= ind_names.len() || ind_names[idx].is_none() {
                        *candidate = false;
                    }
                }

                if let Some(hint) = *rec_arg_hint {
                    if hint < candidates.len() && !candidates[hint] {
                        let ind_name = ind_names[hint].clone().unwrap_or_default();
                        let hint_ctx = TerminationCtx::new(hint, ind_name, num_params);
                        check_mutual_recursive_calls(
                            env,
                            def_name,
                            group.as_slice(),
                            &inner_body,
                            &hint_ctx,
                        )?;
                    }
                }

                max_params = max_params.max(num_params);
                infos.push(GroupDefInfo {
                    name: def_name.clone(),
                    body: body.clone(),
                    num_params,
                    ind_names,
                    candidates,
                    rec_arg_hint: *rec_arg_hint,
                });
            }

            let mut group_candidates = vec![true; max_params];
            let mut group_ind_names: Vec<Option<String>> = vec![None; max_params];

            for info in &infos {
                for pos in 0..max_params {
                    if pos >= info.num_params {
                        group_candidates[pos] = false;
                        continue;
                    }
                    if !info.candidates[pos] {
                        group_candidates[pos] = false;
                        continue;
                    }
                    let ind_name = info.ind_names[pos].clone();
                    if ind_name.is_none() {
                        group_candidates[pos] = false;
                        continue;
                    }
                    match &group_ind_names[pos] {
                        None => group_ind_names[pos] = ind_name,
                        Some(existing) if *existing != ind_name.unwrap_or_default() => {
                            group_candidates[pos] = false;
                        }
                        _ => {}
                    }
                }
            }

            let mut hint_positions: Vec<usize> =
                infos.iter().filter_map(|info| info.rec_arg_hint).collect();
            hint_positions.sort_unstable();
            hint_positions.dedup();

            let group_positions: Vec<usize> = if hint_positions.len() > 1 {
                Vec::new()
            } else if let Some(hint) = hint_positions.first().copied() {
                if hint < group_candidates.len() && group_candidates[hint] {
                    vec![hint]
                } else {
                    Vec::new()
                }
            } else {
                (0..group_candidates.len())
                    .filter(|pos| group_candidates[*pos])
                    .collect()
            };

            // As for a single definition, inference over-approximates: the first shared
            // position at which every definition of the group passes the checking pass is the
            // decreasing argument; when none does, report the first position's error.
            let check_group_at = |pos: usize| -> Result<(), TypeError> {
                for info in &infos {
                    let inner_body = open_binders(&info.body, info.num_params);
                    let ind_name = info.ind_names[pos].clone().unwrap_or_default();
                    let ctx = TerminationCtx::new(pos, ind_name, info.num_params);
                    check_mutual_recursive_calls(
                        env,
                        &info.name,
                        group.as_slice(),
                        &inner_body,
                        &ctx,
                    )?;
                }
                Ok(())
            };
            let mut group_rec_arg = None;
            let mut first_err = None;
            for pos in group_positions {
                match check_group_at(pos) {
                    Ok(()) => {
                        group_rec_arg = Some(pos);
                        break;
                    }
                    Err(err) => {
                        if first_err.is_none() {
                            first_err = Some(err);
                        }
                    }
                }
            }
            let group_rec_arg = match group_rec_arg {
                Some(pos) => pos,
                None => {
                    return Err(first_err.unwrap_or_else(|| TypeError::TerminationError {
                        def_name: group.join(", "),
                        details: TerminationErrorDetails::MutualRecursionError {
                            functions: group.iter().map(|s| s.to_string()).collect(),
                        },
                    }));
                }
            };

            for info in &infos {
                results.push((info.name.clone(), Some(group_rec_arg)));
            }
        }
    }

    Ok(results)
}

/// Build a call graph from definitions
/// Returns a map from function name to set of called function names
fn collect_called_defs(t: &Rc<Term>, def_names: &HashSet<String>, calls: &mut HashSet<String>) {
    match &**t {
        Term::Const(name, _) => {
            if def_names.contains(name) {
                calls.insert(name.clone());
            }
        }
        Term::App(f, a, _) => {
            collect_called_defs(f, def_names, calls);
            collect_called_defs(a, def_names, calls);
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            collect_called_defs(ty, def_names, calls);
            collect_called_defs(body, def_names, calls);
        }
        Term::Fix(ty, body) => {
            collect_called_defs(ty, def_names, calls);
            collect_called_defs(body, def_names, calls);
        }
        Term::LetE(ty, val, body) => {
            collect_called_defs(ty, def_names, calls);
            collect_called_defs(val, def_names, calls);
            collect_called_defs(body, def_names, calls);
        }
        Term::Meta(_) => {}
        _ => {}
    }
}

fn build_call_graph(defs: &[(String, Rc<Term>, Rc<Term>)]) -> HashMap<String, Vec<String>> {
    let def_name_set: HashSet<String> = defs.iter().map(|(n, _, _)| n.clone()).collect();
    let mut graph = HashMap::new();

    for (name, _, body) in defs {
        let mut calls = HashSet::new();
        collect_called_defs(body, &def_name_set, &mut calls);
        let mut calls_vec: Vec<String> = calls.into_iter().collect();
        calls_vec.sort();
        graph.insert(name.clone(), calls_vec);
    }

    graph
}

/// Find groups of mutually recursive functions
/// Returns a list of groups, where each group contains function names that call each other
fn find_mutual_groups<'a>(
    call_graph: &HashMap<String, Vec<String>>,
    def_names: &[&'a str],
) -> Vec<Vec<&'a str>> {
    struct TarjanState {
        index: usize,
        indices: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        groups: Vec<Vec<usize>>,
    }

    impl TarjanState {
        fn new(node_count: usize) -> Self {
            TarjanState {
                index: 0,
                indices: vec![None; node_count],
                lowlink: vec![0; node_count],
                stack: Vec::new(),
                on_stack: vec![false; node_count],
                groups: Vec::new(),
            }
        }

        fn strongconnect(&mut self, v: usize, edges: &[Vec<usize>]) {
            self.indices[v] = Some(self.index);
            self.lowlink[v] = self.index;
            self.index += 1;
            self.stack.push(v);
            self.on_stack[v] = true;

            for &w in &edges[v] {
                if self.indices[w].is_none() {
                    self.strongconnect(w, edges);
                    let lowlink_w = self.lowlink[w];
                    self.lowlink[v] = self.lowlink[v].min(lowlink_w);
                } else if self.on_stack[w] {
                    if let Some(w_index) = self.indices[w] {
                        self.lowlink[v] = self.lowlink[v].min(w_index);
                    }
                }
            }

            if self.indices[v] == Some(self.lowlink[v]) {
                let mut group = Vec::new();
                while let Some(w) = self.stack.pop() {
                    self.on_stack[w] = false;
                    group.push(w);
                    if w == v {
                        break;
                    }
                }
                self.groups.push(group);
            }
        }
    }

    let mut names: Vec<&'a str> = def_names.to_vec();
    names.sort();
    names.dedup();

    let mut name_to_index = HashMap::new();
    for (idx, name) in names.iter().enumerate() {
        name_to_index.insert(*name, idx);
    }

    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); names.len()];
    for (idx, name) in names.iter().enumerate() {
        if let Some(calls) = call_graph.get(*name) {
            let mut indices = Vec::new();
            for called in calls {
                if let Some(&called_idx) = name_to_index.get(called.as_str()) {
                    indices.push(called_idx);
                }
            }
            indices.sort_unstable();
            indices.dedup();
            edges[idx] = indices;
        }
    }

    let mut tarjan = TarjanState::new(names.len());

    for v in 0..names.len() {
        if tarjan.indices[v].is_none() {
            tarjan.strongconnect(v, &edges);
        }
    }

    let mut result: Vec<Vec<&'a str>> = tarjan
        .groups
        .into_iter()
        .map(|group| {
            let mut out: Vec<&'a str> = group.into_iter().map(|idx| names[idx]).collect();
            out.sort();
            out
        })
        .collect();
    result.sort_by(|a, b| a.first().cmp(&b.first()));
    result
}

/// Check recursive calls in mutual recursion context
fn check_mutual_recursive_calls(
    env: &Env,
    def_name: &str,
    mutual_names: &[&str],
    t: &Rc<Term>,
    ctx: &TerminationCtx,
) -> Result<(), TypeError> {
    match &**t {
        Term::Const(name, _) if mutual_names.contains(&name.as_str()) => {
            Err(TypeError::TerminationError {
                def_name: def_name.to_string(),
                details: TerminationErrorDetails::BareRecursiveReference,
            })
        }
        Term::Var(idx) if ctx.is_recursive_alias(*idx) => Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::BareRecursiveReference,
        }),
        Term::App(_, _, _) => {
            // Check if this is a recursor application
            if let Some((ind_name, rec_args)) = extract_rec_app(t) {
                return check_rec_app_mutual(
                    env,
                    def_name,
                    mutual_names,
                    &ind_name,
                    &rec_args,
                    ctx,
                );
            }

            // Check if this is a call to any mutual function
            for mutual_name in mutual_names {
                if let Some(args) = extract_app_to_const(t, mutual_name) {
                    // Verify the recursive argument is smaller
                    check_decreasing_argument(def_name, &args, ctx)?;
                    // Check args recursively
                    for arg in &args {
                        check_mutual_recursive_calls(env, def_name, mutual_names, arg, ctx)?;
                    }
                    return Ok(());
                }
            }

            if let Some((var_idx, args)) = extract_app_to_var(t) {
                if ctx.is_recursive_alias(var_idx) {
                    check_decreasing_argument(def_name, &args, ctx)?;
                    for arg in &args {
                        check_mutual_recursive_calls(env, def_name, mutual_names, arg, ctx)?;
                    }
                    return Ok(());
                }
            }

            // Regular application - check both parts
            let (f, args) = collect_app_spine(t);
            check_mutual_recursive_calls(env, def_name, mutual_names, &f, ctx)?;
            for arg in &args {
                check_mutual_recursive_calls(env, def_name, mutual_names, &arg.arg, ctx)?;
            }
            Ok(())
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) | Term::Fix(ty, body) => {
            check_mutual_recursive_calls(env, def_name, mutual_names, ty, ctx)?;
            let body_ctx = ctx.shift();
            check_mutual_recursive_calls(env, def_name, mutual_names, body, &body_ctx)
        }
        Term::LetE(ty, val, body) => {
            check_mutual_recursive_calls(env, def_name, mutual_names, ty, ctx)?;
            let is_alias = is_mutual_recursive_alias_value(val, mutual_names, ctx);
            if !is_alias {
                check_mutual_recursive_calls(env, def_name, mutual_names, val, ctx)?;
            }
            let mut body_ctx = ctx.shift();
            if is_alias {
                body_ctx = body_ctx.add_recursive_alias(0);
            }
            check_mutual_recursive_calls(env, def_name, mutual_names, body, &body_ctx)
        }
        _ => Ok(()),
    }
}

#[derive(Clone, Debug)]
struct AppSpineItem {
    arg: Rc<Term>,
    #[allow(dead_code)]
    label: Option<String>,
}

/// Collect an application spine: f a1 a2 ... an -> (f, [a1, a2, ..., an])
fn collect_app_spine(t: &Rc<Term>) -> (Rc<Term>, Vec<AppSpineItem>) {
    let mut args = Vec::new();
    let mut curr = t.clone();
    while let Term::App(f, a, label) = &*curr {
        args.push(AppSpineItem {
            arg: a.clone(),
            label: label.clone(),
        });
        curr = f.clone();
    }
    args.reverse();
    (curr, args)
}

fn peel_pi_codomain(ty: &Rc<Term>) -> Rc<Term> {
    let mut curr = ty.clone();
    while let Term::Pi(_, body, _, _) = &*curr {
        curr = body.clone();
    }
    curr
}

pub fn is_comp_return_type(env: &Env, ctx: &Context, ty: &Rc<Term>) -> Result<bool, TypeError> {
    let ret = peel_pi_codomain(ty);
    let ret_whnf = whnf_in_ctx(env, ctx, ret, Transparency::Reducible)?;
    let (head, args) = collect_app_spine(&ret_whnf);
    match &*head {
        Term::Ind(name, _) if name == "Comp" && env.get_inductive(name).is_some() => {
            Ok(args.len() == 1)
        }
        _ => Ok(false),
    }
}

fn subst_params(term: &Rc<Term>, args: &[Rc<Term>]) -> Rc<Term> {
    let mut result = term.clone();
    for arg in args.iter().rev() {
        result = result.subst(0, arg);
    }
    result
}

/// Get the inductive type name if a type is inductive (possibly applied)
fn get_inductive_name(env: &Env, ty: &Rc<Term>) -> Option<String> {
    let head = get_head(ty);
    match &*head {
        Term::Ind(name, _) if env.get_inductive(name).is_some() => Some(name.clone()),
        _ => None,
    }
}

/// Get the inductive type name and arguments if a type is inductive (possibly applied)
fn get_inductive_head_args(env: &Env, ty: &Rc<Term>) -> Option<(String, Vec<Rc<Term>>)> {
    let (head, args) = collect_app_spine(ty);
    let args: Vec<Rc<Term>> = args.into_iter().map(|item| item.arg).collect();
    match &*head {
        Term::Ind(name, _) if env.get_inductive(name).is_some() => Some((name.clone(), args)),
        _ => None,
    }
}

/// Check if a type is an inductive type (possibly applied to arguments)
#[allow(dead_code)]
fn is_inductive_type(env: &Env, ty: &Rc<Term>) -> bool {
    get_inductive_name(env, ty).is_some()
}

/// Get the head of an application chain
fn get_head(t: &Rc<Term>) -> Rc<Term> {
    match &**t {
        Term::App(f, _, _) => get_head(f),
        _ => t.clone(),
    }
}

/// `t` (a function of at least `n` arguments) as a term under `n` binders: its first `n` leading
/// lambdas are peeled and, when it has fewer (`k`), the rest is applied to the remaining
/// `n - k` bound variables (eta-expansion). The termination checker reads `Var(i)` in the result
/// as the `i`-th innermost of the `n` binders; with only `peel_lambdas`, a definition body or a
/// minor premise with fewer leading lambdas than binders was analysed at the wrong depth, so
/// the variables marked as smaller (or as the decreasing argument) were not the intended ones.
fn open_binders(t: &Rc<Term>, n: usize) -> Rc<Term> {
    let mut peeled = 0;
    let mut curr = t.clone();
    while peeled < n {
        let next = match &*curr {
            Term::Lam(_, body, _, _) => body.clone(),
            _ => break,
        };
        curr = next;
        peeled += 1;
    }
    let missing = n - peeled;
    if missing == 0 {
        return curr;
    }
    let mut expanded = curr.shift(0, missing);
    for j in 0..missing {
        expanded = Term::app(expanded, Term::var(missing - 1 - j));
    }
    expanded
}

/// A recursive call (to the function or a member of its mutual group) must supply the
/// decreasing argument, and that argument must be structurally smaller.
fn check_decreasing_argument(
    def_name: &str,
    args: &[Rc<Term>],
    ctx: &TerminationCtx,
) -> Result<(), TypeError> {
    let Some(rec_arg_term) = args.get(ctx.rec_arg_pos) else {
        // A partial application that stops before the decreasing argument is a function that
        // can later be applied to any value; accepting it (as this check once did) admitted
        // non-terminating total definitions.
        return Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::MissingDecreasingArgument {
                arg_position: ctx.rec_arg_pos,
                supplied: args.len(),
            },
        });
    };
    if !is_smaller(rec_arg_term, ctx) {
        return Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::NonSmallerArgument {
                arg_term: rec_arg_term.clone(),
                arg_position: ctx.rec_arg_pos,
                smaller_vars: ctx.smaller_vars.clone(),
            },
        });
    }
    Ok(())
}

/// Peel n lambdas from a term, returning the body
fn peel_lambdas(t: &Rc<Term>, n: usize) -> Rc<Term> {
    if n == 0 {
        return t.clone();
    }
    match &**t {
        Term::Lam(_, body, _, _) => peel_lambdas(body, n - 1),
        _ => t.clone(),
    }
}

fn is_recursive_alias_value(t: &Rc<Term>, def_name: &str, ctx: &TerminationCtx) -> bool {
    match &**t {
        Term::Const(name, _) if name == def_name => true,
        Term::Var(idx) => ctx.is_recursive_alias(*idx),
        _ => false,
    }
}

fn is_mutual_recursive_alias_value(
    t: &Rc<Term>,
    mutual_names: &[&str],
    ctx: &TerminationCtx,
) -> bool {
    match &**t {
        Term::Const(name, _) => mutual_names.contains(&name.as_str()),
        Term::Var(idx) => ctx.is_recursive_alias(*idx),
        _ => false,
    }
}

fn is_recursive_alias_value_for_set(
    t: &Rc<Term>,
    recursive_names: &[&str],
    ctx: &TerminationCtx,
) -> bool {
    match &**t {
        Term::Const(name, _) => recursive_names.contains(&name.as_str()),
        Term::Var(idx) => ctx.is_recursive_alias(*idx),
        _ => false,
    }
}

/// Check recursive calls with full termination context
fn check_recursive_calls_ctx(
    env: &Env,
    def_name: &str,
    t: &Rc<Term>,
    ctx: &TerminationCtx,
) -> Result<(), TypeError> {
    match &**t {
        Term::Const(name, _) if name == def_name => Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::BareRecursiveReference,
        }),
        Term::Var(idx) if ctx.is_recursive_alias(*idx) => Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::BareRecursiveReference,
        }),
        Term::App(_, _, _) => {
            // Check if this is an application of the recursor
            if let Some((ind_name, rec_args)) = extract_rec_app(t) {
                return check_rec_app(env, def_name, &ind_name, &rec_args, ctx);
            }

            // Check if this is a recursive call
            if let Some(args) = extract_app_to_const(t, def_name) {
                // Verify the recursive argument is smaller
                check_decreasing_argument(def_name, &args, ctx)?;
                // Check arguments for nested recursive calls
                for arg in &args {
                    check_recursive_calls_ctx(env, def_name, arg, ctx)?;
                }
                Ok(())
            } else if let Some((var_idx, args)) = extract_app_to_var(t) {
                if ctx.is_recursive_alias(var_idx) {
                    // Verify the recursive argument is smaller
                    check_decreasing_argument(def_name, &args, ctx)?;
                    for arg in &args {
                        check_recursive_calls_ctx(env, def_name, arg, ctx)?;
                    }
                    Ok(())
                } else {
                    // Not a recursive call, check subterms
                    let (f, a) = match &**t {
                        Term::App(f, a, _) => (f, a),
                        _ => unreachable!(),
                    };
                    check_recursive_calls_ctx(env, def_name, f, ctx)?;
                    check_recursive_calls_ctx(env, def_name, a, ctx)
                }
            } else {
                // Not a recursive call, check subterms
                let (f, a) = match &**t {
                    Term::App(f, a, _) => (f, a),
                    _ => unreachable!(),
                };
                check_recursive_calls_ctx(env, def_name, f, ctx)?;
                check_recursive_calls_ctx(env, def_name, a, ctx)
            }
        }
        Term::Lam(ty, body, _, _) => {
            check_recursive_calls_ctx(env, def_name, ty, ctx)?;
            check_recursive_calls_ctx(env, def_name, body, &ctx.shift())
        }
        Term::Pi(dom, cod, _, _) => {
            check_recursive_calls_ctx(env, def_name, dom, ctx)?;
            check_recursive_calls_ctx(env, def_name, cod, &ctx.shift())
        }
        Term::Fix(ty, body) => {
            check_recursive_calls_ctx(env, def_name, ty, ctx)?;
            check_recursive_calls_ctx(env, def_name, body, &ctx.shift())
        }
        Term::LetE(ty, val, body) => {
            check_recursive_calls_ctx(env, def_name, ty, ctx)?;
            let is_alias = is_recursive_alias_value(val, def_name, ctx);
            if !is_alias {
                check_recursive_calls_ctx(env, def_name, val, ctx)?;
            }
            // If val is a smaller variable, body's bound var is also smaller
            let mut body_ctx = if is_smaller(val, ctx) {
                ctx.shift().add_smaller(0)
            } else {
                ctx.shift()
            };
            if is_alias {
                body_ctx = body_ctx.add_recursive_alias(0);
            }
            check_recursive_calls_ctx(env, def_name, body, &body_ctx)
        }
        Term::Rec(_, _) => {
            // Bare recursor reference - OK
            Ok(())
        }
        Term::Meta(_) => Ok(()),
        _ => Ok(()),
    }
}

/// Extract a recursor application: Rec I args...
fn extract_rec_app(t: &Rc<Term>) -> Option<(String, Vec<Rc<Term>>)> {
    let mut args = Vec::new();
    let mut curr = t.clone();

    while let Term::App(f, a, _) = &*curr {
        args.push(a.clone());
        curr = f.clone();
    }

    match &*curr {
        Term::Rec(ind_name, _) => {
            args.reverse();
            Some((ind_name.clone(), args))
        }
        _ => None,
    }
}

fn recursor_major_arg(decl: &InductiveDecl, args: &[Rc<Term>]) -> Option<Rc<Term>> {
    let (binders, _) = extract_pi_binders(&decl.ty);
    let num_indices = binders.len().saturating_sub(decl.num_params);
    let minor_start = decl.num_params + 1;
    let minor_end = minor_start + decl.ctors.len();
    let major_idx = minor_end + num_indices;
    args.get(major_idx).cloned()
}

/// The recursive fields bound by a recursor's minor premises are structurally smaller than the
/// decreasing argument only when the recursor is applied to a major premise that is the
/// decreasing argument itself or is already smaller than it. Marking them smaller for every
/// recursor application admitted non-terminating total definitions: a recursor whose major
/// premise is not the decreasing argument (`Rec .. (succ n)`), and a recursor applied to no
/// major premise that is later applied to an arbitrary value.
fn recursor_fields_are_smaller(
    decl: &InductiveDecl,
    rec_args: &[Rc<Term>],
    ctx: &TerminationCtx,
) -> bool {
    let Some(major) = recursor_major_arg(decl, rec_args) else {
        return false;
    };
    match &*major {
        Term::Var(v) => ctx.inferring || ctx.decreasing_var == Some(*v) || is_smaller(&major, ctx),
        _ => is_smaller(&major, ctx),
    }
}

/// Peel the binders of a minor premise and mark its recursive fields as smaller when
/// `fields_smaller` holds (`recursor_fields_are_smaller`). The induction hypothesis bound after
/// a recursive field is never smaller: it is the recursor's result on that field, not a subterm
/// of the major premise (treating it as smaller admitted a total definition that recursed on its
/// own result).
fn build_minor_premise_ctx(
    decl: &InductiveDecl,
    ctor_idx: usize,
    minor: &Rc<Term>,
    ctx: &TerminationCtx,
    fields_smaller: bool,
) -> Option<(Rc<Term>, TerminationCtx)> {
    let ctor = decl.ctors.get(ctor_idx)?;

    let mut binders_smaller = Vec::new();
    let mut curr = &ctor.ty;

    for _ in 0..decl.num_params {
        if let Term::Pi(_, body, _, _) = &**curr {
            curr = body;
        }
    }

    while let Term::Pi(dom, body, _, _) = &**curr {
        let is_rec = is_recursive_field(dom, &decl.name);
        binders_smaller.push(is_rec && fields_smaller);
        if is_rec {
            // The induction hypothesis.
            binders_smaller.push(false);
        }
        curr = body;
    }

    let total_bindings = binders_smaller.len();
    let body = open_binders(minor, total_bindings);

    let mut new_ctx = ctx.clone();
    for _ in 0..total_bindings {
        new_ctx = new_ctx.shift();
    }

    for (binder_idx, is_smaller) in binders_smaller.iter().enumerate() {
        if *is_smaller {
            let var_idx = total_bindings - 1 - binder_idx;
            new_ctx = new_ctx.add_smaller(var_idx);
        }
    }

    Some((body, new_ctx))
}

/// Check a recursor application for termination.
/// The recursor itself is terminating; recursive calls of the definition inside its minor
/// premises may use the recursive fields as smaller arguments only when the major premise is
/// the decreasing argument or smaller than it (`recursor_fields_are_smaller`), and never the
/// induction hypotheses (`build_minor_premise_ctx`).
fn check_rec_app(
    env: &Env,
    def_name: &str,
    ind_name: &str,
    args: &[Rc<Term>],
    ctx: &TerminationCtx,
) -> Result<(), TypeError> {
    // Get the inductive to understand the recursor structure
    let decl = match env.get_inductive(ind_name) {
        Some(d) => d,
        None => return Ok(()), // Unknown inductive, allow
    };

    let num_params = decl.num_params;
    let num_ctors = decl.ctors.len();

    // args layout: [params...] [motive] [minor_premises...] [indices...] [major]
    // We need to check minor premises - they contain the recursive calls

    // Skip params and motive
    let minor_start = num_params + 1;
    let minor_end = minor_start + num_ctors;
    let fields_smaller = recursor_fields_are_smaller(decl, args, ctx);

    // Check each minor premise
    for (ctor_idx, minor) in args
        .iter()
        .take(minor_end.min(args.len()))
        .skip(minor_start)
        .enumerate()
    {
        check_minor_premise(env, def_name, decl, ctor_idx, minor, ctx, fields_smaller)?;
    }

    // Check the major premise (the thing being recursed on)
    if args.len() > minor_end {
        // Check indices and major
        for arg in &args[minor_end..] {
            check_recursive_calls_ctx(env, def_name, arg, ctx)?;
        }
    }

    Ok(())
}

fn check_rec_app_mutual(
    env: &Env,
    def_name: &str,
    mutual_names: &[&str],
    ind_name: &str,
    args: &[Rc<Term>],
    ctx: &TerminationCtx,
) -> Result<(), TypeError> {
    let decl = match env.get_inductive(ind_name) {
        Some(d) => d,
        None => return Ok(()),
    };

    let minor_start = decl.num_params + 1;
    let minor_end = minor_start + decl.ctors.len();
    let fields_smaller = recursor_fields_are_smaller(decl, args, ctx);

    for (ctor_idx, minor) in args
        .iter()
        .take(minor_end.min(args.len()))
        .skip(minor_start)
        .enumerate()
    {
        check_minor_premise_mutual(
            env,
            def_name,
            mutual_names,
            decl,
            ctor_idx,
            minor,
            ctx,
            fields_smaller,
        )?;
    }

    if args.len() > minor_end {
        for arg in &args[minor_end..] {
            check_mutual_recursive_calls(env, def_name, mutual_names, arg, ctx)?;
        }
    }

    Ok(())
}

/// Check a minor premise of a recursor
fn check_minor_premise(
    env: &Env,
    def_name: &str,
    decl: &InductiveDecl,
    ctor_idx: usize,
    minor: &Rc<Term>,
    ctx: &TerminationCtx,
    fields_smaller: bool,
) -> Result<(), TypeError> {
    let (body, new_ctx) = match build_minor_premise_ctx(decl, ctor_idx, minor, ctx, fields_smaller)
    {
        Some(res) => res,
        None => return Ok(()),
    };

    check_recursive_calls_ctx(env, def_name, &body, &new_ctx)
}

#[allow(clippy::too_many_arguments)]
fn check_minor_premise_mutual(
    env: &Env,
    def_name: &str,
    mutual_names: &[&str],
    decl: &InductiveDecl,
    ctor_idx: usize,
    minor: &Rc<Term>,
    ctx: &TerminationCtx,
    fields_smaller: bool,
) -> Result<(), TypeError> {
    let (body, new_ctx) = match build_minor_premise_ctx(decl, ctor_idx, minor, ctx, fields_smaller)
    {
        Some(res) => res,
        None => return Ok(()),
    };

    check_mutual_recursive_calls(env, def_name, mutual_names, &body, &new_ctx)
}

/// Check if a type is a recursive reference to the inductive being defined
fn is_recursive_field(ty: &Rc<Term>, ind_name: &str) -> bool {
    let head = get_head(ty);
    match &*head {
        Term::Ind(name, _) => name == ind_name,
        _ => false,
    }
}

/// Extract arguments if term is an application of the given constant
fn extract_app_to_const(t: &Rc<Term>, name: &str) -> Option<Vec<Rc<Term>>> {
    let mut args = Vec::new();
    let mut curr = t.clone();

    while let Term::App(f, a, _) = &*curr {
        args.push(a.clone());
        curr = f.clone();
    }

    match &*curr {
        Term::Const(n, _) if n == name => {
            args.reverse();
            Some(args)
        }
        _ => None,
    }
}

/// Extract arguments if term is an application of a variable
fn extract_app_to_var(t: &Rc<Term>) -> Option<(usize, Vec<Rc<Term>>)> {
    let mut args = Vec::new();
    let mut curr = t.clone();

    while let Term::App(f, a, _) = &*curr {
        args.push(a.clone());
        curr = f.clone();
    }

    match &*curr {
        Term::Var(idx) => {
            args.reverse();
            Some((*idx, args))
        }
        _ => None,
    }
}

/// Check if a term is "smaller" than the original recursive argument
fn is_smaller(t: &Rc<Term>, ctx: &TerminationCtx) -> bool {
    match &**t {
        Term::Var(v) => ctx.smaller_vars.contains(v),
        // Only variables bound to structurally smaller fields count. (An earlier version also
        // accepted any application of a constant named `proj` to a smaller term, by name alone;
        // no such projection exists, and a user definition of that name made a non-terminating
        // total definition pass the check.)
        _ => false,
    }
}

// =============================================================================
// Well-Founded Recursion Infrastructure
// =============================================================================

/// Marker for well-founded recursion
/// A function can use well-founded recursion if it provides:
/// 1. A well-founded relation R on the decreasing argument type
/// 2. An accessibility proof that all values are accessible under R
/// 3. Recursive calls must be on R-smaller values
#[derive(Debug, Clone)]
pub struct WellFoundedSpec {
    /// Name of the well-founded relation (e.g., "lt" for natural numbers)
    pub relation: String,
    /// The type of values being compared
    pub value_type: Rc<Term>,
    /// Proof that the relation is well-founded (type: forall x, Acc R x)
    pub wf_proof: Option<Rc<Term>>,
    /// The decreasing argument position
    pub decreasing_arg: usize,
}

/// Context for well-founded recursion checking
#[derive(Debug, Clone)]
pub struct WellFoundedCtx {
    /// Name of the well-founded relation
    pub relation: String,
    /// Type of values in the relation
    pub value_type: Rc<Term>,
    /// Parameter position of the decreasing argument (in the function type)
    pub dec_arg_pos: usize,
    /// Parameter position of the Acc proof (in the function type)
    pub acc_param_pos: usize,
    /// Depth inside Acc.rec minor premises
    acc_rec_depth: usize,
    /// Functions producing Acc proofs (from Acc.rec minor premises)
    acc_fns: Vec<usize>,
    /// Acc proofs derived in scope, mapped to the target term they justify
    acc_proofs: HashMap<usize, Rc<Term>>,
}

impl WellFoundedCtx {
    pub fn new(
        relation: String,
        value_type: Rc<Term>,
        dec_arg_pos: usize,
        acc_param_pos: usize,
    ) -> Self {
        WellFoundedCtx {
            relation,
            value_type,
            dec_arg_pos,
            acc_param_pos,
            acc_rec_depth: 0,
            acc_fns: Vec::new(),
            acc_proofs: HashMap::new(),
        }
    }

    /// Shift indices when going under a binder
    pub fn shift(&self) -> Self {
        let acc_fns = self.acc_fns.iter().map(|v| v + 1).collect();
        let acc_proofs = self
            .acc_proofs
            .iter()
            .map(|(v, target)| (*v + 1, target.shift(0, 1)))
            .collect();
        WellFoundedCtx {
            relation: self.relation.clone(),
            value_type: self.value_type.clone(),
            dec_arg_pos: self.dec_arg_pos,
            acc_param_pos: self.acc_param_pos,
            acc_rec_depth: self.acc_rec_depth,
            acc_fns,
            acc_proofs,
        }
    }

    /// Enter a well-founded recursion context (Acc.rec minor premise)
    pub fn enter_acc_rec(&self) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.acc_rec_depth += 1;
        new_ctx
    }

    /// Add a new Acc proof function (from Acc.rec minor premise)
    pub fn add_acc_fn(&self, fn_var: usize) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.acc_fns.push(fn_var);
        new_ctx
    }

    /// Add a derived Acc proof for a target term
    pub fn add_acc_proof(&self, proof_var: usize, target: Rc<Term>) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.acc_proofs.insert(proof_var, target);
        new_ctx
    }

    pub fn acc_proof_target(&self, var: usize) -> Option<Rc<Term>> {
        self.acc_proofs.get(&var).cloned()
    }

    pub fn has_acc_fn(&self, var: usize) -> bool {
        self.acc_fns.contains(&var)
    }

    pub fn in_acc_rec(&self) -> bool {
        self.acc_rec_depth > 0
    }
}

/// Detailed errors for well-founded recursion
#[derive(Debug, Clone)]
pub enum WellFoundedError {
    /// The accessibility proof has the wrong type
    InvalidAccProof {
        expected_type: String,
        actual_type: String,
    },
    /// Recursive call on a value without accessibility proof
    NoAccessibilityProof { value: Rc<Term> },
    /// The relation is not defined
    UndefinedRelation(String),
    /// Acc type is not in the environment
    AccTypeNotFound,
    /// Well-founded definition is missing an Acc proof parameter
    MissingAccParameter { relation: String },
    /// Recursive call uses an Acc proof that does not match the decreasing argument
    MismatchedAccTarget {
        expected: Rc<Term>,
        actual: Rc<Term>,
    },
}

impl std::fmt::Display for WellFoundedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WellFoundedError::InvalidAccProof {
                expected_type,
                actual_type,
            } => {
                write!(
                    f,
                    "invalid accessibility proof: expected {}, got {}",
                    expected_type, actual_type
                )
            }
            WellFoundedError::NoAccessibilityProof { value } => {
                write!(
                    f,
                    "recursive call on {:?} without accessibility proof",
                    value
                )
            }
            WellFoundedError::UndefinedRelation(name) => {
                write!(f, "undefined well-founded relation: {}", name)
            }
            WellFoundedError::AccTypeNotFound => {
                write!(
                    f,
                    "Acc type not found in environment (required for well-founded recursion)"
                )
            }
            WellFoundedError::MissingAccParameter { relation } => {
                write!(f, "missing Acc proof parameter for relation {}", relation)
            }
            WellFoundedError::MismatchedAccTarget { expected, actual } => {
                write!(
                    f,
                    "recursive call uses Acc proof for {:?}, but decreasing argument is {:?}",
                    expected, actual
                )
            }
        }
    }
}

/// Check termination using a well-founded relation
/// This is more general than structural recursion but requires explicit proofs
///
/// Well-founded recursion works by:
/// 1. The function takes an extra "accessibility proof" argument: Acc R x
/// 2. To recurse on y, we need to show R y x and extract Acc R y from our proof
/// 3. The Acc.rec eliminator ensures this pattern terminates
pub fn check_wellfounded_termination(
    env: &Env,
    def_name: &str,
    ty: &Rc<Term>,
    body: &Rc<Term>,
    spec: &WellFoundedSpec,
) -> Result<(), TypeError> {
    fn wf_error(def_name: &str, err: WellFoundedError) -> TypeError {
        TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::WellFoundedError(err),
        }
    }

    if contains_fix(body) {
        return Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::GeneralRecursion,
        });
    }

    // 1. Acc must exist in the environment.
    let acc_decl = env
        .get_inductive("Acc")
        .ok_or_else(|| wf_error(def_name, WellFoundedError::AccTypeNotFound))?;

    // 2. Relation must exist.
    if env.get_definition(&spec.relation).is_none() && env.get_inductive(&spec.relation).is_none() {
        return Err(wf_error(
            def_name,
            WellFoundedError::UndefinedRelation(spec.relation.clone()),
        ));
    }

    // 3. Verify the well-foundedness proof type (if provided).
    if let Some(ref wf_proof) = spec.wf_proof {
        let ctx = Context::new();
        let proof_ty = infer(env, &ctx, wf_proof.clone())?;
        if !is_wellfoundedness_proof_type(&proof_ty, &spec.relation, &spec.value_type) {
            return Err(wf_error(
                def_name,
                WellFoundedError::InvalidAccProof {
                    expected_type: "forall x, Acc R x".to_string(),
                    actual_type: format!("{:?}", proof_ty),
                },
            ));
        }
    }

    // 4. Extract function parameters and locate the Acc proof parameter.
    let mut param_types = Vec::new();
    let mut curr_ty = ty.clone();
    while let Term::Pi(dom, cod, _, _) = &*curr_ty {
        param_types.push(dom.clone());
        curr_ty = cod.clone();
    }

    let acc_param_pos = find_acc_param_index(&param_types, &spec.relation, spec.decreasing_arg)
        .ok_or_else(|| {
            wf_error(
                def_name,
                WellFoundedError::MissingAccParameter {
                    relation: spec.relation.clone(),
                },
            )
        })?;

    // 5. Check that recursive calls are justified by Acc.rec usage.
    let num_params = param_types.len();
    let inner_body = peel_lambdas(body, num_params);
    let wf_ctx = WellFoundedCtx::new(
        spec.relation.clone(),
        spec.value_type.clone(),
        spec.decreasing_arg,
        acc_param_pos,
    );
    check_wellfounded_calls(def_name, &inner_body, &wf_ctx, acc_decl)?;
    Ok(())
}

/// Check if a type represents a well-foundedness proof: forall x : T, Acc R x
fn is_wellfoundedness_proof_type(ty: &Rc<Term>, relation: &str, value_type: &Rc<Term>) -> bool {
    // Expected structure: Pi (x : T) (Acc R x)
    if let Term::Pi(dom, body, _, _) = &**ty {
        if dom.as_ref() != value_type.as_ref() {
            return false;
        }
        if let Some(target) = acc_type_target(body, relation) {
            return matches!(&*target, Term::Var(0));
        }
    }
    false
}

fn find_acc_param_index(
    param_types: &[Rc<Term>],
    relation: &str,
    decreasing_arg: usize,
) -> Option<usize> {
    for (idx, ty) in param_types.iter().enumerate() {
        if idx <= decreasing_arg {
            continue;
        }
        let dec_var_idx = idx - 1 - decreasing_arg;
        if acc_type_matches_var(ty, relation, dec_var_idx) {
            return Some(idx);
        }
    }
    None
}

fn acc_type_matches_var(ty: &Rc<Term>, relation: &str, target_var: usize) -> bool {
    if let Some(target) = acc_type_target(ty, relation) {
        matches!(&*target, Term::Var(v) if *v == target_var)
    } else {
        false
    }
}

fn acc_type_target(ty: &Rc<Term>, relation: &str) -> Option<Rc<Term>> {
    let args = extract_inductive_args(ty, "Acc")?;
    if args.len() < 3 {
        return None;
    }
    match &*args[1] {
        Term::Const(name, _) | Term::Ind(name, _) if name == relation => {}
        _ => return None,
    }
    args.last().cloned()
}

fn is_acc_fn_type(ty: &Rc<Term>, relation: &str) -> bool {
    let (_binders, res) = peel_pi_binders(ty);
    acc_type_target(&res, relation).is_some()
}

fn acc_proof_target_from_term(t: &Rc<Term>, ctx: &WellFoundedCtx) -> Option<Rc<Term>> {
    if let Term::Var(v) = &**t {
        if let Some(target) = ctx.acc_proof_target(*v) {
            return Some(target);
        }
    }
    let (head, args) = collect_app_spine(t);
    if let Term::Var(v) = &*head {
        if ctx.has_acc_fn(*v) && !args.is_empty() {
            return Some(args[0].arg.clone());
        }
    }
    None
}

/// Check that recursive calls in a well-founded recursive function are valid
fn check_wellfounded_calls(
    def_name: &str,
    t: &Rc<Term>,
    ctx: &WellFoundedCtx,
    acc_decl: &InductiveDecl,
) -> Result<(), TypeError> {
    let wf_error = |err: WellFoundedError| TypeError::TerminationError {
        def_name: def_name.to_string(),
        details: TerminationErrorDetails::WellFoundedError(err),
    };

    match &**t {
        Term::Const(name, _) if name == def_name => {
            // Bare reference to the function - OK (checked when applied)
            Ok(())
        }
        Term::App(_, _, _) => {
            // Check if this is an application of Acc.rec
            // Acc.rec provides smaller accessibility proofs to its argument
            if let Some((ind_name, args)) = extract_rec_app(t) {
                if ind_name == "Acc" {
                    let num_params = acc_decl.num_params;
                    let num_ctors = acc_decl.ctors.len();
                    let minors_start = num_params + 1;
                    let minors_end = minors_start + num_ctors;

                    // Params + motive
                    for arg in args.iter().take(minors_start) {
                        check_wellfounded_calls(def_name, arg, ctx, acc_decl)?;
                    }

                    // Minor premises (Acc.rec body)
                    for arg in args.iter().skip(minors_start).take(num_ctors) {
                        let minor_ctx = ctx.enter_acc_rec();
                        check_wellfounded_calls(def_name, arg, &minor_ctx, acc_decl)?;
                    }

                    // Indices + major (and any extra args, if over-applied)
                    for arg in args.iter().skip(minors_end) {
                        check_wellfounded_calls(def_name, arg, ctx, acc_decl)?;
                    }

                    return Ok(());
                }

                for arg in &args {
                    check_wellfounded_calls(def_name, arg, ctx, acc_decl)?;
                }
                return Ok(());
            }

            // Check if this is a recursive call
            if let Some(args) = extract_app_to_const(t, def_name) {
                let needed = ctx.dec_arg_pos.max(ctx.acc_param_pos);
                if args.len() <= needed {
                    return Err(wf_error(WellFoundedError::NoAccessibilityProof {
                        value: t.clone(),
                    }));
                }

                let dec_arg = &args[ctx.dec_arg_pos];
                let acc_arg = &args[ctx.acc_param_pos];
                let target = acc_proof_target_from_term(acc_arg, ctx).ok_or_else(|| {
                    wf_error(WellFoundedError::NoAccessibilityProof {
                        value: acc_arg.clone(),
                    })
                })?;

                if dec_arg.as_ref() != target.as_ref() {
                    return Err(wf_error(WellFoundedError::MismatchedAccTarget {
                        expected: target,
                        actual: dec_arg.clone(),
                    }));
                }

                for arg in &args {
                    check_wellfounded_calls(def_name, arg, ctx, acc_decl)?;
                }
                return Ok(());
            }

            // Regular application - check both parts
            let (f, args) = collect_app_spine(t);
            check_wellfounded_calls(def_name, &f, ctx, acc_decl)?;
            for arg in &args {
                check_wellfounded_calls(def_name, &arg.arg, ctx, acc_decl)?;
            }
            Ok(())
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) | Term::Fix(ty, body) => {
            check_wellfounded_calls(def_name, ty, ctx, acc_decl)?;
            let mut next_ctx = ctx.shift();
            if ctx.in_acc_rec() {
                if is_acc_fn_type(ty, &ctx.relation) {
                    next_ctx = next_ctx.add_acc_fn(0);
                }
                if let Some(target) = acc_type_target(ty, &ctx.relation) {
                    next_ctx = next_ctx.add_acc_proof(0, target.shift(0, 1));
                }
            }
            check_wellfounded_calls(def_name, body, &next_ctx, acc_decl)
        }
        Term::LetE(ty, val, body) => {
            check_wellfounded_calls(def_name, ty, ctx, acc_decl)?;
            check_wellfounded_calls(def_name, val, ctx, acc_decl)?;
            let mut next_ctx = ctx.shift();
            if ctx.in_acc_rec() {
                if let Some(target) = acc_proof_target_from_term(val, ctx) {
                    next_ctx = next_ctx.add_acc_proof(0, target.shift(0, 1));
                }
            }
            check_wellfounded_calls(def_name, body, &next_ctx, acc_decl)
        }
        _ => Ok(()),
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
    if matches!(crate::ast::normalize_level(l2.clone()), Level::Zero) {
        Level::Zero // If codomain is Prop, result is Prop
    } else {
        level_max(l1, l2)
    }
}

/// Reduce a level to a simpler form if possible
pub fn reduce_level(l: Level) -> Level {
    crate::ast::normalize_level(l)
}

fn level_is_zero(level: &Level) -> bool {
    matches!(reduce_level(level.clone()), Level::Zero)
}

/// `left <= right` for EVERY assignment of the universe-level parameters (sound, not complete:
/// `false` means "not provably"). Both sides are normalised first (`normalize_level` keeps
/// `imax a b` symbolic unless `b` is provably zero or provably nonzero). The comparison is the
/// one of Lean 4's kernel (`is_geq`): `max`/`imax` on either side, then levels of the form
/// `succ^k base` compared by offset (`u + 1 <= max u v + 1` holds, `1 <= imax 1 u` does not,
/// since `u` may be 0). `normalize_level` writes `max (succ a) (succ b)` as `succ (max a b)`,
/// while Lean's normal form distributes `succ` over `max`; the comparison therefore first
/// rewrites `succ^k (max a b)` (k > 0) on either side to `max (succ^k a) (succ^k b)` (equal for
/// every assignment), so that e.g. `u + 1 <= max u v + 2` holds.
fn level_leq(left: &Level, right: &Level) -> bool {
    level_geq_normalized(&reduce_level(right.clone()), &reduce_level(left.clone()))
}

/// `succ^k (max a b)` with `k > 0` rewritten to `max (succ^k a) (succ^k b)`; `None` for any other
/// level. Both forms are equal for every assignment of the level parameters.
fn distribute_succ_over_max(level: &Level) -> Option<Level> {
    let (base, k) = level_offset(level);
    match base {
        Level::Max(a, b) if k > 0 => {
            let lift = |inner: &Level| {
                let mut lifted = inner.clone();
                for _ in 0..k {
                    lifted = Level::Succ(Box::new(lifted));
                }
                lifted
            };
            Some(Level::Max(Box::new(lift(a)), Box::new(lift(b))))
        }
        _ => None,
    }
}

/// `l1 >= l2` for normalised levels (see `level_leq`).
fn level_geq_normalized(l1: &Level, l2: &Level) -> bool {
    if l1 == l2 || matches!(l2, Level::Zero) {
        return true;
    }
    if let Some(l2) = distribute_succ_over_max(l2) {
        return level_geq_normalized(l1, &l2);
    }
    if let Some(l1) = distribute_succ_over_max(l1) {
        return level_geq_normalized(&l1, l2);
    }
    if let Level::Max(a, b) = l2 {
        return level_geq_normalized(l1, a) && level_geq_normalized(l1, b);
    }
    if let Level::Max(a, b) = l1 {
        if level_geq_normalized(a, l2) || level_geq_normalized(b, l2) {
            return true;
        }
    }
    // imax a b <= max a b
    if let Level::IMax(a, b) = l2 {
        return level_geq_normalized(l1, a) && level_geq_normalized(l1, b);
    }
    // imax a b >= b
    if let Level::IMax(_, b) = l1 {
        return level_geq_normalized(b, l2);
    }
    let (base1, k1) = level_offset(l1);
    let (base2, k2) = level_offset(l2);
    if base1 == base2 || matches!(base2, Level::Zero) {
        return k1 >= k2;
    }
    if k1 == k2 && k1 > 0 {
        return level_geq_normalized(base1, base2);
    }
    false
}

/// Splits `succ^k base` (with `base` not a `succ`) into `(base, k)`.
fn level_offset(level: &Level) -> (&Level, usize) {
    let mut base = level;
    let mut k = 0usize;
    while let Level::Succ(inner) = base {
        base = inner;
        k += 1;
    }
    (base, k)
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
pub fn compute_recursor_type(decl: &InductiveDecl, univ_levels: &[Level]) -> Rc<Term> {
    // 1. Extract parameters and indices from decl.ty
    let (all_binders, _sort_level) = extract_pi_binders(&decl.ty);

    // Split binders into params and indices
    let num_params = decl.num_params;
    let index_binders = &all_binders[num_params..];
    let param_binders = &all_binders[0..num_params];

    // 2. Build Motive type
    // Motive: (indices...) -> (t: Ind params indices...) -> Sort u
    // Convention: universe levels are [params..., result]; result is after all params.
    let result_level = univ_levels
        .get(decl.univ_params.len())
        .cloned()
        .unwrap_or(Level::Zero);
    let motive_result_sort = Term::sort(result_level);

    let mut motive_ty = motive_result_sort;

    // Add (t : Ind params indices)
    let mut ind_app = Term::ind(decl.name.clone());
    // Apply parameters (from outer scope of Rec)
    // In Motive type, we are binding [Indices]. Params are bound outside Motive.
    // Distance to Params: index_binders.len() + (num_params - 1 - i).
    // Actually, Params are [P_0 ... P_n]. Last param is P_n (Var 0).
    // So P_i is Var(num_params - 1 - i).
    // Relative to Motive context (Indices bound), add indices.len().
    for i in 0..num_params {
        let idx = index_binders.len() + (num_params - 1 - i);
        ind_app = Term::app(ind_app, Term::var(idx));
    }
    // Apply indices (from current Motive scope)
    for i in 0..index_binders.len() {
        let idx = index_binders.len() - 1 - i;
        ind_app = Term::app(ind_app, Term::var(idx));
    }
    motive_ty = Term::pi(ind_app, motive_ty, crate::ast::BinderInfo::Default);

    // Wrap indices binders for Motive
    for (ty, info) in index_binders.iter().rev() {
        motive_ty = Term::pi(ty.clone(), motive_ty, *info);
    }

    // 3. Construct ResultType

    // Compute Minor types first to know depth
    let num_ctors = decl.ctors.len();
    let mut minor_types = Vec::new();
    for (ctor_idx, ctor) in decl.ctors.iter().enumerate() {
        // compute_minor_premise_type handles param stripping/instantiation.
        // It returns type relative to [Params] [Motive] [PrevMinors].
        minor_types.push(compute_minor_premise_type(
            &decl.name, ctor_idx, ctor, num_ctors, num_params,
        ));
    }

    // Now build Result Body: Motive indices... Major
    // Context: [Params] [Motive] [Minors] [Indices] [Major]
    // Major is at 0. Indices at 1..
    // Motive is at: 1 + indices.len() + minors.len().

    let motive_idx = 1 + index_binders.len() + minor_types.len();
    let mut result_body = Term::var(motive_idx);

    // Apply indices (from Indices binds)
    for i in 0..index_binders.len() {
        // Index i is at: 1 + (len - 1 - i)
        let idx = 1 + (index_binders.len() - 1 - i);
        result_body = Term::app(result_body, Term::var(idx));
    }
    // Apply Major (at 0)
    result_body = Term::app(result_body, Term::var(0));

    // Bind Major: (t : Ind params indices)
    let mut major_ty = Term::ind(decl.name.clone());
    // Apply Params
    for i in 0..num_params {
        // Params are outside Motive/Minors/Indices. At this point the Major binder
        // has NOT been added yet, so we should not offset by the Major.
        // Using motive_idx (which includes the major offset) without the extra +1.
        let p_idx = motive_idx + (num_params - 1 - i);
        major_ty = Term::app(major_ty, Term::var(p_idx));
    }
    // Apply Indices
    for i in 0..index_binders.len() {
        // Indices are the innermost binders before adding Major.
        let idx = index_binders.len() - 1 - i;
        major_ty = Term::app(major_ty, Term::var(idx));
    }

    result_body = Term::pi(major_ty, result_body, crate::ast::BinderInfo::Default);

    // Bind Indices
    for (k, (ty, info)) in index_binders.iter().enumerate().rev() {
        // In `decl.ty` the type of index k is written over [Params] [I_0 .. I_{k-1}].
        // Here its context is [Params] [Motive] [Minors] [I_0 .. I_{k-1}].
        // References to the k earlier indices (Var(i), i < k) are unchanged; references to
        // the parameters (Var(i), i >= k) move outward by the motive and the minors.
        // (A cutoff of 0 also shifted references to earlier indices, so an index whose type
        // depends on an earlier index was typed by the motive, a minor or another index.)
        result_body = Term::pi(ty.shift(k, 1 + minor_types.len()), result_body, *info);
    }

    // Bind Minors
    for ty in minor_types.iter().rev() {
        result_body = Term::pi(ty.clone(), result_body, crate::ast::BinderInfo::Default);
    }

    // Bind Motive
    result_body = Term::pi(motive_ty, result_body, crate::ast::BinderInfo::Default);

    // Bind Params
    for (ty, info) in param_binders.iter().rev() {
        result_body = Term::pi(ty.clone(), result_body, *info);
    }

    result_body
}

// Helper to extract Pi binders (params)
fn extract_pi_binders(term: &Rc<Term>) -> (Vec<(Rc<Term>, BinderInfo)>, Option<Level>) {
    let mut binders = Vec::new();
    let mut current = term.clone();
    loop {
        match &*current {
            Term::Pi(ty, body, info, _) => {
                binders.push((ty.clone(), *info));
                current = body.clone();
            }
            Term::Sort(l) => {
                return (binders, Some(l.clone()));
            }
            _ => return (binders, None),
        }
    }
}

/// Lift a term written over `[outer][f_0 .. f_{j-1}]` (the constructor's own telescope, with the
/// first `j` fields bound) into the minor premise telescope, where the induction hypothesis of
/// every recursive field `f_m` is bound right after `f_m`. `rec_fields[m]` says whether `f_m` is
/// recursive (only `m < j` is consulted).
///
/// Inserting the binder `ih_m` right after `f_m` moves every variable that refers to `f_m` or to
/// a binder outside it (`Var(k)` with `k >= j - 1 - m`) one step outward, and leaves references to
/// the later fields `f_{m+1} .. f_{j-1}` unchanged. The insertions are applied from the outermost
/// field inward, so the cutoff `j - 1 - m` of each later insertion is still the index of `f_m`.
/// (Shifting every free variable by the total number of induction hypotheses, as this function
/// replaced, mis-indexed references to fields that follow a recursive field: the minor premise
/// then bound a field at a type other than its declared one, and the kernel admitted closed
/// proofs of `False`.)
fn lift_over_induction_hypotheses(term: &Rc<Term>, rec_fields: &[bool], j: usize) -> Rc<Term> {
    let mut lifted = term.clone();
    for (m, is_rec) in rec_fields.iter().enumerate().take(j) {
        if *is_rec {
            lifted = lifted.shift(j - 1 - m, 1);
        }
    }
    lifted
}

/// Compute the type of a minor premise for a constructor.
/// This handles constructors with arbitrary arguments and recursive arguments.
///
/// For a constructor `ctor : (x1 : A1) -> ... -> (xn : An) -> Ind is` the minor premise binds the
/// fields at their declared types, each recursive field immediately followed by its induction
/// hypothesis, and ends in the motive applied to the constructor:
/// `(x1 : A1) -> [ih1 : C js1 x1] -> ... -> (xn : An) -> [ihn : C jsn xn] -> C is (ctor x1 ... xn)`
/// (`[..]` only for recursive fields; `jsk` are the indices of `xk`'s type). Every type in this
/// telescope is the constructor's one, lifted over the induction hypotheses bound before it
/// (`lift_over_induction_hypotheses`). This is the order in which iota reduction
/// (`nbe::try_reduce_rec`) applies a minor premise: field, then its IH.
fn compute_minor_premise_type(
    ind_name: &str,
    ctor_idx: usize,
    ctor: &Constructor,
    _num_ctors: usize,
    num_params: usize,
) -> Rc<Term> {
    // 0. Instantiate constructor type with parameters
    //    We assume ctor.ty starts with `num_params` Pis that match the inductive params.
    //    We need to substitute them with Vars pointing to the `Rec` parameters.
    //    Context: [Params] [Motive] [Previous Minors]
    //    We are defining the *type* of the current Minor.
    //    So Params are at de Bruijn index: (number of minors so far) + 1 (motive).
    //    Actually, we compute this type *outside* the minor binder itself.
    //    So context is: `[Params] [Motive] [Minors 0..idx-1]`.
    //    Depth = idx (number of previous minors) + 1 (motive) + num_params.
    //    Param 0 (last param) is at `idx + 1`.
    //    Param k (first param) is at `idx + 1 + num_params - 1`.

    //    We need to peel `num_params` Pis from `ctor.ty` and substitute.
    //    Instead of actual substitution (costly?), we can just `extract_ctor_args` starting deeper?
    //    But `extract_ctor_args` needs `ty` to preserve dependencies on previous args.
    //    If `ctor.ty` is `Pi (T:Type) -> Pi (x:T) ...`, if we just skip first Pi, `x`'s type `T` refers to Var(0).
    //    If we skip, `x`'s type `T` is dangling (Var 0 but 0 is gone).
    //    So we MUST substitute.

    let mut instantiated_ty = ctor.ty.clone();
    let current_depth_to_params = ctor_idx + 1; // +1 for Motive

    // Substitute first `num_params` arguments.
    // Requires peeling Pi and subst.
    // Or just `instantiate` helper?
    // LRL doesn't have `instantiate` helper for multiple args easily.
    // We do it one by one.

    for i in 0..num_params {
        if let Term::Pi(_, body, _, _) = &*instantiated_ty {
            // The param we want to supply is `Param[i]`.
            // Params are bound: P0, P1, ... Pn.
            // Inside Rec: P0 is at ... ?
            // `param_binders` loop: `Term::pi(ty, result)`.
            // rev() iterator implies P_last is innermost?
            // `Rec` type structure: `Pi P_n ... Pi P_0 ...` ?
            // Step 2773: `for (name, ty) in param_binders.iter().rev()`.
            // `param_binders` usually `[A, B]`. `rev` gives `B, A`.
            // So `Pi B. Pi A. ...`.
            // So `A` is at 0, `B` is at 1. (Relative to Params scope).
            // Wait. `Pi A. Pi B.` means A is at 1, B is at 0.
            // If `decl.ty` is `Pi A. Pi B. ...`
            // `extract_pi_binders` pushes `A` then `B`.
            // `param_binders` = `[A, B]`.
            // `rev()` iterates `B`, then `A`.
            // Logic: `result = Term::pi(A, result)`. (Because last loop iteration wraps outer).
            // So result looks like `Pi A. Pi B. ...`.
            // So A is outer (Var 1), B is inner (Var 0).
            // OK.

            // `ctor.ty` should be `Pi A. Pi B. ...`.
            // We peel A. We substitute `Var(ParamA)`.
            // ParamA is at index ??
            // In `[A] [B] [Motive] [Minors...]`.
            // We are at `Minors`.
            // `B` (Param 1) is at `Minors_len + Motive_len + 0`.
            // `A` (Param 0) is at `Minors_len + Motive_len + 1`.

            // Loop `i in 0..num_params`. `i=0` is A (first param).
            // We want Var for A.
            let param_idx = current_depth_to_params + (num_params - 1 - i);

            instantiated_ty = body.subst(0, &Term::var(param_idx));
        } else {
            // Error handling? Or assume well-formed.
            // If ctor lacks params, we can't substitute.
            break;
        }
    }

    let (ctor_args, ctor_result) = peel_pi_binders(&instantiated_ty);
    let result_indices =
        extract_inductive_indices(&ctor_result, ind_name, num_params).unwrap_or_default();

    struct Binder {
        ty: Rc<Term>,
        info: BinderInfo,
        is_arg_idx: Option<usize>,
    }

    let mut binders: Vec<Binder> = Vec::new();
    // `rec_fields[m]` records whether field `m` is recursive, i.e. is followed by its induction
    // hypothesis in the minor premise telescope.
    let mut rec_fields: Vec<bool> = Vec::with_capacity(ctor_args.len());

    for (arg_idx, (arg_ty, arg_info)) in ctor_args.iter().enumerate() {
        // `arg_ty` is written over `[outer][f_0 .. f_{arg_idx-1}]`; the minor premise binds an
        // IH right after every earlier recursive field, so lift it over exactly those binders.
        binders.push(Binder {
            ty: lift_over_induction_hypotheses(arg_ty, &rec_fields, arg_idx),
            info: *arg_info,
            is_arg_idx: Some(arg_idx),
        });

        let rec_indices = extract_inductive_indices(arg_ty, ind_name, num_params);
        rec_fields.push(rec_indices.is_some());
        if let Some(rec_indices) = rec_indices {
            let c_idx = binders.len() + ctor_idx;
            let mut ih_ty = Term::var(c_idx);
            for idx_term in rec_indices.iter() {
                // Same context as the field's type, then one more binder: the field itself.
                let lifted_idx =
                    lift_over_induction_hypotheses(idx_term, &rec_fields[..arg_idx], arg_idx)
                        .shift(0, 1);
                ih_ty = Term::app(ih_ty, lifted_idx);
            }
            ih_ty = Term::app(ih_ty, Term::var(0));

            binders.push(Binder {
                ty: ih_ty,
                info: *arg_info,
                is_arg_idx: None,
            });
        }
    }

    // 3. Build result: C indices... (ctor parameters... args...)
    let total_depth = binders.len();
    let c_idx_final = total_depth + ctor_idx;

    let mut result_ty = Term::var(c_idx_final);
    for idx_term in result_indices.iter() {
        // Result indices are written over `[outer][f_0 .. f_{n-1}]`.
        let lifted_idx = lift_over_induction_hypotheses(idx_term, &rec_fields, ctor_args.len());
        result_ty = Term::app(result_ty, lifted_idx);
    }

    let ctor_term = Rc::new(Term::Ctor(ind_name.to_string(), ctor_idx, vec![]));
    let mut app_term = ctor_term;

    for i in 0..num_params {
        let param_var_idx = c_idx_final + 1 + (num_params - 1 - i);
        app_term = Term::app(app_term, Term::var(param_var_idx));
    }

    for arg_idx in 0..ctor_args.len() {
        let mut found_depth = 0;
        for (depth_from_end, b) in binders.iter().rev().enumerate() {
            if b.is_arg_idx == Some(arg_idx) {
                found_depth = depth_from_end;
                break;
            }
        }
        app_term = Term::app(app_term, Term::var(found_depth));
    }

    result_ty = Term::app(result_ty, app_term);

    let mut final_term = result_ty;
    for binder in binders.iter().rev() {
        // Minor premises are curried; later binders can capture earlier args.
        // Use FnOnce to avoid rejecting linear captures in case functions.
        final_term = Term::pi_with_kind(
            binder.ty.clone(),
            final_term,
            binder.info,
            FunctionKind::FnOnce,
        );
    }

    final_term
}

fn peel_pi_binders(ty: &Rc<Term>) -> (Vec<(Rc<Term>, BinderInfo)>, Rc<Term>) {
    let mut binders = Vec::new();
    let mut current = ty.clone();
    while let Term::Pi(dom, body, info, _) = &*current {
        binders.push((dom.clone(), *info));
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

fn extract_ctor_rec_indices(
    binders: &[Rc<Term>],
    ind_name: &str,
    num_params: usize,
) -> Vec<Option<Vec<Rc<Term>>>> {
    let mut res = Vec::with_capacity(binders.len());
    for dom in binders {
        if let Some(indices) = extract_inductive_indices(dom, ind_name, num_params) {
            res.push(Some(indices));
        } else {
            res.push(None);
        }
    }
    res
}

#[allow(dead_code)]
fn extract_ctor_args(ty: &Rc<Term>, ind_name: &str) -> Vec<(Option<String>, Rc<Term>, bool)> {
    let mut current = ty.clone();
    let mut args = Vec::new();

    while let Term::Pi(arg_ty, body, _, _) = &*current {
        // Check if arg type is the inductive type (possibly applied)
        let is_rec = {
            let mut t = arg_ty.clone();
            loop {
                match &*t {
                    Term::Ind(name, _) if name == ind_name => break true,
                    Term::App(f, _, _) => t = f.clone(),
                    _ => break false,
                }
            }
        };

        args.push((None, arg_ty.clone(), is_rec));
        current = body.clone();
    }
    args
}

fn count_pi_binders(ty: &Rc<Term>) -> usize {
    let mut count = 0;
    let mut current = ty.clone();
    while let Term::Pi(_, body, _, _) = &*current {
        count += 1;
        current = body.clone();
    }
    count
}

fn ctor_return_inductive_args(
    ind_name: &str,
    ctor_name: &str,
    ctor_ty: &Rc<Term>,
    expected_args: usize,
) -> Result<(usize, Vec<Rc<Term>>), TypeError> {
    let mut binder_count = 0;
    let mut current = ctor_ty.clone();
    while let Term::Pi(_, body, _, _) = &*current {
        binder_count += 1;
        current = body.clone();
    }

    let (head, args) = collect_app_spine(&current);
    let args: Vec<Rc<Term>> = args.into_iter().map(|item| item.arg).collect();
    match &*head {
        Term::Ind(n, _) if n == ind_name => {}
        _ => {
            return Err(TypeError::CtorNotReturningInductive {
                ind: ind_name.to_string(),
                ctor: ctor_name.to_string(),
            });
        }
    }

    if args.len() != expected_args {
        return Err(TypeError::CtorArityMismatch {
            ind: ind_name.to_string(),
            ctor: ctor_name.to_string(),
            expected: expected_args,
            got: args.len(),
        });
    }

    Ok((binder_count, args))
}

fn infer_num_params_from_ctors(decl: &InductiveDecl) -> Result<usize, TypeError> {
    let total_binders = count_pi_binders(&decl.ty);
    if decl.ctors.is_empty() {
        return Ok(total_binders);
    }

    let mut common_prefix = total_binders;
    for ctor in &decl.ctors {
        let (binder_count, args) =
            ctor_return_inductive_args(&decl.name, &ctor.name, &ctor.ty, total_binders)?;

        let max = std::cmp::min(binder_count, args.len());
        let mut prefix = 0;
        for (i, arg) in args.iter().take(max).enumerate() {
            match &**arg {
                Term::Var(idx) if *idx == (binder_count - 1 - i) => {
                    prefix += 1;
                }
                _ => break,
            }
        }
        common_prefix = common_prefix.min(prefix);
    }

    Ok(common_prefix)
}

fn map_nbe_error(err: nbe::NbeError) -> TypeError {
    match err {
        nbe::NbeError::FuelExhausted(_) => TypeError::DefEqFuelExhausted {
            context: DefEqFuelContext::Unknown,
        },
        nbe::NbeError::FixUnfoldDisallowed => TypeError::DefEqFixUnfold,
        nbe::NbeError::NonFunctionApplication => TypeError::NbeNonFunctionApplication,
        nbe::NbeError::DepthLimitExceeded { limit } => {
            TypeError::NormalizationDepthExceeded { limit }
        }
    }
}

fn map_nbe_defeq_error(err: nbe::NbeError, context: DefEqFuelContext) -> TypeError {
    match err {
        nbe::NbeError::FuelExhausted(info) => {
            let detail = DefEqFuelDetail::from_nbe(&info);
            TypeError::DefEqFuelExhausted {
                context: context.with_fuel_detail(detail),
            }
        }
        nbe::NbeError::FixUnfoldDisallowed => TypeError::DefEqFixUnfold,
        nbe::NbeError::NonFunctionApplication => TypeError::NbeNonFunctionApplication,
        nbe::NbeError::DepthLimitExceeded { limit } => {
            TypeError::NormalizationDepthExceeded { limit }
        }
    }
}

/// Normal form of `t` for type checking (despite the name, a full normal form, via NbE).
///
/// Like conversion, it never unfolds a fixpoint (`fix` is general recursion; applying one reports
/// `DefEqFixUnfold`, K0049), and one fuel budget covers the evaluation and the read-back
/// together; exhausting it reports `DefEqFuelExhausted` (K0048), and nesting deeper than
/// `nbe::MAX_EVAL_DEPTH` reports `NormalizationDepthExceeded` (K0056). (Before, the type checker's
/// normalisation unfolded fixpoints although conversion does not, and the read-back restarted
/// the budget under every binder, so it could run until the stack overflowed.)
pub fn whnf(
    env: &Env,
    t: Rc<Term>,
    transparency: crate::Transparency,
) -> Result<Rc<Term>, TypeError> {
    let fuel = nbe::default_eval_fuel();
    nbe::normalize_for_typing(&t, &vec![], env, transparency, fuel).map_err(map_nbe_error)
}

fn eval_env_from_ctx(ctx: &Context) -> Vec<crate::nbe::Value> {
    let mut eval_env = Vec::with_capacity(ctx.len());
    for level in 0..ctx.len() {
        eval_env.push(crate::nbe::Value::var(level));
    }
    eval_env
}

/// [`whnf`] for a term in the typing context `ctx` (same rules: no fixpoint unfolding, one
/// budget, depth limit).
pub fn whnf_in_ctx(
    env: &Env,
    ctx: &Context,
    t: Rc<Term>,
    transparency: crate::Transparency,
) -> Result<Rc<Term>, TypeError> {
    let eval_env = eval_env_from_ctx(ctx);
    let fuel = nbe::default_eval_fuel();
    nbe::normalize_for_typing(&t, &eval_env, env, transparency, fuel).map_err(map_nbe_error)
}

// try_iota_reduce removed

/// Definitional equality checking
/// Definitional equality checking via NbE
pub fn is_def_eq(env: &Env, t1: Rc<Term>, t2: Rc<Term>, transparency: crate::Transparency) -> bool {
    is_def_eq_result(env, t1, t2, transparency).unwrap_or(false)
}

pub fn is_def_eq_result(
    env: &Env,
    t1: Rc<Term>,
    t2: Rc<Term>,
    transparency: crate::Transparency,
) -> Result<bool, TypeError> {
    let fuel = nbe::default_eval_fuel();
    let context = DefEqFuelContext::DefEq {
        left: t1.clone(),
        right: t2.clone(),
        transparency,
        fuel,
        fuel_detail: None,
    };
    nbe::is_def_eq_result(t1, t2, env, transparency, fuel)
        .map_err(|err| map_nbe_defeq_error(err, context))
}

pub fn is_def_eq_with_fuel(
    env: &Env,
    t1: Rc<Term>,
    t2: Rc<Term>,
    transparency: crate::Transparency,
    fuel: usize,
) -> Result<bool, TypeError> {
    let context = DefEqFuelContext::DefEq {
        left: t1.clone(),
        right: t2.clone(),
        transparency,
        fuel,
        fuel_detail: None,
    };
    nbe::is_def_eq_result(t1, t2, env, transparency, fuel)
        .map_err(|err| map_nbe_defeq_error(err, context))
}

pub fn is_def_eq_in_ctx(
    env: &Env,
    ctx: &Context,
    t1: Rc<Term>,
    t2: Rc<Term>,
    transparency: crate::Transparency,
) -> Result<bool, TypeError> {
    let eval_env = eval_env_from_ctx(ctx);
    let fuel = nbe::default_eval_fuel();
    let context = DefEqFuelContext::DefEqInCtx {
        left: t1.clone(),
        right: t2.clone(),
        transparency,
        ctx_len: ctx.len(),
        fuel,
        fuel_detail: None,
    };
    nbe::is_def_eq_in_ctx_result(t1, t2, &eval_env, env, transparency, fuel)
        .map_err(|err| map_nbe_defeq_error(err, context))
}

pub fn check(
    env: &Env,
    ctx: &Context,
    term: Rc<Term>,
    expected_type: Rc<Term>,
) -> Result<(), TypeError> {
    // println!("Checking {:?} against {:?}", term, expected_type);
    ensure_type_safe(env, &expected_type)?;
    let inferred = infer(env, ctx, term.clone())?;
    if !is_def_eq_in_ctx(
        env,
        ctx,
        inferred.clone(),
        expected_type.clone(),
        crate::Transparency::Reducible,
    )? {
        if let Some((expected_label, got_label)) =
            ref_label_mismatch_in_ctx(env, ctx, &expected_type, &inferred)?
        {
            return Err(TypeError::RefLifetimeLabelMismatch {
                expected_label: format_ref_label(&expected_label),
                got_label: format_ref_label(&got_label),
                expected: expected_type,
                got: inferred,
            });
        }
        return Err(TypeError::TypeMismatch {
            expected: expected_type,
            got: inferred,
        });
    }
    Ok(())
}

/// Validate elaborator output invariants (no metas, explicit recursor levels, etc.)
pub fn validate_core_term(term: &Rc<Term>) -> Result<(), TypeError> {
    match &**term {
        Term::Meta(id) => Err(TypeError::UnresolvedMeta(*id)),
        Term::Rec(name, levels) if levels.is_empty() => {
            Err(TypeError::MissingRecursorLevel(name.clone()))
        }
        Term::App(f, a, label) => {
            if label.is_some() && parse_ref_term(term).is_none() {
                return Err(TypeError::InvalidRefLifetimeLabel { term: term.clone() });
            }
            validate_core_term(f)?;
            validate_core_term(a)
        }
        Term::Lam(ty, body, _, _) => {
            validate_core_term(ty)?;
            validate_core_term(body)
        }
        Term::Pi(ty, body, _, _) => {
            // The lifetime elision rule applies once per complete signature (the maximal
            // chain of Pis), not to each curried suffix of it; the domains and the final
            // codomain are validated on their own (they may contain further signatures).
            validate_ref_lifetime_elision_for_pi(ty, body)?;
            let mut dom = ty;
            let mut cod = body;
            loop {
                validate_core_term(dom)?;
                match &**cod {
                    Term::Pi(next_dom, next_cod, _, _) => {
                        dom = next_dom;
                        cod = next_cod;
                    }
                    _ => break,
                }
            }
            validate_core_term(cod)
        }
        Term::LetE(ty, val, body) => {
            validate_core_term(ty)?;
            validate_core_term(val)?;
            validate_core_term(body)
        }
        Term::Fix(ty, body) => {
            validate_core_term(ty)?;
            validate_core_term(body)
        }
        _ => Ok(()),
    }
}

fn parse_ref_term(term: &Rc<Term>) -> Option<(Option<String>, Rc<Term>)> {
    if let Term::App(f1, inner_ty, label) = &**term {
        if let Term::App(ref_const, kind_node, _) = &**f1 {
            if !is_const_named(ref_const, "Ref") {
                return None;
            }
            if is_const_named(kind_node, "Shared") || is_const_named(kind_node, "Mut") {
                return Some((label.clone(), inner_ty.clone()));
            }
        }
    }
    None
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum RefKind {
    Shared,
    Mut,
}

struct RefTypeParts {
    kind: RefKind,
    label: Option<String>,
    inner: Rc<Term>,
}

fn parse_ref_type_parts(term: &Rc<Term>) -> Option<RefTypeParts> {
    if let Term::App(f1, inner_ty, label) = &**term {
        if let Term::App(ref_const, kind_node, _) = &**f1 {
            if !is_const_named(ref_const, "Ref") {
                return None;
            }
            let kind = if is_const_named(kind_node, "Shared") {
                RefKind::Shared
            } else if is_const_named(kind_node, "Mut") {
                RefKind::Mut
            } else {
                return None;
            };
            return Some(RefTypeParts {
                kind,
                label: label.clone(),
                inner: inner_ty.clone(),
            });
        }
    }
    None
}

fn format_ref_label(label: &Option<String>) -> String {
    match label {
        Some(name) => format!("#[{}]", name),
        None => "<elided>".to_string(),
    }
}

fn ref_label_mismatch_in_ctx(
    env: &Env,
    ctx: &Context,
    expected: &Rc<Term>,
    got: &Rc<Term>,
) -> Result<Option<RefLabelMismatch>, TypeError> {
    let expected_whnf = whnf_in_ctx(env, ctx, expected.clone(), crate::Transparency::Reducible)?;
    let got_whnf = whnf_in_ctx(env, ctx, got.clone(), crate::Transparency::Reducible)?;
    let expected_ref = match parse_ref_type_parts(&expected_whnf) {
        Some(value) => value,
        None => return Ok(None),
    };
    let got_ref = match parse_ref_type_parts(&got_whnf) {
        Some(value) => value,
        None => return Ok(None),
    };

    if expected_ref.kind != got_ref.kind || expected_ref.label == got_ref.label {
        return Ok(None);
    }

    if !is_def_eq_in_ctx(
        env,
        ctx,
        expected_ref.inner,
        got_ref.inner,
        crate::Transparency::Reducible,
    )? {
        return Ok(None);
    }

    Ok(Some((expected_ref.label, got_ref.label)))
}

fn collect_ref_label_stats(
    term: &Rc<Term>,
    explicit_labels: &mut HashSet<String>,
    unlabeled_count: &mut usize,
) {
    if let Some((label, inner)) = parse_ref_term(term) {
        if let Some(label) = label {
            explicit_labels.insert(label);
        } else {
            *unlabeled_count += 1;
        }
        collect_ref_label_stats(&inner, explicit_labels, unlabeled_count);
        return;
    }

    match &**term {
        Term::App(f, a, _) => {
            collect_ref_label_stats(f, explicit_labels, unlabeled_count);
            collect_ref_label_stats(a, explicit_labels, unlabeled_count);
        }
        Term::LetE(ty, val, body) => {
            collect_ref_label_stats(ty, explicit_labels, unlabeled_count);
            collect_ref_label_stats(val, explicit_labels, unlabeled_count);
            collect_ref_label_stats(body, explicit_labels, unlabeled_count);
        }
        Term::Lam(_, _, _, _) | Term::Pi(_, _, _, _) | Term::Fix(_, _) => {}
        Term::Var(_)
        | Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => {}
    }
}

fn ensure_return_refs_labeled(
    term: &Rc<Term>,
    distinct_arg_labels: usize,
) -> Result<(), TypeError> {
    if distinct_arg_labels == 1 {
        return Ok(());
    }

    if let Some((label, inner)) = parse_ref_term(term) {
        if label.is_none() {
            return Err(TypeError::AmbiguousRefLifetime);
        }
        return ensure_return_refs_labeled(&inner, distinct_arg_labels);
    }

    match &**term {
        Term::App(f, a, _) => {
            ensure_return_refs_labeled(f, distinct_arg_labels)?;
            ensure_return_refs_labeled(a, distinct_arg_labels)
        }
        Term::LetE(ty, val, body) => {
            ensure_return_refs_labeled(ty, distinct_arg_labels)?;
            ensure_return_refs_labeled(val, distinct_arg_labels)?;
            ensure_return_refs_labeled(body, distinct_arg_labels)
        }
        Term::Lam(_, _, _, _) | Term::Pi(_, _, _, _) | Term::Fix(_, _) => Ok(()),
        Term::Var(_)
        | Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => Ok(()),
    }
}

fn validate_ref_lifetime_elision_for_pi(dom: &Rc<Term>, body: &Rc<Term>) -> Result<(), TypeError> {
    let mut explicit_labels: HashSet<String> = HashSet::new();
    let mut unlabeled_count = 0usize;
    let mut current_dom = dom.clone();
    let mut current_body = body.clone();

    loop {
        collect_ref_label_stats(&current_dom, &mut explicit_labels, &mut unlabeled_count);
        if let Term::Pi(next_dom, next_body, _, _) = &*current_body {
            current_dom = next_dom.clone();
            current_body = next_body.clone();
        } else {
            break;
        }
    }

    let distinct_arg_labels = explicit_labels.len() + unlabeled_count;
    ensure_return_refs_labeled(&current_body, distinct_arg_labels)
}

fn validate_marker_definitions(
    env: &mut Env,
    markers: &[crate::ast::MarkerId],
) -> Result<(), TypeError> {
    if markers.is_empty() {
        return Ok(());
    }
    env.init_marker_registry()?;
    env.marker_registry.validate_marker_ids(markers)
}

fn marker_signature_ok(ty: &Rc<Term>) -> bool {
    match &**ty {
        Term::Sort(level) => match reduce_level(level.clone()) {
            Level::Succ(inner) => matches!(*inner, Level::Zero),
            _ => false,
        },
        _ => false,
    }
}

/// Copy(T): sorts; types, type families and proofs (erased at run time, `is_erased_type`);
/// `Ref Shared _`; an inductive type with a Copy instance (derived or explicit) whose
/// requirements hold for the arguments. Function types (other than proofs), `Ref Mut _`, affine
/// and interior-mutable inductives, opaque types and type variables are not Copy.
fn is_copy_type(env: &Env, ctx: &Context, ty: &Rc<Term>) -> Result<bool, TypeError> {
    let mut stack = Vec::new();
    is_copy_type_inner(env, ctx, ty, &mut stack)
}

pub fn is_copy_type_in_env(env: &Env, ty: &Rc<Term>) -> bool {
    is_copy_type(env, &Context::new(), ty).unwrap_or(false)
}

pub fn is_copy_type_in_ctx(env: &Env, ctx: &Context, ty: &Rc<Term>) -> Result<bool, TypeError> {
    is_copy_type(env, ctx, ty)
}

fn is_copy_type_inner(
    env: &Env,
    ctx: &Context,
    ty: &Rc<Term>,
    stack: &mut Vec<(String, Vec<Rc<Term>>)>,
) -> Result<bool, TypeError> {
    let ty_norm = whnf_in_ctx(env, ctx, ty.clone(), crate::Transparency::Reducible)?;
    match &*ty_norm {
        Term::Sort(_) => Ok(true),
        // A function type is Copy only if its values are erased (a type family or a proof).
        Term::Pi(_, _, _, _) => Ok(is_erased_type(env, ctx, &ty_norm)),
        _ => {
            let (head, args) = collect_app_spine(&ty_norm);
            if is_const_named(&head, "Ref") && args.len() == 2 {
                if is_const_named(&args[0].arg, "Shared") {
                    return Ok(true);
                }
                if is_const_named(&args[0].arg, "Mut") {
                    return Ok(false);
                }
            }
            if let Some((ind_name, args)) = get_inductive_head_args(env, &ty_norm) {
                if stack
                    .iter()
                    .any(|(name, existing_args)| *name == ind_name && *existing_args == args)
                {
                    return Ok(false);
                }
                stack.push((ind_name.clone(), args.clone()));
                let mut result = false;
                if let Some(instances) = env.copy_instances.get(&ind_name) {
                    for inst in instances {
                        // Derived instances are parameterised by the type's parameters only
                        // (indices never affect Copy-ness); explicit instances bind every
                        // argument of the type. Either way, the first `param_count` arguments
                        // instantiate the instance.
                        if inst.param_count > args.len() {
                            continue;
                        }
                        let mut all_ok = true;
                        for req in &inst.requirements {
                            let req_inst = subst_params(req, &args[..inst.param_count]);
                            if !is_copy_type_inner(env, ctx, &req_inst, stack)? {
                                all_ok = false;
                                break;
                            }
                        }
                        if all_ok {
                            result = true;
                            break;
                        }
                    }
                }
                stack.pop();
                // Proofs are erased at run time and therefore duplicable.
                Ok(result || is_erased_type(env, ctx, &ty_norm))
            } else {
                Ok(is_erased_type(env, ctx, &ty_norm))
            }
        }
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

fn usage_mode_for_kind(kind: FunctionKind) -> UsageMode {
    match kind {
        FunctionKind::Fn => UsageMode::Observational,
        FunctionKind::FnMut => UsageMode::MutBorrow,
        FunctionKind::FnOnce => UsageMode::Consuming,
    }
}

// =============================================================================================
// Ownership: erased positions, the ownership walk, and the uses analysis behind function kinds.
//
// The rules implemented here are written out in docs/spec/ownership_model.md (section 6.2).
// =============================================================================================

/// Whether `ty` is an arity: a sort, or a Pi type whose codomain is (after whnf) an arity.
fn is_arity(env: &Env, ctx: &Context, ty: &Rc<Term>) -> bool {
    let mut current_ctx = ctx.clone();
    let mut current = ty.clone();
    loop {
        let Ok(norm) = whnf_in_ctx(env, &current_ctx, current.clone(), Transparency::Reducible)
        else {
            return false;
        };
        match &*norm {
            Term::Sort(_) => return true,
            Term::Pi(dom, body, _, _) => {
                current_ctx = current_ctx.push(dom.clone());
                current = body.clone();
            }
            _ => return false,
        }
    }
}

/// Whether the values of type `ty` are erased at run time: types (`ty` is a sort), type
/// families (`ty` is an arity `Pi ... -> Sort`) and proofs (`ty` is a proposition). Erased values
/// are Copy, and occurrences of variables inside erased terms have no ownership effect. A type
/// the kernel cannot classify (e.g. an open term outside its context) counts as not erased.
pub fn is_erased_type(env: &Env, ctx: &Context, ty: &Rc<Term>) -> bool {
    if is_arity(env, ctx, ty) {
        return true;
    }
    is_prop_like(env, ctx, ty).unwrap_or(false)
}

/// Borrow primitives: the argument of `borrow_shared` is read, the argument of `borrow_mut` is
/// used mutably; neither is moved (K3: borrowing is not moving).
fn borrow_primitive_use(head: &Rc<Term>) -> Option<UsageMode> {
    match &**head {
        Term::Const(name, _) if name == "borrow_shared" => Some(UsageMode::Observational),
        Term::Const(name, _) if name == "borrow_mut" => Some(UsageMode::MutBorrow),
        _ => None,
    }
}

/// Erasure information along an application spine `head a1 ... an`.
struct SpineInfo {
    /// Whether argument `i` is in an erased position (the domain it is checked against is
    /// erased, see [`is_erased_type`]).
    arg_erased: Vec<bool>,
    /// Kind of the Pi type consumed by argument `i`: how the function value is called.
    arg_kind: Vec<FunctionKind>,
    /// Whether the whole application is erased (it is a type, a type family or a proof).
    result_erased: bool,
}

fn spine_info(
    env: &Env,
    ctx: &Context,
    head: &Rc<Term>,
    args: &[Rc<Term>],
) -> Result<SpineInfo, TypeError> {
    let mut ty = infer(env, ctx, head.clone())?;
    let mut arg_erased = Vec::with_capacity(args.len());
    let mut arg_kind = Vec::with_capacity(args.len());
    for arg in args {
        let norm = whnf_in_ctx(env, ctx, ty, Transparency::Reducible)?;
        match &*norm {
            Term::Pi(dom, body, _, kind) => {
                arg_erased.push(is_erased_type(env, ctx, dom));
                arg_kind.push(*kind);
                ty = body.subst(0, arg);
            }
            _ => return Err(TypeError::ExpectedFunction(norm)),
        }
    }
    Ok(SpineInfo {
        arg_erased,
        arg_kind,
        result_erased: is_erased_type(env, ctx, &ty),
    })
}

/// Role of an argument of a recursor application `Rec_I params motive minors indices major`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RecArgRole {
    Param,
    Motive,
    Minor(usize),
    Index,
    Major,
    /// An argument beyond the major premise (applied to the result of the elimination).
    Extra,
}

fn rec_arg_role(decl: &InductiveDecl, num_indices: usize, pos: usize) -> RecArgRole {
    let num_params = decl.num_params;
    let num_ctors = decl.ctors.len();
    if pos < num_params {
        RecArgRole::Param
    } else if pos == num_params {
        RecArgRole::Motive
    } else if pos < num_params + 1 + num_ctors {
        RecArgRole::Minor(pos - num_params - 1)
    } else if pos < num_params + 1 + num_ctors + num_indices {
        RecArgRole::Index
    } else if pos == num_params + 1 + num_ctors + num_indices {
        RecArgRole::Major
    } else {
        RecArgRole::Extra
    }
}

/// Erased positions of a recursor application: parameters, motive and indices always; minors,
/// major and extra arguments when their domain is erased (elimination into `Prop` or into a sort,
/// or a major premise that is a proof).
fn rec_erased_positions(decl: &InductiveDecl, num_indices: usize, info: &SpineInfo) -> Vec<bool> {
    (0..info.arg_erased.len())
        .map(|pos| {
            matches!(
                rec_arg_role(decl, num_indices, pos),
                RecArgRole::Param | RecArgRole::Motive | RecArgRole::Index
            ) || info.arg_erased[pos]
        })
        .collect()
}

fn check_ownership_in_term(
    env: &Env,
    ctx: &Context,
    term: &Rc<Term>,
    usage: &mut UsageContext,
    mode: UsageMode,
) -> Result<(), TypeError> {
    if mode == UsageMode::Observational {
        // An erased position: no ownership effect.
        return Ok(());
    }
    check_ownership_in_term_with_capture(env, ctx, term, usage, &[])
}

fn term_key(term: &Rc<Term>) -> usize {
    Rc::as_ptr(term) as usize
}

/// The ownership walk of a term in a *runtime* position (erased subterms are never visited).
///
/// `usage` holds the moved state of every variable in scope; `captures` records, for each
/// enclosing lambda inside the walked term, how that closure captures the variables bound
/// outside it (see [`use_var_at_runtime`]).
fn check_ownership_in_term_with_capture(
    env: &Env,
    ctx: &Context,
    term: &Rc<Term>,
    usage: &mut UsageContext,
    captures: &[CaptureContext],
) -> Result<(), TypeError> {
    match &**term {
        // A variable in a runtime position is moved (a no-op for Copy variables).
        Term::Var(idx) => use_var_at_runtime(usage, *idx, UsageMode::Consuming, captures),
        Term::App(_, _, _) => {
            let (head, spine) = collect_app_spine(term);
            let args: Vec<Rc<Term>> = spine.into_iter().map(|item| item.arg).collect();
            if let Term::Rec(ind_name, _) = &*head {
                if let Some(decl) = env.get_inductive(ind_name) {
                    return check_ownership_rec_app(env, ctx, &head, decl, &args, usage, captures);
                }
            }
            if let Some(borrow_mode) = borrow_primitive_use(&head) {
                if args.len() >= 2 {
                    // `borrow_* {A} x`: A is a type; x is read / used mutably, not moved. A
                    // compound argument is a temporary: it is evaluated (consumed) and borrowed.
                    match &*args[1] {
                        Term::Var(idx) => use_var_at_runtime(usage, *idx, borrow_mode, captures)?,
                        _ => check_ownership_in_term_with_capture(
                            env, ctx, &args[1], usage, captures,
                        )?,
                    }
                    for arg in &args[2..] {
                        check_ownership_in_term_with_capture(env, ctx, arg, usage, captures)?;
                    }
                    return Ok(());
                }
            }
            let info = spine_info(env, ctx, &head, &args)?;
            if info.result_erased {
                // The application is a type, a type family or a proof.
                return Ok(());
            }
            match &*head {
                // Calling a function variable: a read (Fn), a mutable use (FnMut) or a move
                // (FnOnce) of the variable; each requires that it has not been moved.
                Term::Var(f_idx) => use_var_at_runtime(
                    usage,
                    *f_idx,
                    usage_mode_for_kind(info.arg_kind[0]),
                    captures,
                )?,
                // A compound head is evaluated to a function value and consumed by the call.
                _ => check_ownership_in_term_with_capture(env, ctx, &head, usage, captures)?,
            }
            for (arg, erased) in args.iter().zip(&info.arg_erased) {
                if !*erased {
                    check_ownership_in_term_with_capture(env, ctx, arg, usage, captures)?;
                }
            }
            Ok(())
        }
        Term::Lam(ty, body, info, kind) => {
            // The binder type is erased. Inside the body, an outer variable is used at most as
            // strongly as the closure's kind allows (see `use_var_at_runtime`).
            let is_copy = is_copy_type(env, ctx, ty)?;
            usage.push_binder(is_copy, *info, Some(term_key(term)));
            let new_ctx = ctx.push(ty.clone());
            let mut body_captures = bump_captures(captures);
            body_captures.push(CaptureContext {
                mode: usage_mode_for_kind(*kind),
                depth: 1,
            });
            let res =
                check_ownership_in_term_with_capture(env, &new_ctx, body, usage, &body_captures);
            usage.pop();
            res
        }
        // A Pi type is erased.
        Term::Pi(_, _, _, _) => Ok(()),
        Term::LetE(ty, val, body) => {
            // The value is evaluated unless it is erased (a type, type family or proof).
            if !is_erased_type(env, ctx, ty) {
                check_ownership_in_term_with_capture(env, ctx, val, usage, captures)?;
            }
            let is_copy = is_copy_type(env, ctx, ty)?;
            usage.push_binder(is_copy, BinderInfo::Default, Some(term_key(term)));
            let new_ctx = ctx.push(ty.clone());
            let body_captures = bump_captures(captures);
            let res =
                check_ownership_in_term_with_capture(env, &new_ctx, body, usage, &body_captures);
            usage.pop();
            res
        }
        Term::Fix(ty, body) => {
            let is_copy = is_copy_type(env, ctx, ty)?;
            // The fixpoint body runs once per recursive call: outer non-Copy variables may not
            // be consumed in it.
            usage.push_barrier();
            usage.push_binder(is_copy, BinderInfo::Default, Some(term_key(term)));
            let new_ctx = ctx.push(ty.clone());
            let body_captures = bump_captures(captures);
            let res =
                check_ownership_in_term_with_capture(env, &new_ctx, body, usage, &body_captures);
            usage.pop();
            usage.pop_barrier();
            res
        }
        Term::Rec(ind_name, _) => {
            // A recursor value outside an application spine that supplies its minor premises.
            Err(TypeError::OwnershipError(
                OwnershipError::RecursorWithoutMinorPremises {
                    ind: ind_name.clone(),
                },
            ))
        }
        Term::Const(_, _)
        | Term::Sort(_)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Meta(_) => Ok(()),
    }
}

/// Runtime occurrence of variable `idx` in `mode` (a move, a mutable use, or — for
/// `Observational` — a read), seen through the closures in `captures`: an occurrence inside a
/// closure counts for the variable as the weaker of `mode` and the capture modes of the closures it
/// is captured by (an `Fn` closure only reads its captures, an `FnMut` closure uses them mutably).
fn use_var_at_runtime(
    usage: &mut UsageContext,
    idx: usize,
    mode: UsageMode,
    captures: &[CaptureContext],
) -> Result<(), TypeError> {
    let effective_mode = effective_capture_mode(idx, mode, captures);
    match effective_mode {
        UsageMode::Observational => usage.read_var(idx).map_err(TypeError::from),
        _ => usage.use_var(idx, effective_mode).map_err(TypeError::from),
    }
}

/// `mode` downgraded by the capture modes of the enclosing closures that capture variable `idx`.
fn effective_capture_mode(idx: usize, mode: UsageMode, captures: &[CaptureContext]) -> UsageMode {
    let mut effective_mode = mode;
    for capture in captures {
        if idx >= capture.depth {
            effective_mode = usage_mode_min(effective_mode, capture.mode);
        }
    }
    effective_mode
}

/// For each constructor field (binders after the parameters), whether it is a recursive field,
/// with the same criterion as the recursor's minor-premise type (`compute_minor_premise_type`).
fn ctor_recursive_fields(ctor_ty: &Rc<Term>, ind_name: &str, num_params: usize) -> Vec<bool> {
    let (binders, _) = peel_pi_binders(ctor_ty);
    binders
        .iter()
        .skip(num_params)
        .map(|(dom, _)| extract_inductive_indices(dom, ind_name, num_params).is_some())
        .collect()
}

/// Ownership walk of a recursor application `Rec_I params motive minors indices major extra...`.
///
/// * The application must supply the motive and every minor premise (a recursor value that
///   receives its minor premises later, through a variable, is rejected).
/// * Parameters, motive and indices are erased; so are minor premises, major premise and extra
///   arguments whose domain is erased, and the whole application if its type is erased (an
///   elimination into `Prop` or into a sort).
/// * `I` non-recursive (no constructor has a recursive field) and the application saturated
///   (the major premise is supplied): exactly one minor premise runs, after the major premise has
///   been evaluated (this is also the order of MIR's inline lowering). The major premise is walked
///   first; then every minor premise is walked from the same state (they are alternatives) and
///   the resulting moved sets are joined.
/// * Otherwise (`I` recursive, or the application unsaturated): the arguments are walked in order
///   (the minor premises are built as values before any dispatch: MIR builds them as closures
///   before it evaluates the major premise, and an unsaturated application is a function that
///   holds them). A minor premise is *repeatable* if the application is unsaturated (the result
///   is a function that may be called many times), if `I` is branching (some constructor has two
///   or more recursive fields), or if its constructor has a recursive field; for an unsaturated
///   application every minor premise is repeatable, also for a non-recursive `I`, so two minor
///   premises may not consume the same captured value. A repeatable minor premise of a
///   constructor with fields must be a lambda abstraction (or a global constant), and its body
///   may not consume non-Copy variables bound outside it; a repeatable minor premise of a
///   field-less constructor is returned for every occurrence of the constructor and must be Copy.
/// * In every minor premise, a recursive field of non-Copy type starts out moved: the recursor
///   evaluates the induction hypotheses eagerly, consuming the field, before running the minor
///   premise (only the induction hypothesis may be used). A minor premise must bind such fields as
///   lambda parameters.
fn check_ownership_rec_app(
    env: &Env,
    ctx: &Context,
    head: &Rc<Term>,
    decl: &InductiveDecl,
    args: &[Rc<Term>],
    usage: &mut UsageContext,
    captures: &[CaptureContext],
) -> Result<(), TypeError> {
    let ind_name = decl.name.as_str();
    let num_params = decl.num_params;
    let num_ctors = decl.ctors.len();
    let num_indices = count_pi_binders(&decl.ty).saturating_sub(num_params);
    let expected_args = num_params + 1 + num_ctors + num_indices + 1;
    let saturated = args.len() >= expected_args;
    if args.len() < num_params + 1 + num_ctors {
        // Minor premises supplied later (through a variable bound to this partial application)
        // could not be checked against how often the recursor runs them.
        return Err(TypeError::OwnershipError(
            OwnershipError::RecursorWithoutMinorPremises {
                ind: ind_name.to_string(),
            },
        ));
    }

    let info = spine_info(env, ctx, head, args)?;
    if info.result_erased {
        return Ok(());
    }
    let erased = rec_erased_positions(decl, num_indices, &info);

    let recursive_fields: Vec<Vec<bool>> = decl
        .ctors
        .iter()
        .map(|ctor| ctor_recursive_fields(&ctor.ty, ind_name, num_params))
        .collect();
    let recursive_counts: Vec<usize> = recursive_fields
        .iter()
        .map(|fields| fields.iter().filter(|is_rec| **is_rec).count())
        .collect();
    let is_recursive = recursive_counts.iter().any(|count| *count > 0);
    let is_branching = recursive_counts.iter().any(|count| *count >= 2);

    // Whether a value of `I params ...` (hence a recursive field) is Copy. Copy-ness does not
    // depend on indices (see `derive_copy_instance`).
    let recursive_field_copy = if is_recursive && args.len() >= num_params {
        let levels = match &**head {
            Term::Rec(_, levels) => levels.clone(),
            _ => Vec::new(),
        };
        let ind_levels: Vec<Level> = levels
            .iter()
            .take(decl.univ_params.len())
            .cloned()
            .collect();
        let mut ind_ty = Rc::new(Term::Ind(ind_name.to_string(), ind_levels));
        for param in &args[..num_params] {
            ind_ty = Term::app(ind_ty, param.clone());
        }
        is_copy_type(env, ctx, &ind_ty)?
    } else {
        true
    };

    let walk_minor =
        |pos: usize, ctor_idx: usize, usage: &mut UsageContext| -> Result<(), TypeError> {
            let repeatable =
                !saturated || (is_recursive && (is_branching || recursive_counts[ctor_idx] > 0));
            check_ownership_minor_premise(
                env,
                ctx,
                &args[pos],
                &decl.ctors[ctor_idx].name,
                &recursive_fields[ctor_idx],
                repeatable,
                recursive_field_copy,
                usage,
                captures,
            )
        };

    if !is_recursive && saturated {
        // Major premise first, then the minor premises as alternatives. An unsaturated
        // application builds every minor premise before any dispatch, so it takes the sequential
        // walk below (with every minor premise repeatable).
        let major_pos = num_params + 1 + num_ctors + num_indices;
        if major_pos < args.len() && !erased[major_pos] {
            check_ownership_in_term_with_capture(env, ctx, &args[major_pos], usage, captures)?;
        }
        let before = usage.moved_state();
        let mut joined = before.clone();
        for ctor_idx in 0..num_ctors {
            let pos = num_params + 1 + ctor_idx;
            if erased[pos] {
                continue;
            }
            usage.restore_moved_state(&before);
            walk_minor(pos, ctor_idx, usage)?;
            UsageContext::join_moved_states(&mut joined, &usage.moved_state());
        }
        usage.restore_moved_state(&joined);
        for pos in (major_pos + 1)..args.len() {
            if !erased[pos] {
                check_ownership_in_term_with_capture(env, ctx, &args[pos], usage, captures)?;
            }
        }
        return Ok(());
    }

    for (pos, arg) in args.iter().enumerate() {
        if erased[pos] {
            continue;
        }
        match rec_arg_role(decl, num_indices, pos) {
            RecArgRole::Minor(ctor_idx) => walk_minor(pos, ctor_idx, usage)?,
            _ => check_ownership_in_term_with_capture(env, ctx, arg, usage, captures)?,
        }
    }
    Ok(())
}

/// Ownership walk of one minor premise (see `check_ownership_rec_app`).
#[allow(clippy::too_many_arguments)]
fn check_ownership_minor_premise(
    env: &Env,
    ctx: &Context,
    minor: &Rc<Term>,
    ctor_name: &str,
    recursive_fields: &[bool],
    repeatable: bool,
    recursive_field_copy: bool,
    usage: &mut UsageContext,
    captures: &[CaptureContext],
) -> Result<(), TypeError> {
    // Binders of the minor premise: each field, followed by its induction hypothesis when the
    // field is recursive (`compute_minor_premise_type`). `Some(true)` marks a recursive field.
    let mut roles: Vec<Option<bool>> = Vec::new();
    for is_rec in recursive_fields {
        roles.push(Some(*is_rec));
        if *is_rec {
            roles.push(None);
        }
    }

    if roles.is_empty() {
        // Field-less constructor: the minor premise is the value the recursor returns for it.
        if repeatable {
            let minor_ty = infer(env, ctx, minor.clone())?;
            if !is_copy_type(env, ctx, &minor_ty)? {
                return Err(TypeError::OwnershipError(
                    OwnershipError::RepeatedMinorValueNotCopy {
                        ctor: ctor_name.to_string(),
                    },
                ));
            }
        }
        return check_ownership_in_term_with_capture(env, ctx, minor, usage, captures);
    }

    if repeatable {
        usage.push_barrier();
    }
    let mut pushed = 0usize;
    let mut current = minor.clone();
    let mut current_ctx = ctx.clone();
    let mut current_captures = captures.to_vec();
    let mut role_idx = 0usize;
    let result = loop {
        if role_idx == roles.len() {
            break check_ownership_in_term_with_capture(
                env,
                &current_ctx,
                &current,
                usage,
                &current_captures,
            );
        }
        match &*current {
            Term::Lam(ty, body, info, kind) => {
                // The binder type is erased.
                let is_copy = match is_copy_type(env, &current_ctx, ty) {
                    Ok(is_copy) => is_copy,
                    Err(err) => break Err(err),
                };
                if roles[role_idx] == Some(true) {
                    usage.push_recursive_field(is_copy, *info, Some(term_key(&current)));
                } else {
                    usage.push_binder(is_copy, *info, Some(term_key(&current)));
                }
                pushed += 1;
                current_ctx = current_ctx.push(ty.clone());
                current_captures = bump_captures(&current_captures);
                current_captures.push(CaptureContext {
                    mode: usage_mode_for_kind(*kind),
                    depth: 1,
                });
                let next = body.clone();
                current = next;
                role_idx += 1;
            }
            _ => {
                let unbound_recursive_field =
                    roles[role_idx..].iter().any(|role| *role == Some(true));
                if unbound_recursive_field && !recursive_field_copy {
                    break Err(TypeError::OwnershipError(
                        OwnershipError::MinorMustBindRecursiveField {
                            ctor: ctor_name.to_string(),
                        },
                    ));
                }
                if repeatable
                    && pushed == 0
                    && !matches!(&*current, Term::Const(_, _) | Term::Ctor(_, _, _))
                {
                    break Err(TypeError::OwnershipError(
                        OwnershipError::RepeatedMinorNotLambda {
                            ctor: ctor_name.to_string(),
                        },
                    ));
                }
                break check_ownership_in_term_with_capture(
                    env,
                    &current_ctx,
                    &current,
                    usage,
                    &current_captures,
                );
            }
        }
    };
    for _ in 0..pushed {
        usage.pop();
    }
    if repeatable {
        usage.pop_barrier();
    }
    result
}

// ---------------------------------------------------------------------------------------------
// Uses analysis: how a term uses the variables free in it (stateless; same positions as the walk)
// ---------------------------------------------------------------------------------------------

/// How `body` uses each variable free in it: for a variable with de Bruijn index `i` in `ctx`
/// (the context of `body`), the strongest use of it in `body` — `Consuming` (moved),
/// `MutBorrow` (used mutably) or `Observational` (read, or only occurring in erased positions).
/// Variables that do not occur are absent.
///
/// The positions are those of the ownership walk: erased positions count as `Observational`;
/// a variable in a runtime position is `Consuming`; the head of a call is used according to the
/// kind of the called function (Fn: read, FnMut: mutable use, FnOnce: move); the argument of
/// `borrow_shared` / `borrow_mut` is read / used mutably; inside a nested lambda of kind `k`, a
/// use counts as the weaker of the use and `k`'s capture mode (Fn: read, FnMut: mutable use,
/// FnOnce: move).
///
/// This one analysis computes the function kind a lambda requires (kernel, [`TypeError::FunctionKindTooSmall`]),
/// the elaborator's capture analysis and MIR's required capture modes.
pub fn term_variable_uses(
    env: &Env,
    ctx: &Context,
    body: &Rc<Term>,
) -> Result<HashMap<usize, UsageMode>, TypeError> {
    let mut uses = VariableUses::default();
    collect_term_uses(env, ctx, body, 0, &[], &mut uses)?;
    Ok(uses.modes)
}

/// The variables free in `term` that occur in at least one runtime (non-erased) position, by de
/// Bruijn index in `ctx`. A free variable outside this set occurs only in erased positions
/// (types, proofs, motives, indices, parameters): its value is not needed at run time.
pub fn term_runtime_variables(
    env: &Env,
    ctx: &Context,
    term: &Rc<Term>,
) -> Result<HashSet<usize>, TypeError> {
    let mut uses = VariableUses::default();
    collect_term_uses(env, ctx, term, 0, &[], &mut uses)?;
    Ok(uses.runtime)
}

#[derive(Default)]
struct VariableUses {
    /// Strongest use of each free variable.
    modes: HashMap<usize, UsageMode>,
    /// Free variables with a runtime occurrence.
    runtime: HashSet<usize>,
}

/// The capture modes of the closure `λx. body` from the uses of the variables free in `body`
/// (`ctx` is the context of `body`, so index 0 is `x`, which is not a capture): a captured
/// variable of Copy type is always read (`Observational`: the closure works on its own copy);
/// otherwise it is moved into the closure (`Consuming`) if the body consumes it, mutably borrowed
/// (`MutBorrow`) if the body uses it mutably or consumes a `Ref Mut` value, and read
/// (`Observational`) otherwise. Keys are indices outside the lambda (body index minus 1).
pub fn capture_modes_from_uses(
    env: &Env,
    ctx: &Context,
    uses: &HashMap<usize, UsageMode>,
) -> Result<CaptureModes, TypeError> {
    let mut modes = CaptureModes::new();
    for (idx, mode) in uses {
        if *idx == 0 {
            continue;
        }
        let mut capture_mode = *mode;
        if capture_mode != UsageMode::Observational {
            if let Some(ty) = ctx.get(*idx) {
                let shifted_ty = ty.shift(0, idx + 1);
                if capture_mode == UsageMode::Consuming && is_mut_ref_type(env, ctx, &shifted_ty)? {
                    // Consuming a captured `Ref Mut` reborrows it.
                    capture_mode = UsageMode::MutBorrow;
                } else if is_copy_type(env, ctx, &shifted_ty)? {
                    // The closure holds its own copy: moving or mutably borrowing it does not
                    // affect the captured variable.
                    capture_mode = UsageMode::Observational;
                }
            }
        }
        modes.insert(idx - 1, capture_mode);
    }
    Ok(modes)
}

/// The function kind a closure with these capture modes requires: `FnOnce` if it moves a
/// capture, else `FnMut` if it uses one mutably, else `Fn`.
pub fn required_kind_from_capture_modes(modes: &CaptureModes) -> FunctionKind {
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

fn record_use(
    uses: &mut VariableUses,
    idx: usize,
    depth: usize,
    mode: UsageMode,
    captures: &[CaptureContext],
) {
    if idx < depth {
        return;
    }
    let effective = effective_capture_mode(idx, mode, captures);
    uses.runtime.insert(idx - depth);
    uses.modes
        .entry(idx - depth)
        .and_modify(|existing| {
            if usage_mode_rank(effective) > usage_mode_rank(*existing) {
                *existing = effective;
            }
        })
        .or_insert(effective);
}

/// Records the variables free in an erased subterm as `Observational` uses.
fn record_erased_uses(term: &Rc<Term>, depth: usize, uses: &mut VariableUses) {
    let mut free = HashSet::new();
    collect_free_vars(term, depth, &mut free);
    for idx in free {
        uses.modes.entry(idx).or_insert(UsageMode::Observational);
    }
}

fn collect_term_uses(
    env: &Env,
    ctx: &Context,
    term: &Rc<Term>,
    depth: usize,
    captures: &[CaptureContext],
    uses: &mut VariableUses,
) -> Result<(), TypeError> {
    match &**term {
        Term::Var(idx) => {
            record_use(uses, *idx, depth, UsageMode::Consuming, captures);
            Ok(())
        }
        Term::App(_, _, _) => {
            let (head, spine) = collect_app_spine(term);
            let args: Vec<Rc<Term>> = spine.into_iter().map(|item| item.arg).collect();
            if let Term::Rec(ind_name, _) = &*head {
                if let Some(decl) = env.get_inductive(ind_name) {
                    let num_indices = count_pi_binders(&decl.ty).saturating_sub(decl.num_params);
                    let info = spine_info(env, ctx, &head, &args)?;
                    if info.result_erased {
                        record_erased_uses(term, depth, uses);
                        return Ok(());
                    }
                    let erased = rec_erased_positions(decl, num_indices, &info);
                    for (arg, is_erased) in args.iter().zip(erased) {
                        if is_erased {
                            record_erased_uses(arg, depth, uses);
                        } else {
                            collect_term_uses(env, ctx, arg, depth, captures, uses)?;
                        }
                    }
                    return Ok(());
                }
            }
            if let Some(borrow_mode) = borrow_primitive_use(&head) {
                if args.len() >= 2 {
                    record_erased_uses(&args[0], depth, uses);
                    match &*args[1] {
                        Term::Var(idx) => record_use(uses, *idx, depth, borrow_mode, captures),
                        _ => collect_term_uses(env, ctx, &args[1], depth, captures, uses)?,
                    }
                    for arg in &args[2..] {
                        collect_term_uses(env, ctx, arg, depth, captures, uses)?;
                    }
                    return Ok(());
                }
            }
            let info = spine_info(env, ctx, &head, &args)?;
            if info.result_erased {
                record_erased_uses(term, depth, uses);
                return Ok(());
            }
            match &*head {
                Term::Var(f_idx) => record_use(
                    uses,
                    *f_idx,
                    depth,
                    usage_mode_for_kind(info.arg_kind[0]),
                    captures,
                ),
                _ => collect_term_uses(env, ctx, &head, depth, captures, uses)?,
            }
            for (arg, erased) in args.iter().zip(&info.arg_erased) {
                if *erased {
                    record_erased_uses(arg, depth, uses);
                } else {
                    collect_term_uses(env, ctx, arg, depth, captures, uses)?;
                }
            }
            Ok(())
        }
        Term::Lam(ty, body, _, kind) => {
            record_erased_uses(ty, depth, uses);
            let new_ctx = ctx.push(ty.clone());
            let mut body_captures = bump_captures(captures);
            body_captures.push(CaptureContext {
                mode: usage_mode_for_kind(*kind),
                depth: 1,
            });
            collect_term_uses(env, &new_ctx, body, depth + 1, &body_captures, uses)
        }
        Term::Pi(_, _, _, _) => {
            record_erased_uses(term, depth, uses);
            Ok(())
        }
        Term::LetE(ty, val, body) => {
            record_erased_uses(ty, depth, uses);
            if is_erased_type(env, ctx, ty) {
                record_erased_uses(val, depth, uses);
            } else {
                collect_term_uses(env, ctx, val, depth, captures, uses)?;
            }
            let new_ctx = ctx.push(ty.clone());
            let body_captures = bump_captures(captures);
            collect_term_uses(env, &new_ctx, body, depth + 1, &body_captures, uses)
        }
        Term::Fix(ty, body) => {
            record_erased_uses(ty, depth, uses);
            let new_ctx = ctx.push(ty.clone());
            let body_captures = bump_captures(captures);
            collect_term_uses(env, &new_ctx, body, depth + 1, &body_captures, uses)
        }
        Term::Const(_, _)
        | Term::Sort(_)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => Ok(()),
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

fn validate_capture_modes(
    def_name: &str,
    term: &Rc<Term>,
    capture_modes: &DefCaptureModeMap,
) -> Result<(), TypeError> {
    if capture_modes.is_empty() {
        return Ok(());
    }

    let mut seen = HashSet::new();
    let mut counter: u64 = 0;

    fn walk(
        term: &Rc<Term>,
        def_name: &str,
        counter: &mut u64,
        capture_modes: &DefCaptureModeMap,
        seen: &mut HashSet<DefId>,
    ) -> Result<(), TypeError> {
        match &**term {
            Term::Lam(ty, body, _, _) => {
                let closure_id = DefId::new(format!("{}::closure#{}", def_name, *counter));
                *counter += 1;
                seen.insert(closure_id);
                if let Some(modes) = capture_modes.get(&closure_id) {
                    let mut free_vars = HashSet::new();
                    collect_free_vars(body, 1, &mut free_vars);
                    for idx in modes.keys() {
                        if !free_vars.contains(idx) {
                            return Err(TypeError::InvalidCaptureAnnotation {
                                def_name: def_name.to_string(),
                                closure_id: closure_id.0,
                                index: *idx,
                            });
                        }
                    }
                }
                walk(ty, def_name, counter, capture_modes, seen)?;
                walk(body, def_name, counter, capture_modes, seen)
            }
            Term::Fix(ty, body) => {
                let closure_id = DefId::new(format!("{}::closure#{}", def_name, *counter));
                *counter += 1;
                seen.insert(closure_id);
                if let Some(modes) = capture_modes.get(&closure_id) {
                    let mut free_vars = HashSet::new();
                    collect_free_vars(body, 1, &mut free_vars);
                    for idx in modes.keys() {
                        if !free_vars.contains(idx) {
                            return Err(TypeError::InvalidCaptureAnnotation {
                                def_name: def_name.to_string(),
                                closure_id: closure_id.0,
                                index: *idx,
                            });
                        }
                    }
                }
                walk(ty, def_name, counter, capture_modes, seen)?;
                walk(body, def_name, counter, capture_modes, seen)
            }
            Term::App(f, a, _) => {
                walk(f, def_name, counter, capture_modes, seen)?;
                walk(a, def_name, counter, capture_modes, seen)
            }
            Term::Pi(ty, body, _, _) => {
                walk(ty, def_name, counter, capture_modes, seen)?;
                walk(body, def_name, counter, capture_modes, seen)
            }
            Term::LetE(ty, val, body) => {
                walk(ty, def_name, counter, capture_modes, seen)?;
                walk(val, def_name, counter, capture_modes, seen)?;
                walk(body, def_name, counter, capture_modes, seen)
            }
            Term::Sort(_)
            | Term::Const(_, _)
            | Term::Ind(_, _)
            | Term::Ctor(_, _, _)
            | Term::Rec(_, _)
            | Term::Var(_)
            | Term::Meta(_) => Ok(()),
        }
    }

    walk(term, def_name, &mut counter, capture_modes, &mut seen)?;

    for closure_id in capture_modes.keys() {
        if !seen.contains(closure_id) {
            return Err(TypeError::UnknownCaptureAnnotation {
                def_name: def_name.to_string(),
                closure_id: closure_id.0,
            });
        }
    }

    Ok(())
}

fn is_mut_ref_type(env: &Env, ctx: &Context, ty: &Rc<Term>) -> Result<bool, TypeError> {
    let ty_whnf = whnf_in_ctx(env, ctx, ty.clone(), crate::Transparency::Reducible)?;
    let (head, args) = collect_app_spine(&ty_whnf);
    match &*head {
        Term::Const(name, _) if name == "Ref" && args.len() == 2 => Ok(matches!(
            &*args[0].arg,
            Term::Const(k, _) if k == "Mut"
        )),
        _ => Ok(false),
    }
}

fn result_sort_with_transparency(
    env: &Env,
    ctx: &Context,
    term: &Rc<Term>,
    transparency: Transparency,
) -> Result<Option<Level>, TypeError> {
    let mut current = term.clone();
    let mut local_ctx = ctx.clone();
    loop {
        let norm = whnf_in_ctx(env, &local_ctx, current, transparency)?;
        match &*norm {
            Term::Pi(ty, body, _, _) => {
                local_ctx = local_ctx.push(ty.clone());
                current = body.clone();
            }
            Term::Sort(level) => return Ok(Some(level.clone())),
            _ => return Ok(None),
        }
    }
}

/// Transparency policy for Prop classification checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PropTransparencyContext {
    /// Default: respect `opaque` aliases during Prop classification.
    #[default]
    Opaque,
    /// Explicitly unfold `opaque` aliases during Prop classification.
    UnfoldOpaque,
}

impl PropTransparencyContext {
    fn transparency(self) -> Transparency {
        match self {
            PropTransparencyContext::Opaque => Transparency::Reducible,
            PropTransparencyContext::UnfoldOpaque => Transparency::All,
        }
    }
}

pub fn is_prop_like(env: &Env, ctx: &Context, term: &Rc<Term>) -> Result<bool, TypeError> {
    is_prop_like_with_transparency(env, ctx, term, PropTransparencyContext::default())
}

pub fn is_prop_like_with_transparency(
    env: &Env,
    ctx: &Context,
    term: &Rc<Term>,
    prop_ctx: PropTransparencyContext,
) -> Result<bool, TypeError> {
    let transparency = prop_ctx.transparency();
    let term_norm = whnf_in_ctx(env, ctx, term.clone(), transparency)?;
    if let Term::Sort(level) = &*term_norm {
        return Ok(level_is_zero(level));
    }

    let sort_ty = infer(env, ctx, term.clone())?;
    let sort_norm = whnf_in_ctx(env, ctx, sort_ty, transparency)?;
    Ok(extract_level(&sort_norm)
        .as_ref()
        .map_or(false, level_is_zero))
}

/// Whether `ty` (a type in `ctx`) is a proposition, i.e. its own type is the sort `Prop`,
/// so that its inhabitants are proofs.
///
/// Unlike [`is_prop_like_with_transparency`], this does NOT hold for the sort `Prop` itself:
/// a binder of type `Prop` holds a proposition (data), not a proof.
fn is_proposition_with_transparency(
    env: &Env,
    ctx: &Context,
    ty: &Rc<Term>,
    prop_ctx: PropTransparencyContext,
) -> Result<bool, TypeError> {
    let sort_ty = infer(env, ctx, ty.clone())?;
    let sort_norm = whnf_in_ctx(env, ctx, sort_ty, prop_ctx.transparency())?;
    Ok(extract_level(&sort_norm)
        .as_ref()
        .map_or(false, level_is_zero))
}

/// Enforce the Prop -> Type elimination restriction for inductives in Prop.
///
/// The restriction applies to every inductive that MAY be a proposition: its arity ends in a
/// sort whose level is not provably nonzero for every assignment of the level parameters
/// (`Prop`, `Sort u`, `Sort (imax 1 u)`; not `Sort (u + 1)` or `Sort (max 1 u)`), as in Lean 4.
///
/// Elimination into Prop is always allowed. Elimination of an inductive proposition into any
/// other sort ("large elimination") is allowed only if
/// * it has no constructor, or
/// * it has exactly one constructor all of whose fields (the constructor's binders after the
///   uniform parameters) are proofs, i.e. their types are propositions, or
/// * it has the shape of equality (controlled exception: transport).
///
/// A field whose type is the sort `Prop` itself holds a proposition, not a proof; allowing
/// large elimination for it would make `Prop` a definitional retract of a proposition, which is
/// inconsistent with an impredicative `Prop` (Hurkens' paradox). Parameters are not fields and
/// are not restricted.
pub fn check_elimination_restriction(
    env: &Env,
    ind_name: &str,
    levels: &[Level],
) -> Result<(), TypeError> {
    check_elimination_restriction_with_transparency(
        env,
        ind_name,
        levels,
        PropTransparencyContext::UnfoldOpaque,
    )
}

pub fn check_elimination_restriction_with_transparency(
    env: &Env,
    ind_name: &str,
    levels: &[Level],
    prop_ctx: PropTransparencyContext,
) -> Result<(), TypeError> {
    let decl = env
        .get_inductive(ind_name)
        .ok_or_else(|| TypeError::UnknownInductive(ind_name.to_string()))?;

    // 1. Determine target level (convention: universe levels are [params..., result])
    let expected_levels = decl.univ_params.len() + 1;
    if levels.len() != expected_levels {
        return Err(TypeError::RecursorLevelCount {
            ind: ind_name.to_string(),
            expected: expected_levels,
            got: levels.len(),
        });
    }
    let target_level = levels
        .get(decl.univ_params.len())
        .cloned()
        .unwrap_or(Level::Zero);
    let target_level = reduce_level(target_level);

    // 2. If target is Prop (Zero), elimination is always allowed.
    if level_is_zero(&target_level) {
        return Ok(());
    }

    // 3. Determine whether the inductive may be a proposition: its arity ends in a sort whose
    // level is not provably nonzero (`Prop`, but also a level parameter `u` or `imax 1 u`).
    // Such an inductive is a proposition for some assignment of its level parameters, so (as in
    // Lean 4, which decides this once per declaration) it gets the restriction of propositions.
    let ctx = Context::new();
    let result_sort = result_sort_with_transparency(env, &ctx, &decl.ty, prop_ctx.transparency())?;

    let may_be_prop = result_sort.as_ref().map_or(false, |level| {
        !level_is_never_zero(&reduce_level(level.clone()))
    });

    if may_be_prop {
        // Controlled exception: allow equality eliminator (transport) into Type
        // for inductives that match the shape of Eq.
        if is_equality_inductive(decl) {
            return Ok(());
        }

        // 4. Large Elimination Restriction
        // Allowed only if 0 constructors, OR 1 constructor all of whose fields
        // (binders after the uniform parameters) are proofs.

        if decl.ctors.len() > 1 {
            return Err(TypeError::LargeElimination(ind_name.to_string()));
        }

        if decl.ctors.len() == 1 {
            let ctor = &decl.ctors[0];
            let mut ctx = Context::new();
            let mut curr = &ctor.ty;
            let mut binder_idx = 0usize;

            while let Term::Pi(dom, body, _, _) = &**curr {
                // Parameters are not fields: they are fixed by the type being eliminated.
                if binder_idx >= decl.num_params
                    && !is_proposition_with_transparency(env, &ctx, dom, prop_ctx)?
                {
                    return Err(TypeError::LargeElimination(ind_name.to_string()));
                }

                ctx = ctx.push(dom.clone());
                curr = body;
                binder_idx += 1;
            }
        }
    }
    Ok(())
}

pub fn infer(env: &Env, ctx: &Context, term: Rc<Term>) -> Result<Rc<Term>, TypeError> {
    let inferred = infer_inner(env, ctx, term.clone())?;
    if is_type_term_in_ctx(env, ctx, &inferred)? {
        ensure_type_safe(env, &term)?;
    }
    Ok(inferred)
}

fn is_type_term_in_ctx(env: &Env, ctx: &Context, ty: &Rc<Term>) -> Result<bool, TypeError> {
    Ok(matches!(
        &*whnf_in_ctx(env, ctx, ty.clone(), crate::Transparency::Reducible)?,
        Term::Sort(_)
    ))
}

/// The universe level of `ty` if `ty` is a type in `ctx`, i.e. its type reduces to a sort
/// (`Γ ⊢ ty : Sort ℓ`); `ExpectedSort` otherwise. Opaque aliases of sorts are unfolded only
/// when the reducible normal form is not already a sort.
fn infer_sort_level(env: &Env, ctx: &Context, ty: &Rc<Term>) -> Result<Level, TypeError> {
    infer_sort_level_and_type(env, ctx, ty).map(|(level, _)| level)
}

/// Like [`infer_sort_level`], also returning the type of `ty` in reducible weak head normal
/// form (a `Sort`, or an opaque alias of one).
fn infer_sort_level_and_type(
    env: &Env,
    ctx: &Context,
    ty: &Rc<Term>,
) -> Result<(Level, Rc<Term>), TypeError> {
    let ty_ty = infer(env, ctx, ty.clone())?;
    let ty_ty_norm = whnf_in_ctx(env, ctx, ty_ty.clone(), crate::Transparency::Reducible)?;
    if let Some(level) = extract_level(&ty_ty_norm) {
        return Ok((level, ty_ty_norm));
    }
    let ty_ty_full = whnf_in_ctx(env, ctx, ty_ty, crate::Transparency::All)?;
    match extract_level(&ty_ty_full) {
        Some(level) => Ok((level, ty_ty_norm)),
        None => Err(TypeError::ExpectedSort(ty_ty_norm)),
    }
}

fn infer_inner(env: &Env, ctx: &Context, term: Rc<Term>) -> Result<Rc<Term>, TypeError> {
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
        Term::Lam(ty, body, info, kind) => {
            // T-Lam: the binder type must be a type.
            ensure_type_safe(env, ty)?;
            infer_sort_level(env, ctx, ty)?;
            let new_ctx = ctx.push(ty.clone());
            let body_ty = infer(env, &new_ctx, body.clone())?;
            ensure_type_safe(env, &body_ty)?;
            let uses = term_variable_uses(env, &new_ctx, body)?;
            let required_kind =
                required_kind_from_capture_modes(&capture_modes_from_uses(env, &new_ctx, &uses)?);
            if !function_kind_leq(required_kind, *kind) {
                return Err(TypeError::FunctionKindTooSmall {
                    annotated: *kind,
                    required: required_kind,
                });
            }
            Ok(Term::pi_with_kind(ty.clone(), body_ty, *info, *kind))
        }
        Term::Pi(ty, body, _, _) => {
            // T-Pi: Pi (x : A) -> B has type Sort(imax(level(A), level(B))); both A and B
            // must be types (`ExpectedSort` otherwise).
            ensure_type_safe(env, ty)?;
            let l1 = infer_sort_level(env, ctx, ty)?;

            let new_ctx = ctx.push(ty.clone());
            ensure_type_safe(env, body)?;
            let (l2, s2_norm) = infer_sort_level_and_type(env, &new_ctx, body)?;

            // Use imax for impredicative Prop: if codomain is Prop, result is Prop.
            // If the codomain's sort is an opaque alias of Prop, the Pi lives in that same
            // alias (keeps the alias opaque for later reducible comparisons). The alias was
            // computed under the binder: it is returned only if it does not mention the bound
            // variable, with its free variables lowered by one (otherwise `Prop` itself).
            if level_is_zero(&l2) && !matches!(&*s2_norm, Term::Sort(_)) {
                let mut free = HashSet::new();
                collect_free_vars(&s2_norm, 0, &mut free);
                if !free.contains(&0) {
                    return Ok(s2_norm.subst(0, &Term::sort(Level::Zero)));
                }
            }
            let result_level = reduce_level(level_imax(l1, l2));
            Ok(Term::sort(result_level))
        }
        Term::App(f, a, _) => {
            let f_ty = infer(env, ctx, f.clone())?;
            let f_ty_norm = whnf_in_ctx(env, ctx, f_ty, crate::Transparency::Reducible)?;

            if let Term::Pi(arg_ty, body_ty, _, _) = &*f_ty_norm {
                check(env, ctx, a.clone(), arg_ty.clone())?;
                Ok(body_ty.subst(0, a))
            } else {
                Err(TypeError::ExpectedFunction(f_ty_norm))
            }
        }
        Term::Const(name, _levels) => {
            if let Some(def) = env.get_definition(name) {
                Ok(def.ty.clone())
            } else {
                Err(TypeError::UnknownConst(name.clone()))
            }
        }
        Term::LetE(ty, v, b) => {
            // T-Let: the annotation must be a type.
            ensure_type_safe(env, ty)?;
            infer_sort_level(env, ctx, ty)?;
            check(env, ctx, v.clone(), ty.clone())?;
            let new_ctx = ctx.push(ty.clone());
            let b_ty = infer(env, &new_ctx, b.clone())?;
            ensure_type_safe(env, &b_ty)?;
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
        Term::Rec(ind_name, levels) => {
            if levels.is_empty() {
                return Err(TypeError::MissingRecursorLevel(ind_name.clone()));
            }
            check_elimination_restriction(env, ind_name, levels)?;
            // Compute and return the recursor type
            if let Some(decl) = env.get_inductive(ind_name) {
                Ok(compute_recursor_type(decl, levels))
            } else {
                Err(TypeError::UnknownInductive(ind_name.clone()))
            }
        }
        Term::Fix(ty, body) => {
            // T-Fix: the type of the recursive binder must be a type.
            ensure_type_safe(env, ty)?;
            infer_sort_level(env, ctx, ty)?;
            // Restrict fixpoints to function types (Pi) for codegen soundness.
            let ty_whnf = whnf_in_ctx(env, ctx, ty.clone(), crate::Transparency::Reducible)?;
            if !matches!(&*ty_whnf, Term::Pi(_, _, _, _)) {
                return Err(TypeError::ExpectedFunction(ty_whnf));
            }
            // A fixpoint may not return a proof (K0055).
            ensure_fix_codomain_not_proof(env, ctx, &ty_whnf)?;

            // Push ty to context (this is the type of the recursive variable Var(0)). The body is
            // checked against `ty` read in that extended context, i.e. lifted over the new
            // binder: T-Fix is `Γ, f : A ⊢ t : A` with `A` weakened by one. (Checking against
            // the unlifted `ty` read every free variable of the annotation as the next binder
            // inward, so an ill-typed body was accepted and a well-typed one rejected.)
            let new_ctx = ctx.push(ty.clone());
            check(env, &new_ctx, body.clone(), ty.shift(0, 1))?;
            Ok(ty.clone())
        }
        Term::Meta(id) => Err(TypeError::UnresolvedMeta(*id)),
    }
}

/// T-Fix side condition: the result type at the end of the fixpoint's Pi telescope must not be a
/// proposition (a type whose sort may be `Prop`). Proofs are erased at run time, so a fixpoint
/// returning a proof would never run: a looping `fix` would stand for a proof of any proposition,
/// e.g. of `Eq Nat (succ zero) zero`, and transport along that "proof" would re-type a value in
/// compiled partial code. `ty_whnf` is the annotation in reducible normal form (a Pi); each
/// codomain is normalised to expose further Pis, and the final codomain's sort is inspected.
fn ensure_fix_codomain_not_proof(
    env: &Env,
    ctx: &Context,
    ty_whnf: &Rc<Term>,
) -> Result<(), TypeError> {
    let mut ctx = ctx.clone();
    let mut cur = ty_whnf.clone();
    while let Term::Pi(dom, cod, _, _) = &*cur {
        ctx = ctx.push(dom.clone());
        cur = whnf_in_ctx(env, &ctx, cod.clone(), crate::Transparency::Reducible)?;
    }
    let level = infer_sort_level(env, &ctx, &cur)?;
    if !level_is_never_zero(&level) {
        return Err(TypeError::FixProofCodomain { codomain: cur });
    }
    Ok(())
}

// =============================================================================
// Soundness Checks
// =============================================================================

/// Check if a term contains references to non-type-safe (partial) definitions
pub fn contains_partial_def(env: &Env, t: &Rc<Term>) -> Option<String> {
    match &**t {
        Term::Var(_) | Term::Sort(_) => None,
        Term::Const(name, _) => {
            if reserved_effect_totality(name).is_some() || !env.is_type_safe(name) {
                Some(name.clone())
            } else {
                None
            }
        }
        Term::App(f, a, _) => contains_partial_def(env, f).or_else(|| contains_partial_def(env, a)),
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            contains_partial_def(env, ty).or_else(|| contains_partial_def(env, body))
        }
        Term::LetE(ty, val, body) => contains_partial_def(env, ty)
            .or_else(|| contains_partial_def(env, val))
            .or_else(|| contains_partial_def(env, body)),
        Term::Fix(_, _) => Some("fix".to_string()),
        Term::Ind(_, _) | Term::Ctor(_, _, _) | Term::Rec(_, _) => None,
        Term::Meta(_) => None,
    }
}

/// Whether `t` contains a fixpoint (`fix`, general recursion) anywhere.
pub fn contains_fix(t: &Rc<Term>) -> bool {
    match &**t {
        Term::Fix(_, _) => true,
        Term::App(f, a, _) => contains_fix(f) || contains_fix(a),
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            contains_fix(ty) || contains_fix(body)
        }
        Term::LetE(ty, val, body) => contains_fix(ty) || contains_fix(val) || contains_fix(body),
        Term::Ind(_, _) | Term::Ctor(_, _, _) | Term::Rec(_, _) => false,
        Term::Const(_, _) | Term::Var(_) | Term::Sort(_) | Term::Meta(_) => false,
    }
}

pub(crate) fn reserved_effect_totality(name: &str) -> Option<Totality> {
    match name {
        "eval" => Some(Totality::Unsafe),
        _ => None,
    }
}

fn is_sort1(term: &Rc<Term>) -> bool {
    matches!(
        &**term,
        Term::Sort(Level::Succ(inner)) if matches!(**inner, Level::Zero)
    )
}

fn is_var_idx(term: &Rc<Term>, idx: usize) -> bool {
    matches!(&**term, Term::Var(i) if *i == idx)
}

fn is_const_named(term: &Rc<Term>, name: &str) -> bool {
    matches!(&**term, Term::Const(n, _) if n == name)
}

fn is_ind_named(term: &Rc<Term>, name: &str) -> bool {
    matches!(&**term, Term::Ind(n, _) if n == name)
}

fn match_pi(term: &Rc<Term>) -> Option<(Rc<Term>, Rc<Term>)> {
    match &**term {
        Term::Pi(dom, body, _, _) => Some((dom.clone(), body.clone())),
        _ => None,
    }
}

fn is_ind_app_with_var(term: &Rc<Term>, ind_name: &str, var_idx: usize) -> bool {
    let (head, args) = collect_app_spine(term);
    matches!(&*head, Term::Ind(name, _) if name == ind_name)
        && args.len() == 1
        && is_var_idx(&args[0].arg, var_idx)
}

fn check_ref_signature(ty: &Rc<Term>) -> bool {
    let Some((k_dom, rest)) = match_pi(ty) else {
        return false;
    };
    if !is_sort1(&k_dom) {
        return false;
    }
    let Some((a_dom, ret)) = match_pi(&rest) else {
        return false;
    };
    if !is_sort1(&a_dom) {
        return false;
    }
    is_sort1(&ret)
}

fn check_ref_kind_signature(ty: &Rc<Term>) -> bool {
    is_sort1(ty)
}

fn check_borrow_signature(ty: &Rc<Term>, kind_name: &str) -> bool {
    let Some((a_dom, rest)) = match_pi(ty) else {
        return false;
    };
    if !is_sort1(&a_dom) {
        return false;
    }
    let Some((x_dom, ret)) = match_pi(&rest) else {
        return false;
    };
    if !is_var_idx(&x_dom, 0) {
        return false;
    }
    let (head, args) = collect_app_spine(&ret); // Ref Shared/Mut A
    if !is_const_named(&head, "Ref") || args.len() != 2 {
        return false;
    }
    if !is_const_named(&args[0].arg, kind_name) {
        return false;
    }
    if !is_var_idx(&args[1].arg, 1) {
        return false;
    }
    true
}

fn check_index_signature(ty: &Rc<Term>, container_name: &str) -> bool {
    let Some((t_dom, rest)) = match_pi(ty) else {
        return false;
    };
    if !is_sort1(&t_dom) {
        return false;
    }
    let Some((v_dom, rest2)) = match_pi(&rest) else {
        return false;
    };
    if !is_ind_app_with_var(&v_dom, container_name, 0) {
        return false;
    }
    let Some((i_dom, ret)) = match_pi(&rest2) else {
        return false;
    };
    if !is_ind_named(&i_dom, "Nat") {
        return false;
    }
    if !is_var_idx(&ret, 2) {
        return false;
    }
    true
}

fn reserved_primitive_requires_unsafe(name: &str) -> bool {
    matches!(name, "index_vec_dyn" | "index_slice" | "index_array")
}

fn reserved_primitive_signature_ok(name: &str, ty: &Rc<Term>) -> bool {
    match name {
        "Ref" => check_ref_signature(ty),
        "Shared" | "Mut" => check_ref_kind_signature(ty),
        "borrow_shared" => check_borrow_signature(ty, "Shared"),
        "borrow_mut" => check_borrow_signature(ty, "Mut"),
        "index_vec_dyn" => check_index_signature(ty, "VecDyn"),
        "index_slice" => check_index_signature(ty, "Slice"),
        "index_array" => check_index_signature(ty, "Array"),
        _ => true,
    }
}

fn ensure_type_safe(env: &Env, t: &Rc<Term>) -> Result<(), TypeError> {
    if let Some(name) = contains_partial_def(env, t) {
        Err(TypeError::PartialInType(name))
    } else {
        Ok(())
    }
}

/// Check if a term contains a specific constant (by name)
fn contains_const(t: &Rc<Term>, name: &str) -> bool {
    match &**t {
        Term::Var(_) | Term::Sort(_) => false,
        Term::Const(n, _) | Term::Ind(n, _) | Term::Ctor(n, _, _) | Term::Rec(n, _) => n == name,
        Term::App(f, a, _) => contains_const(f, name) || contains_const(a, name),
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) | Term::Fix(ty, body) => {
            contains_const(ty, name) || contains_const(body, name)
        }
        Term::LetE(ty, val, body) => {
            contains_const(ty, name) || contains_const(val, name) || contains_const(body, name)
        }
        Term::Meta(_) => false,
    }
}

/// `t` with every `let` expanded (zeta-reduced): `let x : A := v in b` becomes `b[v/x]`.
/// Zeta is part of definitional equality, so the result is definitionally equal to `t`.
/// Inductive declarations are zeta-expanded before their syntactic checks (`add_inductive`).
fn zeta_expand(t: &Rc<Term>) -> Rc<Term> {
    zeta_expand_changed(t).unwrap_or_else(|| t.clone())
}

/// `Some(expansion)` if `t` contains a `let`, `None` if `t` is let-free (and so unchanged).
fn zeta_expand_changed(t: &Rc<Term>) -> Option<Rc<Term>> {
    fn pair(
        a: &Rc<Term>,
        b: &Rc<Term>,
        rebuild: impl FnOnce(Rc<Term>, Rc<Term>) -> Term,
    ) -> Option<Rc<Term>> {
        let (a2, b2) = (zeta_expand_changed(a), zeta_expand_changed(b));
        if a2.is_none() && b2.is_none() {
            return None;
        }
        Some(Rc::new(rebuild(
            a2.unwrap_or_else(|| a.clone()),
            b2.unwrap_or_else(|| b.clone()),
        )))
    }
    match &**t {
        Term::LetE(_, val, body) => Some(zeta_expand(body).subst(0, &zeta_expand(val))),
        Term::App(f, a, label) => pair(f, a, |f, a| Term::App(f, a, label.clone())),
        Term::Lam(ty, body, info, kind) => {
            pair(ty, body, |ty, body| Term::Lam(ty, body, *info, *kind))
        }
        Term::Pi(ty, body, info, kind) => {
            pair(ty, body, |ty, body| Term::Pi(ty, body, *info, *kind))
        }
        Term::Fix(ty, body) => pair(ty, body, Term::Fix),
        Term::Var(_)
        | Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => None,
    }
}

/// Check whether a constructor field contains a nested recursive occurrence.
/// Direct recursive fields are allowed only when the inductive is the head and
/// is fully applied to its parameters, with no nested occurrences in arguments.
fn contains_nested_inductive(term: &Rc<Term>, ind_name: &str) -> bool {
    match &**term {
        Term::App(_, _, _) => {
            let (head, args) = collect_app_spine(term);
            if let Term::Ind(name, _) = &*head {
                if name == ind_name {
                    for arg in &args {
                        if contains_const(&arg.arg, ind_name) {
                            return true;
                        }
                    }
                    return false;
                }
            }

            if contains_const(&head, ind_name) {
                return true;
            }
            for arg in &args {
                if contains_const(&arg.arg, ind_name) {
                    return true;
                }
            }
            false
        }
        Term::Ind(_, _) => false,
        Term::Pi(dom, body, _, _) | Term::Lam(dom, body, _, _) | Term::Fix(dom, body) => {
            contains_nested_inductive(dom, ind_name) || contains_nested_inductive(body, ind_name)
        }
        Term::LetE(ty, val, body) => {
            // Zeta: the let-bound variable stands for `val`, so look at the body with `val`
            // substituted (`let X := I in List X` is the nested occurrence `List I`).
            contains_nested_inductive(ty, ind_name)
                || contains_nested_inductive(val, ind_name)
                || contains_nested_inductive(&body.subst(0, val), ind_name)
        }
        Term::Var(_)
        | Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => false,
    }
}

/// Where a subterm of a constructor field type sits: `Positive` = reachable from the field type
/// through Pi codomains, applications and binders only; `Negative` = inside the domain of some
/// Pi (at any depth). Strict positivity forbids every occurrence of the inductive in a
/// `Negative` position; there is no flipping back (see `check_strict_positivity`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Polarity {
    Positive,
    Negative,
}

fn check_inductive_params(
    ind_name: &str,
    num_params: usize,
    args: &[Rc<Term>],
    depth: usize,
) -> Result<(), String> {
    if args.len() < num_params {
        return Err(format!(
            "inductive {} applied to fewer than {} parameters",
            ind_name, num_params
        ));
    }
    if depth < num_params {
        return Err(format!(
            "inductive {} parameters out of scope (depth {}, params {})",
            ind_name, depth, num_params
        ));
    }

    for (param_idx, arg) in args.iter().take(num_params).enumerate() {
        let expected = depth - 1 - param_idx;
        match &**arg {
            Term::Var(idx) if *idx == expected => {}
            _ => {
                return Err(format!(
                    "inductive {} parameter {} is not the expected binder (expected Var({}))",
                    ind_name, param_idx, expected
                ));
            }
        }
    }
    Ok(())
}

/// Strict positivity check for a constructor argument type (as in Lean 4 and Coq): the
/// inductive may occur only as the head of the field type, or of the codomain of a Pi in it,
/// applied to its parameters; it must not occur in the domain of any Pi, at any depth. So
/// `(I -> X) -> I` is rejected, and so is `((I -> X) -> Y) -> I`: that occurrence is positive
/// but not strictly positive, and with an impredicative Prop it gives a proof of False
/// (Coquand-Paulin: `intro : ((A -> Prop) -> Prop) -> A`). A `let` is zeta-reduced, so a
/// let-bound variable cannot hide an occurrence (`add_inductive` also expands lets up front).
fn check_strict_positivity(
    ind_name: &str,
    num_params: usize,
    term: &Rc<Term>,
    depth: usize,
    polarity: Polarity,
) -> Result<(), String> {
    // Fast path: if the term doesn't mention the inductive at all, it's OK.
    if !contains_const(term, ind_name) {
        return Ok(());
    }

    match &**term {
        Term::App(_, _, _) => {
            let (head, args) = collect_app_spine(term);
            if let Term::Ind(name, _) = &*head {
                if name == ind_name {
                    if polarity == Polarity::Negative {
                        return Err(format!(
                            "inductive {} occurs in negative position",
                            ind_name
                        ));
                    }
                    let arg_terms: Vec<Rc<Term>> =
                        args.iter().map(|item| item.arg.clone()).collect();
                    check_inductive_params(ind_name, num_params, &arg_terms, depth)?;
                    for arg in &args {
                        check_strict_positivity(ind_name, num_params, &arg.arg, depth, polarity)?;
                    }
                    return Ok(());
                }
            }

            check_strict_positivity(ind_name, num_params, &head, depth, polarity)?;
            for arg in &args {
                check_strict_positivity(ind_name, num_params, &arg.arg, depth, polarity)?;
            }
            Ok(())
        }
        Term::Ind(name, _) if name == ind_name => {
            if polarity == Polarity::Negative {
                return Err(format!(
                    "inductive {} occurs in negative position",
                    ind_name
                ));
            }
            check_inductive_params(ind_name, num_params, &[], depth)?;
            Ok(())
        }
        Term::Pi(dom, body, _, _) => {
            // Everything inside a domain is negative for good: a second arrow does not make
            // an occurrence strictly positive again.
            check_strict_positivity(ind_name, num_params, dom, depth, Polarity::Negative)?;
            check_strict_positivity(ind_name, num_params, body, depth + 1, polarity)
        }
        Term::Lam(dom, body, _, _) | Term::Fix(dom, body) => {
            check_strict_positivity(ind_name, num_params, dom, depth, polarity)?;
            check_strict_positivity(ind_name, num_params, body, depth + 1, polarity)
        }
        Term::LetE(ty, val, body) => {
            // Zeta: the let-bound variable stands for `val`, so check the body with `val`
            // substituted (a negative use of the variable is a negative use of `val`).
            check_strict_positivity(ind_name, num_params, ty, depth, polarity)?;
            check_strict_positivity(ind_name, num_params, val, depth, polarity)?;
            check_strict_positivity(ind_name, num_params, &body.subst(0, val), depth, polarity)
        }
        Term::Const(_, _)
        | Term::Sort(_)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Var(_)
        | Term::Meta(_) => Ok(()),
    }
}

fn is_equality_inductive(decl: &InductiveDecl) -> bool {
    if decl.ctors.len() != 1 {
        return false;
    }

    // Eq : (A : Type u) -> (a : A) -> (b : A) -> Prop
    let (binders, result_sort) = extract_pi_binders(&decl.ty);
    if binders.len() != 3 {
        return false;
    }
    if result_sort.as_ref().map_or(true, |lvl| !level_is_zero(lvl)) {
        return false;
    }
    if !matches!(&*binders[0].0, Term::Sort(_)) {
        return false;
    }
    if !matches!(&*binders[1].0, Term::Var(0)) {
        return false;
    }
    if !matches!(&*binders[2].0, Term::Var(1)) {
        return false;
    }

    // refl : (A : Type u) -> (a : A) -> Eq A a a
    let ctor = &decl.ctors[0];
    let (ctor_binders, ctor_body) = peel_pi_binders(&ctor.ty);
    if ctor_binders.len() != 2 {
        return false;
    }
    if !matches!(&*ctor_binders[0].0, Term::Sort(_)) {
        return false;
    }
    if !matches!(&*ctor_binders[1].0, Term::Var(0)) {
        return false;
    }

    let (head, args) = collect_app_spine(&ctor_body);
    match &*head {
        Term::Ind(name, _) if name == &decl.name => {}
        _ => return false,
    }
    if args.len() != 3 {
        return false;
    }
    if !matches!(&*args[0].arg, Term::Var(1)) {
        return false;
    }
    if !matches!(&*args[1].arg, Term::Var(0)) {
        return false;
    }
    if !matches!(&*args[2].arg, Term::Var(0)) {
        return false;
    }

    true
}

/// Check universe levels for an inductive type
fn collect_level_params_in_level(level: &Level, out: &mut HashSet<String>) {
    match level {
        Level::Param(name) => {
            out.insert(name.clone());
        }
        Level::Succ(inner) => collect_level_params_in_level(inner, out),
        Level::Max(a, b) | Level::IMax(a, b) => {
            collect_level_params_in_level(a, out);
            collect_level_params_in_level(b, out);
        }
        Level::Zero => {}
    }
}

fn collect_level_params_in_term(term: &Rc<Term>, out: &mut HashSet<String>) {
    match &**term {
        Term::Sort(level) => collect_level_params_in_level(level, out),
        Term::Const(_, levels)
        | Term::Ind(_, levels)
        | Term::Ctor(_, _, levels)
        | Term::Rec(_, levels) => {
            for level in levels {
                collect_level_params_in_level(level, out);
            }
        }
        Term::App(f, a, _) => {
            collect_level_params_in_term(f, out);
            collect_level_params_in_term(a, out);
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) | Term::Fix(ty, body) => {
            collect_level_params_in_term(ty, out);
            collect_level_params_in_term(body, out);
        }
        Term::LetE(ty, val, body) => {
            collect_level_params_in_term(ty, out);
            collect_level_params_in_term(val, out);
            collect_level_params_in_term(body, out);
        }
        Term::Var(_) | Term::Meta(_) => {}
    }
}

/// Universe rule for inductive declarations (as in Lean 4 and Coq).
///
/// Let the arity of `decl` end in `Sort u` (read through aliases, transparent or opaque).
/// * If `u` is `Prop` (level zero) nothing is checked here: an inductive proposition may have
///   fields of any universe; what it may be eliminated into is governed by the elimination
///   restriction (`check_elimination_restriction`).
/// * Otherwise every constructor FIELD must have a type whose own sort is at most `u`: for a
///   field `(x : A)`, `Γ ⊢ A : Sort v` with `v ≤ u`. The fields are the binders of the
///   constructor type after its first `decl.num_params` binders (constructor types repeat the
///   uniform parameters as their leading binders; the parameters are fixed by the type of the
///   value and are not fields). The level `v` is computed uniformly as the sort of the inferred
///   type of `A` (`infer_sort_level`), so a field of type `Sort l` has level `l + 1` and a field
///   of type `Π x : Nat, Sort 1` has level 2. Accepting `v = l` for a field of type `Sort l`
///   (the rule before this one) made `Sort 1` a definitional retract of a type in `Sort 1`
///   (`El (mkU A) ≡ A`, the setting of Hurkens' paradox for `Type : Type`).
/// * Parameters and indices of the arity are not constrained (Lean 4 and Coq do not constrain
///   them either): a parameter is never stored, and an index is determined by the type of the
///   value, so neither lets a value of the inductive carry a larger universe. E.g.
///   `(inductive T (pi A (sort 1) (sort 1)) (ctor mkT (T Nat)))` lives in `Sort 1`.
///
/// Universe-level parameters must be declared in `decl.univ_params`. Levels are compared with
/// `level_leq`, which holds only when `v <= u` for every assignment of the level parameters
/// (Lean 4's comparison; sound but not complete). Surface programs only write concrete levels,
/// for which the comparison is exact.
fn check_universe_levels(env: &Env, decl: &InductiveDecl) -> Result<(), String> {
    // The result sort may be written through an alias (e.g. an opaque alias of a sort): use
    // its unfolded level, so that such an arity does not bypass the check.
    let result_sort =
        result_sort_with_transparency(env, &Context::new(), &decl.ty, crate::Transparency::All)
            .map_err(|err| format!("inductive {} arity: {:?}", decl.name, err))?;
    let ind_level = match result_sort {
        Some(level) => reduce_level(level),
        None => {
            return Err(format!(
                "inductive {} arity does not end in a sort",
                decl.name
            ))
        }
    };

    let mut used_params = HashSet::new();
    collect_level_params_in_term(&decl.ty, &mut used_params);
    for ctor in &decl.ctors {
        collect_level_params_in_term(&ctor.ty, &mut used_params);
    }
    let allowed: HashSet<&str> = decl.univ_params.iter().map(|name| name.as_str()).collect();
    for param in used_params {
        if !allowed.contains(param.as_str()) {
            return Err(format!("unknown universe parameter {}", param));
        }
    }

    if level_is_zero(&ind_level) {
        return Ok(());
    }

    for ctor in &decl.ctors {
        // Constructor types are closed: each binder type is well scoped in the context of
        // the constructor's own preceding binders (parameters first), starting from empty.
        let mut ctx = Context::new();
        let mut curr = ctor.ty.clone();
        let mut binder_idx = 0usize;

        while let Term::Pi(dom, body, _, _) = &*curr {
            if binder_idx >= decl.num_params {
                let field_idx = binder_idx - decl.num_params;
                let level = infer_sort_level(env, &ctx, dom).map_err(|err| {
                    format!(
                        "constructor {} field {} (argument {}): {:?}",
                        ctor.name, field_idx, binder_idx, err
                    )
                })?;
                let level = reduce_level(level);
                if !level_leq(&level, &ind_level) {
                    return Err(format!(
                        "constructor {} field {} (argument {}) has a type in universe level {:?}, which is above inductive level {:?}",
                        ctor.name, field_idx, binder_idx, level, ind_level
                    ));
                }
            }

            ctx = ctx.push(dom.clone());
            curr = body.clone();
            binder_idx += 1;
        }
    }

    Ok(())
}

fn term_depends_on_params(term: &Rc<Term>, param_count: usize, depth: usize) -> bool {
    match &**term {
        Term::Var(idx) => {
            if *idx >= depth {
                let outer = *idx - depth;
                outer < param_count
            } else {
                false
            }
        }
        Term::App(f, a, _) => {
            term_depends_on_params(f, param_count, depth)
                || term_depends_on_params(a, param_count, depth)
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            term_depends_on_params(ty, param_count, depth)
                || term_depends_on_params(body, param_count, depth + 1)
        }
        Term::LetE(ty, val, body) => {
            term_depends_on_params(ty, param_count, depth)
                || term_depends_on_params(val, param_count, depth)
                || term_depends_on_params(body, param_count, depth + 1)
        }
        Term::Fix(ty, body) => {
            term_depends_on_params(ty, param_count, depth)
                || term_depends_on_params(body, param_count, depth + 1)
        }
        Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => false,
    }
}

fn remap_copy_requirement(
    term: &Rc<Term>,
    depth: usize,
    binder_pos: usize,
    total_binders: usize,
    param_count: usize,
    body_to_param: &HashMap<usize, usize>,
) -> Option<Rc<Term>> {
    match &**term {
        Term::Var(idx) => {
            if *idx < depth {
                return Some(Rc::new(Term::Var(*idx)));
            }
            let outer = *idx - depth;
            let body_index = total_binders - binder_pos + outer;
            if body_index >= total_binders {
                return None;
            }
            let param_pos = *body_to_param.get(&body_index)?;
            let new_idx = depth + (param_count - 1 - param_pos);
            Some(Rc::new(Term::Var(new_idx)))
        }
        Term::Sort(lvl) => Some(Rc::new(Term::Sort(lvl.clone()))),
        Term::Const(name, levels) => Some(Rc::new(Term::Const(name.clone(), levels.clone()))),
        Term::Ind(name, levels) => Some(Rc::new(Term::Ind(name.clone(), levels.clone()))),
        Term::Ctor(name, idx, levels) => {
            Some(Rc::new(Term::Ctor(name.clone(), *idx, levels.clone())))
        }
        Term::Rec(name, levels) => Some(Rc::new(Term::Rec(name.clone(), levels.clone()))),
        Term::Meta(id) => Some(Rc::new(Term::Meta(*id))),
        Term::App(f, a, label) => {
            let f_new = remap_copy_requirement(
                f,
                depth,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            let a_new = remap_copy_requirement(
                a,
                depth,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            Some(Rc::new(Term::App(f_new, a_new, label.clone())))
        }
        Term::Lam(ty, body, info, kind) => {
            let ty_new = remap_copy_requirement(
                ty,
                depth,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            let body_new = remap_copy_requirement(
                body,
                depth + 1,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            Some(Rc::new(Term::Lam(ty_new, body_new, *info, *kind)))
        }
        Term::Pi(ty, body, info, kind) => {
            let ty_new = remap_copy_requirement(
                ty,
                depth,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            let body_new = remap_copy_requirement(
                body,
                depth + 1,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            Some(Rc::new(Term::Pi(ty_new, body_new, *info, *kind)))
        }
        Term::LetE(ty, val, body) => {
            let ty_new = remap_copy_requirement(
                ty,
                depth,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            let val_new = remap_copy_requirement(
                val,
                depth,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            let body_new = remap_copy_requirement(
                body,
                depth + 1,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            Some(Rc::new(Term::LetE(ty_new, val_new, body_new)))
        }
        Term::Fix(ty, body) => {
            let ty_new = remap_copy_requirement(
                ty,
                depth,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            let body_new = remap_copy_requirement(
                body,
                depth + 1,
                binder_pos,
                total_binders,
                param_count,
                body_to_param,
            )?;
            Some(Rc::new(Term::Fix(ty_new, body_new)))
        }
    }
}

/// Derives the structural `Copy` instance of an inductive type, if it has one.
///
/// The instance is parameterised by the uniform *parameters* of the type (`decl.num_params`)
/// only. Every constructor binder after the parameters is a runtime field, including binders that
/// occur as index arguments of the constructor's result type: indices are not parameters, so an
/// index binder of a constructor is stored like any other field. Each field adds the requirement
/// "the field's type is Copy", expressed over the parameters:
/// - a recursive field (the type itself, applied to its parameters and any indices) adds nothing,
///   because whether a value of the type is Copy does not depend on its indices; this is what makes
///   indexed families such as `Vec A n` Copy exactly when `A` is;
/// - for a field whose type is another inductive family, only that family's parameter arguments
///   are kept (its derived instance depends on parameters only);
/// - a field whose type depends on an earlier field in any other way cannot be expressed over the
///   parameters, and derivation fails (the type is then not Copy);
/// - a non-uniform recursive occurrence (the type applied to other parameters) also makes
///   derivation fail.
fn derive_copy_instance(env: &mut Env, decl: &InductiveDecl) -> Result<(), String> {
    let inst = compute_derived_copy_instance(env, decl)?;
    env.push_copy_instance(inst);
    Ok(())
}

/// The Copy instance the kernel derives for `decl` (no registration), or why none exists.
fn compute_derived_copy_instance(env: &Env, decl: &InductiveDecl) -> Result<CopyInstance, String> {
    if env
        .marker_registry
        .has_marker(&decl.markers, TypeMarker::InteriorMutable)
        .map_err(|e| e.to_string())?
    {
        return Err("interior-mutable types do not derive Copy".to_string());
    }
    if env
        .marker_registry
        .has_marker(&decl.markers, TypeMarker::Affine)
        .map_err(|e| e.to_string())?
    {
        return Err("affine types do not derive Copy".to_string());
    }

    let param_count = decl.num_params;
    let mut requirements = Vec::new();

    for ctor in &decl.ctors {
        let binder_count = count_pi_binders(&ctor.ty);
        if binder_count < param_count {
            return Err(format!(
                "constructor {} binds fewer than {} parameters",
                ctor.name, param_count
            ));
        }
        // The first `param_count` binders of a constructor are the type's parameters.
        let body_to_param: HashMap<usize, usize> = (0..param_count)
            .map(|param_pos| (binder_count - 1 - param_pos, param_pos))
            .collect();

        let mut curr = ctor.ty.clone();
        let mut pos = 0usize;
        while let Term::Pi(dom, body, _, _) = &*curr {
            if pos >= param_count {
                let field_idx = pos - param_count;
                match self_occurrence(dom, &decl.name, param_count, pos) {
                    SelfOccurrence::Uniform => {}
                    SelfOccurrence::NonUniform => {
                        return Err(format!(
                            "constructor {} field {} is a non-uniform recursive occurrence",
                            ctor.name, field_idx
                        ));
                    }
                    SelfOccurrence::None => {
                        let field_ty = drop_family_indices(env, dom);
                        let remapped = remap_copy_requirement(
                            &field_ty,
                            0,
                            pos,
                            binder_count,
                            param_count,
                            &body_to_param,
                        )
                        .ok_or_else(|| {
                            format!(
                                "constructor {} field {} depends on other constructor fields",
                                ctor.name, field_idx
                            )
                        })?;
                        if !requirements.iter().any(|req| req == &remapped) {
                            requirements.push(remapped);
                        }
                    }
                }
            }
            pos += 1;
            curr = body.clone();
        }
    }

    // If any requirement is closed and not Copy, derivation fails.
    let ctx = Context::new();
    for req in &requirements {
        if !term_depends_on_params(req, param_count, 0)
            && !is_copy_type(env, &ctx, req).map_err(|e| format!("Copy check failed: {}", e))?
        {
            return Err(format!("field requirement {:?} is not Copy", req));
        }
    }

    Ok(CopyInstance {
        ind_name: decl.name.clone(),
        param_count,
        requirements,
        source: CopyInstanceSource::Derived,
        is_unsafe: false,
    })
}

/// How a constructor field type refers to the inductive type being declared.
enum SelfOccurrence {
    /// The field type does not have the declared type as its head.
    None,
    /// The declared type applied to its own parameters (in order) and any index arguments.
    Uniform,
    /// The declared type applied to anything else in parameter position.
    NonUniform,
}

/// Classifies a field type `dom` found at constructor binder position `pos` (so the parameter
/// binder `i` is `Var(pos - 1 - i)` in `dom`'s context).
fn self_occurrence(
    dom: &Rc<Term>,
    ind_name: &str,
    param_count: usize,
    pos: usize,
) -> SelfOccurrence {
    let (head, args) = collect_app_spine(dom);
    match &*head {
        Term::Ind(name, _) if name == ind_name => {
            if args.len() < param_count {
                return SelfOccurrence::NonUniform;
            }
            let uniform = args
                .iter()
                .take(param_count)
                .enumerate()
                .all(|(i, arg)| matches!(&*arg.arg, Term::Var(idx) if *idx + 1 + i == pos));
            if uniform {
                SelfOccurrence::Uniform
            } else {
                SelfOccurrence::NonUniform
            }
        }
        _ => SelfOccurrence::None,
    }
}

/// If `ty` is an inductive family applied to more arguments than it has parameters, drops the
/// index arguments (Copy instances are derived over parameters only, see `derive_copy_instance`).
fn drop_family_indices(env: &Env, ty: &Rc<Term>) -> Rc<Term> {
    let (head, args) = collect_app_spine(ty);
    if let Term::Ind(name, _) = &*head {
        if let Some(decl) = env.get_inductive(name) {
            if args.len() > decl.num_params {
                let mut out = head.clone();
                for item in args.iter().take(decl.num_params) {
                    out = Rc::new(Term::App(out, item.arg.clone(), item.label.clone()));
                }
                return out;
            }
        }
    }
    ty.clone()
}

/// The arity of `decl` must be a type of the form `Π (x1 : A1) ... (xn : An). S` whose
/// binders are written out and whose result `S` is a sort or (an alias that unfolds to) a sort,
/// and every constructor type must be a type (`ExpectedSort` otherwise). Binders hidden behind
/// an alias are rejected: the parameter/index count, the recursor and the constructor checks
/// read the telescope syntactically. Expects the inductive itself to be registered (as a
/// placeholder) in `env`.
fn check_inductive_arity_and_ctor_types(env: &Env, decl: &InductiveDecl) -> Result<(), TypeError> {
    let ctx = Context::new();
    infer_sort_level(env, &ctx, &decl.ty)?;
    let mut tail = decl.ty.clone();
    let mut tail_ctx = ctx.clone();
    while let Term::Pi(dom, body, _, _) = &*tail {
        tail_ctx = tail_ctx.push(dom.clone());
        tail = body.clone();
    }
    if !matches!(&*tail, Term::Sort(_)) {
        let tail_norm = whnf_in_ctx(env, &tail_ctx, tail.clone(), crate::Transparency::All)?;
        if !matches!(&*tail_norm, Term::Sort(_)) {
            return Err(TypeError::ExpectedSort(tail_norm));
        }
    }
    for ctor in &decl.ctors {
        infer_sort_level(env, &ctx, &ctor.ty)?;
    }
    Ok(())
}

pub fn check_inductive_soundness(env: &Env, decl: &InductiveDecl) -> Result<(), TypeError> {
    // 0. Constructor return type must be the inductive applied to all params/indices, and
    //    these arguments may not mention the inductive itself (as in Lean 4 and Coq): an
    //    occurrence in an index of the result, e.g. `base : T (T Tru -> False)`, is not a
    //    strictly positive occurrence, and the recursor's motive would be applied to it.
    let total_binders = count_pi_binders(&decl.ty);
    for ctor in &decl.ctors {
        let (_binder_count, args) =
            ctor_return_inductive_args(&decl.name, &ctor.name, &ctor.ty, total_binders)?;
        if let Some(arg) = args.iter().position(|arg| contains_const(arg, &decl.name)) {
            return Err(TypeError::InductiveInCtorResultArg {
                ind: decl.name.clone(),
                ctor: ctor.name.clone(),
                arg,
            });
        }
    }

    // 0b. Well-formedness of the declaration (premises of T-Ind / T-Ctor): the arity is a
    //     telescope of types written out, ending in a sort or an alias of one (the checks
    //     below and the recursor read the telescope syntactically), and every
    //     constructor type is a type, i.e. its binder types are types and its result applies
    //     the inductive to arguments of the arity's binder types. Without this, an arity such
    //     as an empty proposition made `Ind` itself a closed proof of it.
    check_inductive_arity_and_ctor_types(env, decl)?;

    // 1. Check strict positivity with polarity tracking
    for ctor in &decl.ctors {
        let (binders, _) = peel_pi_binders(&ctor.ty);
        for (arg_idx, (arg_ty, _)) in binders.iter().enumerate() {
            if let Err(_msg) = check_strict_positivity(
                &decl.name,
                decl.num_params,
                arg_ty,
                arg_idx,
                Polarity::Positive,
            ) {
                return Err(TypeError::NonPositiveOccurrence(
                    decl.name.clone(),
                    ctor.name.clone(),
                    arg_idx,
                ));
            }
        }
    }

    // 1b. Reject nested inductive occurrences in constructor fields.
    for ctor in &decl.ctors {
        let mut curr = ctor.ty.clone();
        let mut binder_idx = 0usize;
        while let Term::Pi(dom, body, _, _) = &*curr {
            if binder_idx >= decl.num_params && contains_nested_inductive(dom, &decl.name) {
                let field_idx = binder_idx - decl.num_params;
                return Err(TypeError::NestedInductive {
                    ind: decl.name.clone(),
                    ctor: ctor.name.clone(),
                    field: field_idx,
                });
            }
            curr = body.clone();
            binder_idx += 1;
        }
    }

    // 2. Disallow Prop-typed fields in data inductives
    let decl_ctx = Context::new();
    let result_sort = result_sort_with_transparency(
        env,
        &decl_ctx,
        &decl.ty,
        PropTransparencyContext::UnfoldOpaque.transparency(),
    )?;
    let is_prop_ind = result_sort.as_ref().map_or(false, level_is_zero);
    if !is_prop_ind {
        for ctor in &decl.ctors {
            let mut ctx = Context::new();
            let mut curr = ctor.ty.clone();
            let mut binder_idx = 0usize;

            while let Term::Pi(dom, body, _, _) = &*curr {
                if binder_idx >= decl.num_params
                    && is_prop_like_with_transparency(
                        env,
                        &ctx,
                        dom,
                        PropTransparencyContext::UnfoldOpaque,
                    )?
                {
                    let field_idx = binder_idx - decl.num_params;
                    return Err(TypeError::PropFieldInData {
                        ind: decl.name.clone(),
                        ctor: ctor.name.clone(),
                        field: field_idx,
                    });
                }

                ctx = ctx.push(dom.clone());
                curr = body.clone();
                binder_idx += 1;
            }
        }
    } else {
        // Prop inductives skip universe checks; still validate constructor domains.
        for ctor in &decl.ctors {
            let mut ctx = Context::new();
            let mut curr = ctor.ty.clone();
            while let Term::Pi(dom, body, _, _) = &*curr {
                let _ = infer(env, &ctx, dom.clone())?;
                ensure_type_safe(env, dom)?;
                ctx = ctx.push(dom.clone());
                curr = body.clone();
            }
        }
    }

    // 3. Universe check
    if let Err(msg) = check_universe_levels(env, decl) {
        return Err(TypeError::UniverseLevelTooSmall(
            decl.name.clone(),
            "type".to_string(),
            "ctor".to_string(),
            msg,
        ));
    }

    Ok(())
}

/// Whether some subterm of `t` (including `t`) satisfies `pred`.
fn term_mentions(t: &Rc<Term>, pred: &dyn Fn(&Term) -> bool) -> bool {
    if pred(t) {
        return true;
    }
    match &**t {
        Term::App(f, a, _) => term_mentions(f, pred) || term_mentions(a, pred),
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) | Term::Fix(ty, body) => {
            term_mentions(ty, pred) || term_mentions(body, pred)
        }
        Term::LetE(ty, val, body) => {
            term_mentions(ty, pred) || term_mentions(val, pred) || term_mentions(body, pred)
        }
        Term::Var(_)
        | Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => false,
    }
}

fn collect_axioms_rec(
    env: &Env,
    t: &Rc<Term>,
    axioms: &mut HashSet<String>,
    primitives: &mut HashSet<String>,
) {
    match &**t {
        Term::Const(name, _) => {
            if let Some(def) = env.get_definition(name) {
                for ax in &def.axioms {
                    axioms.insert(ax.clone());
                }
                for prim in &def.primitive_deps {
                    primitives.insert(prim.clone());
                }
            }
        }
        Term::Ind(name, _) | Term::Rec(name, _) => {
            if let Some(decl) = env.get_inductive(name) {
                for ax in &decl.axioms {
                    axioms.insert(ax.clone());
                }
                for prim in &decl.primitive_deps {
                    primitives.insert(prim.clone());
                }
            }
        }
        Term::Ctor(ind_name, _, _) => {
            if let Some(decl) = env.get_inductive(ind_name) {
                for ax in &decl.axioms {
                    axioms.insert(ax.clone());
                }
                for prim in &decl.primitive_deps {
                    primitives.insert(prim.clone());
                }
            }
        }
        Term::App(f, a, _) => {
            collect_axioms_rec(env, f, axioms, primitives);
            collect_axioms_rec(env, a, axioms, primitives);
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            collect_axioms_rec(env, ty, axioms, primitives);
            collect_axioms_rec(env, body, axioms, primitives);
        }
        Term::LetE(ty, val, body) => {
            collect_axioms_rec(env, ty, axioms, primitives);
            collect_axioms_rec(env, val, axioms, primitives);
            collect_axioms_rec(env, body, axioms, primitives);
        }
        Term::Fix(ty, body) => {
            collect_axioms_rec(env, ty, axioms, primitives);
            collect_axioms_rec(env, body, axioms, primitives);
        }
        _ => {}
    }
}

/// Collect transitive axiom dependencies for an arbitrary term.
pub fn term_axiom_dependencies(env: &Env, t: &Rc<Term>) -> Vec<String> {
    let mut used_axioms = HashSet::new();
    let mut used_primitives = HashSet::new();
    collect_axioms_rec(env, t, &mut used_axioms, &mut used_primitives);
    let mut axioms: Vec<String> = used_axioms.into_iter().collect();
    axioms.sort();
    axioms
}

/// Collect transitive primitive dependencies for an arbitrary term.
pub fn term_primitive_dependencies(env: &Env, t: &Rc<Term>) -> Vec<String> {
    let mut used_axioms = HashSet::new();
    let mut used_primitives = HashSet::new();
    collect_axioms_rec(env, t, &mut used_axioms, &mut used_primitives);
    let mut prims: Vec<String> = used_primitives.into_iter().collect();
    prims.sort();
    prims
}

// =============================================================================
// Classical Axiom Tracking
// =============================================================================

/// Extract the subset of axiom dependencies that are classified by a given tag.
pub fn axiom_dependencies_with_tag(env: &Env, axioms: &[String], tag: AxiomTag) -> Vec<String> {
    let mut deps: Vec<String> = axioms
        .iter()
        .filter(|ax| {
            env.axiom_tag_snapshot
                .get(ax.as_str())
                .map(|tags| tags.contains(&tag))
                .unwrap_or(false)
        })
        .cloned()
        .collect();
    deps.sort();
    deps.dedup();
    deps
}

/// Extract the subset of axiom dependencies that are classified as classical.
pub fn classical_axiom_dependencies(env: &Env, def: &Definition) -> Vec<String> {
    axiom_dependencies_with_tag(env, &def.axioms, AxiomTag::Classical)
}

// =============================================================================
// Effect System Checks (Phase 5)
// =============================================================================

/// Check if a term respects effect boundaries based on the allowed context.
///
/// Rules:
/// - Total context: Cannot call Partial or Unsafe.
/// - Partial context: Cannot call Unsafe.
/// - Unsafe context: Can call anything.
pub fn check_effects(env: &Env, allowed_context: Totality, t: &Rc<Term>) -> Result<(), TypeError> {
    if allowed_context == Totality::Unsafe {
        return Ok(()); // Unsafe code can do anything
    }

    match &**t {
        Term::Const(name, _) => {
            if let Some(reserved_totality) = reserved_effect_totality(name) {
                return enforce_effect_boundary(allowed_context, reserved_totality, name);
            }

            if let Some(def) = env.get_definition(name) {
                let called_totality = def.effective_totality();
                return enforce_effect_boundary(allowed_context, called_totality, name);
            }
            Ok(())
        }
        Term::App(f, a, _) => {
            check_effects(env, allowed_context, f)?;
            check_effects(env, allowed_context, a)
        }
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            check_effects(env, allowed_context, ty)?;
            check_effects(env, allowed_context, body)
        }
        Term::LetE(ty, val, body) => {
            check_effects(env, allowed_context, ty)?;
            check_effects(env, allowed_context, val)?;
            check_effects(env, allowed_context, body)
        }
        Term::Fix(ty, body) => {
            // Fix is inherently Partial (general recursion)
            match allowed_context {
                Totality::Total | Totality::WellFounded => Err(TypeError::EffectError(
                    "Total".to_string(),
                    "Partial".to_string(),
                    "fix".to_string(),
                )),
                _ => {
                    check_effects(env, allowed_context, ty)?;
                    check_effects(env, allowed_context, body)
                }
            }
        }
        // Ind, Ctor, Rec are primitives (effectively Total)
        Term::Ind(_, _) | Term::Ctor(_, _, _) | Term::Rec(_, _) => Ok(()),
        Term::Var(_) | Term::Sort(_) | Term::Meta(_) => Ok(()),
    }
}

/// Enforce that a partial definition returns a Comp A type.
fn enforce_effect_boundary(
    allowed_context: Totality,
    called_totality: Totality,
    name: &str,
) -> Result<(), TypeError> {
    match (allowed_context, called_totality) {
        // Total cannot call Partial or Unsafe
        (Totality::Total | Totality::WellFounded, Totality::Partial) => Err(
            TypeError::EffectError("Total".to_string(), "Partial".to_string(), name.to_string()),
        ),
        (Totality::Total | Totality::WellFounded, Totality::Unsafe) => Err(TypeError::EffectError(
            "Total".to_string(),
            "Unsafe".to_string(),
            name.to_string(),
        )),

        // Partial cannot call Unsafe
        (Totality::Partial, Totality::Unsafe) => Err(TypeError::EffectError(
            "Partial".to_string(),
            "Unsafe".to_string(),
            name.to_string(),
        )),

        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use crate::ownership::DefCaptureModeMap;

    fn add_marker_axioms(env: &mut Env) {
        let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        let markers = [
            "interior_mutable",
            "may_panic_on_borrow_violation",
            "concurrency_primitive",
            "atomic_primitive",
            "indexable",
        ];
        for name in markers {
            env.add_definition(Definition::axiom_with_tags(
                name.to_string(),
                type0.clone(),
                vec![AxiomTag::Unsafe],
            ))
            .expect("Failed to add marker axiom");
        }
        env.set_allow_reserved_primitives(allow_reserved);
        env.init_marker_registry()
            .expect("Failed to init marker registry");
    }

    fn add_nullary_constructor_inductive(env: &mut Env, ind_name: &str, ctor_name: &str) {
        let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let ind = Rc::new(Term::Ind(ind_name.to_string(), vec![]));
        env.add_inductive(InductiveDecl::new_copy(
            ind_name.to_string(),
            type0,
            vec![Constructor {
                name: ctor_name.to_string(),
                ty: ind,
            }],
        ))
        .expect("Failed to add test inductive");
    }

    #[test]
    fn test_effect_boundaries() {
        let mut env = Env::new();
        let sort = Rc::new(Term::Sort(Level::Zero));
        let val = Rc::new(Term::Sort(Level::Zero)); // Dummies

        // Define constants with different totalities
        env.definitions.insert(
            "total_def".to_string(),
            Definition {
                name: "total_def".to_string(),
                ty: sort.clone(),
                value: Some(val.clone()),
                totality: Totality::Total,
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
            },
        );

        env.definitions.insert(
            "partial_def".to_string(),
            Definition {
                name: "partial_def".to_string(),
                ty: sort.clone(),
                value: Some(val.clone()),
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
            },
        );

        env.definitions.insert(
            "unsafe_def".to_string(),
            Definition {
                name: "unsafe_def".to_string(),
                ty: sort.clone(),
                value: Some(val.clone()),
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
            },
        );

        // Test Terms calling these constants
        let call_total = Rc::new(Term::Const("total_def".to_string(), vec![]));
        let call_partial = Rc::new(Term::Const("partial_def".to_string(), vec![]));
        let call_unsafe = Rc::new(Term::Const("unsafe_def".to_string(), vec![]));

        // 1. Total context
        // Can call Total
        assert!(check_effects(&env, Totality::Total, &call_total).is_ok());
        // Cannot call Partial
        match check_effects(&env, Totality::Total, &call_partial) {
            Err(TypeError::EffectError(ctx, called, _)) => {
                assert_eq!(ctx, "Total");
                assert_eq!(called, "Partial");
            }
            _ => panic!("Expected EffectError(Total, Partial)"),
        }
        // Cannot call Unsafe
        match check_effects(&env, Totality::Total, &call_unsafe) {
            Err(TypeError::EffectError(ctx, called, _)) => {
                assert_eq!(ctx, "Total");
                assert_eq!(called, "Unsafe");
            }
            _ => panic!("Expected EffectError(Total, Unsafe)"),
        }

        // 2. Partial context
        // Can call Total
        assert!(check_effects(&env, Totality::Partial, &call_total).is_ok());
        // Can call Partial
        assert!(check_effects(&env, Totality::Partial, &call_partial).is_ok());
        // Cannot call Unsafe
        match check_effects(&env, Totality::Partial, &call_unsafe) {
            Err(TypeError::EffectError(ctx, called, _)) => {
                assert_eq!(ctx, "Partial");
                assert_eq!(called, "Unsafe");
            }
            _ => panic!("Expected EffectError(Partial, Unsafe)"),
        }

        // 3. Unsafe context
        // All ok
        assert!(check_effects(&env, Totality::Unsafe, &call_total).is_ok());
        assert!(check_effects(&env, Totality::Unsafe, &call_partial).is_ok());
        assert!(check_effects(&env, Totality::Unsafe, &call_unsafe).is_ok());
    }

    #[test]
    fn test_implicit_binder_consumes_noncopy_rejected() {
        let mut env = Env::new();
        add_marker_axioms(&mut env);
        let ctx = Context::new();

        let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let lin_ref = Rc::new(Term::Ind("Lin".to_string(), vec![]));

        let lin_decl = InductiveDecl {
            name: "Lin".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: type0.clone(),
            ctors: vec![Constructor {
                name: "mk".to_string(),
                ty: lin_ref.clone(),
            }],
            is_copy: false,
            markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(lin_decl).expect("Failed to add Lin");
        assert!(!is_copy_type_in_env(&env, &lin_ref));

        let implicit_val = Rc::new(Term::Lam(
            lin_ref.clone(),
            Rc::new(Term::Var(0)),
            BinderInfo::Implicit,
            FunctionKind::Fn,
        ));

        let mut usage = UsageContext::new();
        let result =
            check_ownership_in_term(&env, &ctx, &implicit_val, &mut usage, UsageMode::Consuming);

        match result {
            Err(TypeError::OwnershipError(OwnershipError::ImplicitNonCopyUse { var, .. })) => {
                assert_eq!(var.index, 0);
            }
            other => panic!("Expected implicit binder ownership error, got {:?}", other),
        }
    }

    #[test]
    fn test_prop_field_in_data_unfolds_opaque_alias() {
        let mut env = Env::new();
        let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
        let prop = Rc::new(Term::Sort(Level::Zero));

        let mut alias_def = Definition::total("PropAlias".to_string(), type0.clone(), prop.clone());
        alias_def.transparency = Transparency::None;
        env.add_definition(alias_def)
            .expect("Failed to add PropAlias");

        let ctor_ty = Term::pi(
            Rc::new(Term::Const("PropAlias".to_string(), vec![])),
            Term::ind("Box".to_string()),
            BinderInfo::Default,
        );
        let decl = InductiveDecl {
            name: "Box".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: type0.clone(),
            ctors: vec![Constructor {
                name: "mk".to_string(),
                ty: ctor_ty,
            }],
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };

        match env.add_inductive(decl) {
            Err(TypeError::PropFieldInData { ind, ctor, field }) => {
                assert_eq!(ind, "Box");
                assert_eq!(ctor, "mk");
                assert_eq!(field, 0);
            }
            other => panic!("Expected PropFieldInData error, got {:?}", other),
        }
    }

    #[test]
    fn test_wellfounded_unfold_requires_check() {
        let mut env = Env::new();
        let ty = Rc::new(Term::Sort(Level::Zero));
        let body = Rc::new(Term::Lam(
            ty.clone(),
            Term::var(0),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let wf_info = WellFoundedInfo {
            relation: "lt".to_string(),
            decreasing_arg: 0,
        };
        let def = Definition::wellfounded("wf_fn".to_string(), ty.clone(), body, wf_info);
        assert!(!def.wf_checked);
        env.definitions.insert("wf_fn".to_string(), def);

        let term = Rc::new(Term::Const("wf_fn".to_string(), vec![]));
        let val =
            crate::nbe::eval(&term, &vec![], &env, Transparency::All).expect("nbe eval failed");

        match val {
            crate::nbe::Value::Neutral(head, _) => match *head {
                crate::nbe::Neutral::Const(name, _) => assert_eq!(name, "wf_fn"),
                other => panic!("Expected neutral const head, got {:?}", other),
            },
            other => panic!("Expected neutral value, got {:?}", other),
        }
    }

    #[test]
    fn test_axiom_tracking() {
        let mut env = Env::new();
        let prop = Rc::new(Term::Sort(Level::Zero));

        // 1. Declare Axiom "Choice"
        let choice_def = Definition::axiom("Choice".to_string(), prop.clone());
        env.add_definition(choice_def).unwrap();

        // Verify Choice depends on itself
        let stored_choice = env.get_definition("Choice").unwrap();
        assert!(stored_choice.axioms.contains(&"Choice".to_string()));

        // 2. Define Theorem that uses Choice
        // def use_choice := Choice
        let mut use_choice_def = Definition::total(
            "use_choice".to_string(),
            prop.clone(),
            Rc::new(Term::Const("Choice".to_string(), vec![])),
        );
        use_choice_def.noncomputable = true;
        env.add_definition(use_choice_def).unwrap();

        let stored_use = env.get_definition("use_choice").unwrap();
        assert!(stored_use.axioms.contains(&"Choice".to_string()));

        // 3. Define Theorem that does NOT use Choice
        // def no_choice := Prop
        let no_choice_def = Definition::total(
            "no_choice".to_string(),
            Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero)))), // Type 0
            prop.clone(),
        );
        env.add_definition(no_choice_def).unwrap();

        let stored_no = env.get_definition("no_choice").unwrap();
        assert!(stored_no.axioms.is_empty());
    }

    #[test]
    fn test_primitive_deps_do_not_require_noncomputable() {
        let mut env = Env::new();
        env.set_allow_reserved_primitives(true);

        let sort1 = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ty = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let nat_ref = Term::ind("Nat".to_string());

        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: nat_ty.clone(),
            ctors: vec![
                Constructor {
                    name: "zero".to_string(),
                    ty: nat_ref.clone(),
                },
                Constructor {
                    name: "succ".to_string(),
                    ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default),
                },
            ],
            is_copy: true,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(nat_decl).unwrap();

        let shared_ty = sort1.clone();
        env.add_definition(Definition::axiom("Shared".to_string(), shared_ty))
            .unwrap();

        let ref_ty = Term::pi(
            sort1.clone(),
            Term::pi(sort1.clone(), sort1.clone(), BinderInfo::Default),
            BinderInfo::Default,
        );
        env.add_definition(Definition::axiom("Ref".to_string(), ref_ty))
            .unwrap();

        let ref_const = Rc::new(Term::Const("Ref".to_string(), vec![]));
        let shared_const = Rc::new(Term::Const("Shared".to_string(), vec![]));
        let borrow_shared_ty = Term::pi(
            sort1.clone(),
            Term::pi(
                Term::var(0),
                Term::app_with_label(
                    Term::app(ref_const.clone(), shared_const.clone()),
                    Term::var(1),
                    Some("r".to_string()),
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        env.add_definition(Definition::axiom(
            "borrow_shared".to_string(),
            borrow_shared_ty,
        ))
        .unwrap();

        let id_ref_ty = Term::pi(
            nat_ref.clone(),
            Term::app_with_label(
                Term::app(ref_const.clone(), shared_const.clone()),
                nat_ref.clone(),
                Some("r".to_string()),
            ),
            BinderInfo::Default,
        );
        let borrow_shared_const = Rc::new(Term::Const("borrow_shared".to_string(), vec![]));
        let id_ref_val = Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(borrow_shared_const, nat_ref.clone()),
                Term::var(0),
            ),
            BinderInfo::Default,
        );

        let id_ref_def = Definition::total("id_ref".to_string(), id_ref_ty, id_ref_val);
        env.add_definition(id_ref_def)
            .expect("id_ref should typecheck without noncomputable");

        let stored = env.get_definition("id_ref").unwrap();
        assert!(stored.axioms.is_empty());
        assert!(stored.primitive_deps.contains(&"borrow_shared".to_string()));
        assert!(stored.primitive_deps.contains(&"Ref".to_string()));
        assert!(stored.primitive_deps.contains(&"Shared".to_string()));
    }

    #[test]
    fn test_unsafe_axiom_tracking() {
        let mut env = Env::new();
        let prop = Rc::new(Term::Sort(Level::Zero));
        let unsafe_ty = Term::pi(prop.clone(), prop.clone(), BinderInfo::Default);

        let unsafe_axiom = Definition::axiom_with_tags(
            "UnsafeAx".to_string(),
            unsafe_ty.clone(),
            vec![AxiomTag::Unsafe],
        );
        env.add_definition(unsafe_axiom).unwrap();

        let uses_unsafe = Definition::unsafe_def(
            "uses_unsafe".to_string(),
            unsafe_ty.clone(),
            Rc::new(Term::Const("UnsafeAx".to_string(), vec![])),
        );
        env.add_definition(uses_unsafe).unwrap();

        let stored = env.get_definition("uses_unsafe").unwrap();
        assert!(stored.axioms.contains(&"UnsafeAx".to_string()));
        let deps = axiom_dependencies_with_tag(&env, &stored.axioms, AxiomTag::Unsafe);
        assert_eq!(deps, vec!["UnsafeAx".to_string()]);
    }

    #[test]
    fn test_inductive_axiom_tracking() {
        let mut env = Env::new();
        let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

        // Declare a classical axiom used in an inductive constructor.
        let ax_ty = Definition::axiom_classical("AxTy".to_string(), sort1.clone());
        env.add_definition(ax_ty).unwrap();

        let bad_decl = InductiveDecl {
            name: "Bad".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: sort1.clone(),
            ctors: vec![Constructor {
                name: "mk".to_string(),
                ty: Term::pi(
                    Rc::new(Term::Const("AxTy".to_string(), vec![])),
                    Rc::new(Term::Ind("Bad".to_string(), vec![])),
                    BinderInfo::Default,
                ),
            }],
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(bad_decl).unwrap();

        let bad_decl = env.get_inductive("Bad").unwrap().clone();
        assert!(bad_decl.axioms.contains(&"AxTy".to_string()));

        // Definition that only mentions the inductive in its type should inherit axiom deps.
        let bad_ty = Rc::new(Term::Ind("Bad".to_string(), vec![]));
        let uses_bad_ty = Rc::new(Term::Pi(
            bad_ty.clone(),
            bad_ty.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let uses_bad_val = Rc::new(Term::Lam(
            bad_ty.clone(),
            Term::var(0),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let mut uses_bad_def = Definition::total("uses_bad".to_string(), uses_bad_ty, uses_bad_val);
        uses_bad_def.noncomputable = true;
        env.add_definition(uses_bad_def).unwrap();

        let uses_bad = env.get_definition("uses_bad").unwrap();
        assert!(uses_bad.axioms.contains(&"AxTy".to_string()));
        let classical = classical_axiom_dependencies(&env, uses_bad);
        assert_eq!(classical, vec!["AxTy".to_string()]);

        // Recursor usage should also inherit inductive axiom deps. The recursor is applied to
        // its motive and minor premise in place (a bare recursor value is rejected by the
        // ownership check, see `check_ownership_rec_app`):
        //   bad_rec : Π (P : Bad → Prop). Π^FnOnce (m : Π^FnOnce (x : AxTy), P (mk x)).
        //             Π^FnOnce (b : Bad), P b
        //   bad_rec := λ P. λ^FnOnce m. λ^FnOnce b. Rec Bad P m b
        let ax_ty = Rc::new(Term::Const("AxTy".to_string(), vec![]));
        let motive_ty = Term::pi(bad_ty.clone(), Term::sort(Level::Zero), BinderInfo::Default);
        // In context [P]: Π^FnOnce (x : AxTy), P (mk x)
        let minor_ty = Term::pi_with_kind(
            ax_ty,
            Term::app(
                Term::var(1),
                Term::app(
                    Rc::new(Term::Ctor("Bad".to_string(), 0, vec![])),
                    Term::var(0),
                ),
            ),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        );
        // In context [P, m]: Π^FnOnce (b : Bad), P b
        let result_ty = Term::pi_with_kind(
            bad_ty.clone(),
            Term::app(Term::var(2), Term::var(0)),
            BinderInfo::Default,
            FunctionKind::FnOnce,
        );
        let rec_ty = Term::pi(
            motive_ty.clone(),
            Term::pi_with_kind(
                minor_ty.clone(),
                result_ty,
                BinderInfo::Default,
                FunctionKind::FnOnce,
            ),
            BinderInfo::Default,
        );
        let rec_app = Term::app(
            Term::app(
                Term::app(
                    Rc::new(Term::Rec("Bad".to_string(), vec![Level::Zero])),
                    Term::var(2),
                ),
                Term::var(1),
            ),
            Term::var(0),
        );
        let rec_term = Term::lam(
            motive_ty,
            Rc::new(Term::Lam(
                minor_ty,
                Rc::new(Term::Lam(
                    bad_ty.clone(),
                    rec_app,
                    BinderInfo::Default,
                    FunctionKind::FnOnce,
                )),
                BinderInfo::Default,
                FunctionKind::FnOnce,
            )),
            BinderInfo::Default,
        );
        let mut bad_rec_def = Definition::total("bad_rec".to_string(), rec_ty, rec_term);
        bad_rec_def.noncomputable = true;
        env.add_definition(bad_rec_def).unwrap();
        let bad_rec = env.get_definition("bad_rec").unwrap();
        assert!(bad_rec.axioms.contains(&"AxTy".to_string()));
    }

    #[test]
    fn test_axiom_tag_snapshot_stable_against_redefinition() {
        let mut env = Env::new();
        let prop = Rc::new(Term::Sort(Level::Zero));

        env.add_definition(Definition::axiom_classical("Ax".to_string(), prop.clone()))
            .expect("Failed to add Ax");
        let mut use_ax_def = Definition::total(
            "use_ax".to_string(),
            prop.clone(),
            Rc::new(Term::Const("Ax".to_string(), vec![])),
        );
        use_ax_def.noncomputable = true;
        env.add_definition(use_ax_def)
            .expect("Failed to add use_ax");

        let use_ax_axioms = env
            .get_definition("use_ax")
            .expect("Missing use_ax")
            .axioms
            .clone();
        let before = axiom_dependencies_with_tag(&env, &use_ax_axioms, AxiomTag::Classical);
        assert_eq!(before, vec!["Ax".to_string()]);

        // Simulate a redefinition that drops the classical tag without touching the snapshot.
        env.definitions
            .insert("Ax".to_string(), Definition::axiom("Ax".to_string(), prop));

        let after = axiom_dependencies_with_tag(&env, &use_ax_axioms, AxiomTag::Classical);
        assert_eq!(after, vec!["Ax".to_string()]);
    }

    #[test]
    fn test_dependency_fixpoint_propagates_copy_instance() {
        let mut env = Env::new();
        let type0 = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let foo_ref = Term::ind("Foo".to_string());

        let foo_decl = InductiveDecl {
            name: "Foo".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: type0.clone(),
            ctors: vec![Constructor {
                name: "mk".to_string(),
                ty: foo_ref.clone(),
            }],
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(foo_decl).unwrap();

        let leaf = Definition::total(
            "leaf".to_string(),
            foo_ref.clone(),
            Term::ctor("Foo".to_string(), 0),
        );
        env.add_definition(leaf).unwrap();

        let middle = Definition::total(
            "middle".to_string(),
            foo_ref.clone(),
            Rc::new(Term::Const("leaf".to_string(), vec![])),
        );
        env.add_definition(middle).unwrap();

        let top = Definition::total(
            "top".to_string(),
            foo_ref.clone(),
            Rc::new(Term::Const("middle".to_string(), vec![])),
        );
        env.add_definition(top).unwrap();

        let inst = CopyInstance {
            ind_name: "Foo".to_string(),
            param_count: 0,
            requirements: vec![],
            source: CopyInstanceSource::Explicit,
            is_unsafe: true,
        };
        env.add_copy_instance(inst).unwrap();

        let axiom_name = copy_instance_axiom_name("Foo");
        let top_def = env.get_definition("top").unwrap();
        assert!(top_def.axioms.contains(&axiom_name));
    }

    #[test]
    fn test_dependency_ordering_deterministic() {
        let mut env = Env::new();
        let prop = Term::sort(Level::Zero);

        env.add_definition(Definition::axiom("B".to_string(), prop.clone()))
            .unwrap();
        env.add_definition(Definition::axiom("A".to_string(), prop.clone()))
            .unwrap();

        let body = Rc::new(Term::LetE(
            prop.clone(),
            Rc::new(Term::Const("B".to_string(), vec![])),
            Rc::new(Term::Const("A".to_string(), vec![])),
        ));
        let mut def = Definition::total("use_ab".to_string(), prop.clone(), body);
        def.noncomputable = true;
        env.add_definition(def).unwrap();

        let stored = env.get_definition("use_ab").unwrap();
        assert_eq!(stored.axioms, vec!["A".to_string(), "B".to_string()]);
    }

    #[test]
    fn test_constructor_candidates_deterministic_across_decl_order() {
        let mut first = Env::new();
        add_nullary_constructor_inductive(&mut first, "Foo", "mk");
        add_nullary_constructor_inductive(&mut first, "Bar", "mk");

        let mut second = Env::new();
        add_nullary_constructor_inductive(&mut second, "Bar", "mk");
        add_nullary_constructor_inductive(&mut second, "Foo", "mk");

        let first_candidates: Vec<(String, usize)> = first
            .constructor_candidates("mk")
            .iter()
            .map(|candidate| (candidate.ind_name.clone(), candidate.index))
            .collect();
        let second_candidates: Vec<(String, usize)> = second
            .constructor_candidates("mk")
            .iter()
            .map(|candidate| (candidate.ind_name.clone(), candidate.index))
            .collect();

        assert_eq!(
            first_candidates,
            vec![("Bar".to_string(), 0), ("Foo".to_string(), 0)]
        );
        assert_eq!(first_candidates, second_candidates);
    }
}
