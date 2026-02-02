use crate::ast::{Term, Level, InductiveDecl, Constructor, Definition, Totality, BinderInfo, Transparency};
use crate::nbe;
use crate::ownership::{OwnershipError, UsageContext, UsageMode};
use std::collections::{HashMap, HashSet};
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
    #[error("Unknown Const: {0}")]
    UnknownConst(String),
    #[error("Non-strictly positive occurrence of {0} in constructor {1} argument {2}")]
    NonPositiveOccurrence(String, String, usize),
    #[error("Universe level too small: Inductive {0} is {1}, but constructor {2} argument is {3}")]
    UniverseLevelTooSmall(String, String, String, String),
    #[error("Non-terminating recursion in definition {0}: recursive call not on structurally smaller argument")]
    NonTerminating(String),
    #[error("Termination check failed in {def_name}: {details}")]
    TerminationError { def_name: String, details: TerminationErrorDetails },
    #[error("Partial definition {0} used in type context")]
    PartialInType(String),
    #[error("Ownership violation: {0}")]
    OwnershipError(#[from] OwnershipError),
    #[error("Effect violation: {0} definition calls {1} definition {2}")]
    EffectError(String, String, String),
    #[error("Well-founded definition {0} is missing well-foundedness info")]
    MissingWellFoundedInfo(String),
    #[error("Well-founded definition {name} has invalid decreasing argument index {index}")]
    InvalidWellFoundedDecreasingArg { name: String, index: usize },
    #[error("Large elimination from Prop inductive {0} to Type is not allowed")]
    LargeElimination(String),
    #[error("Inductive {ind} constructor {ctor} field {field} is in Prop")]
    PropFieldInData { ind: String, ctor: String, field: usize },
    #[error("Recursor for inductive {0} requires an explicit universe level")]
    MissingRecursorLevel(String),
    #[error("Recursor for inductive {ind} expects {expected} universe levels, got {got}")]
    RecursorLevelCount { ind: String, expected: usize, got: usize },
    #[error("Constructor {ctor} does not return inductive {ind}")]
    CtorNotReturningInductive { ind: String, ctor: String },
    #[error("Constructor {ctor} for inductive {ind} returns {got} arguments, expected {expected}")]
    CtorArityMismatch { ind: String, ctor: String, expected: usize, got: usize },
    #[error("Unresolved metavariable ?{0}")]
    UnresolvedMeta(usize),
    #[error("Definitional equality fuel exhausted")]
    DefEqFuelExhausted,
    #[error("NbE application of non-function value")]
    NbeNonFunctionApplication,
    #[error("Not implemented")]
    NotImplemented,
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
            TerminationErrorDetails::NonSmallerArgument { arg_term, arg_position, smaller_vars } => {
                write!(f, "recursive call at argument position {} is not structurally smaller. ", arg_position)?;
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
                write!(f, "invalid decreasing argument hint at position {}", arg_position)
            }
            TerminationErrorDetails::RecursiveCallInType => {
                write!(f, "recursive call appears in type position")
            }
            TerminationErrorDetails::MutualRecursionError { functions } => {
                write!(f, "mutual recursion between {} does not decrease", functions.join(", "))
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

/// Global environment containing inductive definitions and constants
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Builtin {
    Nat,
    Bool,
    List,
}

#[derive(Clone)]
pub struct Env {
    definitions: HashMap<String, Definition>,
    pub inductives: HashMap<String, InductiveDecl>,
    pub axioms: HashMap<String, Rc<Term>>,
    pub known_inductives: HashMap<Builtin, String>,
}

impl Env {
    pub fn new() -> Self {
        Env {
            definitions: HashMap::new(),
            inductives: HashMap::new(),
            axioms: HashMap::new(),
            known_inductives: HashMap::new(),
        }
    }

    pub fn definitions(&self) -> &HashMap<String, Definition> {
        &self.definitions
    }

    /// Register an inductive type definition
    pub fn add_inductive(&mut self, mut decl: InductiveDecl) -> Result<(), TypeError> {
        if let Some(partial_name) = contains_partial_def(self, &decl.ty) {
            return Err(TypeError::PartialInType(partial_name));
        }
        // Infer parameter count from constructors for consistency with recursors/elimination.
        // If the caller specified params, honor them but don't exceed what constructors support.
        let inferred_params = infer_num_params_from_ctors(&decl)?;
        if decl.num_params == 0 {
            decl.num_params = inferred_params;
        } else if decl.num_params > inferred_params {
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

        if let Err(e) = check_inductive_soundness(self, &decl) {
            match previous {
                Some(prev) => {
                    self.inductives.insert(name.clone(), prev);
                }
                None => {
                    self.inductives.remove(&name);
                }
            }
            return Err(e);
        }
        if decl.name == "Nat" { self.known_inductives.insert(Builtin::Nat, decl.name.clone()); }
        if decl.name == "Bool" { self.known_inductives.insert(Builtin::Bool, decl.name.clone()); }
        if decl.name == "List" { self.known_inductives.insert(Builtin::List, decl.name.clone()); }
        self.inductives.insert(decl.name.clone(), decl);
        Ok(())
    }

    pub fn register_builtin(&mut self, builtin: Builtin, name: String) {
        self.known_inductives.insert(builtin, name);
    }

    pub fn is_builtin(&self, builtin: Builtin, name: &str) -> bool {
        self.known_inductives.get(&builtin).map(|s| s == name).unwrap_or(false)
    }

    /// Register a definition with explicit totality.
    /// Automatically sets `rec_arg` for total definitions based on termination analysis.
    pub fn add_definition(&mut self, mut def: Definition) -> Result<(), TypeError> {
        // Validate core invariants early (no metas, explicit recursor levels, etc.)
        validate_core_term(&def.ty)?;
        if let Some(ref val) = def.value {
            validate_core_term(val)?;
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
            rec_arg: def.rec_arg,
            wf_info: def.wf_info.clone(),
            wf_checked: false,
            transparency: Transparency::None,
            axiom_tags: def.axiom_tags.clone(),
            axioms: def.axioms.clone(),
        };
        let previous = self.definitions.insert(name.clone(), placeholder);

        let result = (|| {
            let ctx = Context::new();

            // Ensure the declared type itself is well-typed and is a Sort.
            let ty_ty = infer(self, &ctx, def.ty.clone())?;
            let ty_ty_norm = whnf_in_ctx(self, &ctx, ty_ty, crate::Transparency::Reducible)?;
            if !matches!(&*ty_ty_norm, Term::Sort(_)) {
                return Err(TypeError::ExpectedSort(ty_ty_norm));
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

            // Check Effect Boundaries (Phase 5)
            if let Some(ref val) = def.value {
                check_effects(self, def.totality, val)?;
            }

        // For Total definitions, verify termination and record decreasing argument
        if def.totality == Totality::Total {
            if let Some(ref val) = def.value {
                // Collect all existing total definitions (with bodies) plus the new definition.
                let mut total_defs: Vec<(String, Rc<Term>, Rc<Term>, Option<usize>)> = self
                    .definitions
                    .iter()
                    .filter_map(|(name, existing)| {
                        if existing.totality == Totality::Total {
                            existing
                                .value
                                .as_ref()
                                .map(|body| {
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
                let def_names: Vec<&str> = total_defs.iter().map(|(n, _, _, _)| n.as_str()).collect();
                let call_graph = build_call_graph(
                    &total_defs
                        .iter()
                        .map(|(n, ty, body, _)| (n.clone(), ty.clone(), body.clone()))
                        .collect::<Vec<_>>(),
                );
                let mutual_groups = find_mutual_groups(&call_graph, &def_names);

                let mut rec_arg = None;
                if let Some(group) = mutual_groups.iter().find(|g| g.contains(&def.name.as_str())) {
                    if group.len() > 1 {
                        let group_defs: Vec<(String, Rc<Term>, Rc<Term>, Option<usize>)> = group
                            .iter()
                            .filter_map(|name| {
                                total_defs
                                    .iter()
                                    .find(|(n, _, _, _)| n == *name)
                                    .cloned()
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
                    rec_arg = check_termination_with_hint(self, &def.name, &def.ty, val, def.rec_arg)?;
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
                while let Term::Pi(dom, cod, _) = &*curr_ty {
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
            match previous {
                Some(prev) => {
                    self.definitions.insert(name, prev);
                }
                None => {
                    self.definitions.remove(&name);
                }
            }
            return Err(e);
        }

        // Compute axiom dependencies
        let mut used_axioms = HashSet::new();
        // Include self-declared axioms
        for ax in &def.axioms {
            used_axioms.insert(ax.clone());
        }
        // Collect from type
        collect_axioms_rec(self, &def.ty, &mut used_axioms);
        // Collect from value
        if let Some(ref val) = def.value {
            collect_axioms_rec(self, val, &mut used_axioms);
        }
        def.axioms = used_axioms.into_iter().collect();
        def.axioms.sort();

        // Also add to legacy defs for backward compatibility
        self.definitions.insert(def.name.clone(), def);
        Ok(())
    }


    /// Get an inductive declaration by name
    pub fn get_inductive(&self, name: &str) -> Option<&InductiveDecl> {
        self.inductives.get(name)
    }



    /// Get a full definition with totality info
    pub fn get_definition(&self, name: &str) -> Option<&Definition> {
        self.definitions.get(name)
    }

    /// Check if a definition can be safely unfolded in type contexts
    pub fn is_type_safe(&self, name: &str) -> bool {
        self.definitions.get(name).map_or(true, |d| d.is_type_safe())
    }
}

// =============================================================================
// Termination Checking - Structural Recursion & Well-Founded Recursion
// =============================================================================

/// Termination context for tracking smaller variables
#[derive(Clone, Debug)]
struct TerminationCtx {
    /// Variables known to be strictly smaller than the decreasing argument
    smaller_vars: Vec<usize>,
    /// The de Bruijn index of the original decreasing argument
    rec_arg_var: usize,
    /// Name of the inductive type being recursed on
    ind_name: String,
    /// Current binding depth
    depth: usize,
}

impl TerminationCtx {
    fn new(rec_arg_var: usize, ind_name: String) -> Self {
        TerminationCtx {
            smaller_vars: Vec::new(),
            rec_arg_var,
            ind_name,
            depth: 0,
        }
    }

    /// Shift context when entering a binder
    fn shift(&self) -> Self {
        TerminationCtx {
            smaller_vars: self.smaller_vars.iter().map(|v| v + 1).collect(),
            rec_arg_var: self.rec_arg_var + 1,
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

    /// Add multiple smaller variables with shifting
    fn add_smaller_range(&self, start: usize, count: usize) -> Self {
        let mut ctx = self.clone();
        for i in 0..count {
            ctx.smaller_vars.push(start + i);
        }
        ctx
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
/// Check termination for a definition.
/// Returns Ok(Some(idx)) if structurally recursive on argument `idx`,
/// Ok(None) if non-recursive or no decreasing argument needed.
fn select_rec_arg(
    env: &Env,
    def_name: &str,
    param_types: &[Rc<Term>],
    rec_arg_hint: Option<usize>,
) -> Result<Option<(usize, String)>, TypeError> {
    if let Some(idx) = rec_arg_hint {
        if idx >= param_types.len() {
            return Err(TypeError::TerminationError {
                def_name: def_name.to_string(),
                details: TerminationErrorDetails::InvalidDecreasingArgument { arg_position: idx },
            });
        }
        if let Some(ind_name) = get_inductive_name(env, &param_types[idx]) {
            return Ok(Some((idx, ind_name)));
        }
        return Err(TypeError::TerminationError {
            def_name: def_name.to_string(),
            details: TerminationErrorDetails::InvalidDecreasingArgument { arg_position: idx },
        });
    }

    for (i, param_ty) in param_types.iter().enumerate() {
        if let Some(ind_name) = get_inductive_name(env, param_ty) {
            return Ok(Some((i, ind_name)));
        }
    }

    Ok(None)
}

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
    // Step 1: Find the decreasing argument candidate
    let mut param_types = Vec::new();
    let mut curr_ty = ty.clone();
    while let Term::Pi(dom, cod, _) = &*curr_ty {
        param_types.push(dom.clone());
        curr_ty = cod.clone();
    }

    let rec_arg_info = select_rec_arg(env, def_name, &param_types, rec_arg_hint)?;

    // If no inductive parameter, allow if no recursive calls
    let (rec_arg, ind_name) = match rec_arg_info {
        Some((idx, name)) => (idx, name),
        None => {
            if contains_recursive_call(body, def_name, 0) {
                return Err(TypeError::TerminationError {
                    def_name: def_name.to_string(),
                    details: TerminationErrorDetails::NoDecreasingArgument,
                });
            }
            // Non-recursive, no decreasing argument needed
            return Ok(None);
        }
    };

    // Step 2: Extract the body under lambdas
    let num_params = param_types.len();
    let inner_body = peel_lambdas(body, num_params);

    // Step 3: Initialize termination context
    // The decreasing argument is at de Bruijn index (num_params - 1 - rec_arg)
    let rec_arg_var = num_params - 1 - rec_arg;
    let ctx = TerminationCtx::new(rec_arg_var, ind_name);

    // Step 4: Check recursive calls
    check_recursive_calls_ctx(env, def_name, &inner_body, &ctx)?;

    // Return the decreasing argument index if:
    // 1. There are direct recursive calls (self-reference), OR
    // 2. The function uses a recursor (which encodes structural recursion)
    if contains_recursive_call(body, def_name, 0) || contains_recursor_usage(body, &ctx.ind_name) {
        Ok(Some(rec_arg))
    } else {
        Ok(None)
    }
}

/// Check termination for a group of mutually recursive definitions.
/// Returns a Vec of (name, rec_arg) pairs for each definition.
///
/// For mutual recursion to be valid:
/// 1. All functions must decrease on the same argument position, OR
/// 2. There must be a lexicographic ordering where at least one function decreases
pub fn check_mutual_termination(
    env: &Env,
    defs: &[(String, Rc<Term>, Rc<Term>)], // (name, type, body)
) -> Result<Vec<(String, Option<usize>)>, TypeError> {
    let defs_with_hints: Vec<(String, Rc<Term>, Rc<Term>, Option<usize>)> = defs
        .iter()
        .map(|(name, ty, body)| (name.clone(), ty.clone(), body.clone(), None))
        .collect();
    check_mutual_termination_with_hints(env, &defs_with_hints)
}

fn check_mutual_termination_with_hints(
    env: &Env,
    defs: &[(String, Rc<Term>, Rc<Term>, Option<usize>)], // (name, type, body, rec_arg_hint)
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
            // Mutual recursion - need common decreasing measure
            let group_defs: Vec<_> = group
                .iter()
                .filter_map(|name| defs.iter().find(|(n, _, _, _)| n == *name))
                .collect();

            // Find decreasing arguments for each function in the group
            let mut group_rec_args = Vec::new();
            for (def_name, ty, _body, rec_arg_hint) in &group_defs {
                // Find the first inductive argument position
                let mut param_types = Vec::new();
                let mut curr_ty = (*ty).clone();
                while let Term::Pi(dom, cod, _) = &*curr_ty {
                    param_types.push(dom.clone());
                    curr_ty = cod.clone();
                }

                let rec_arg_info = select_rec_arg(env, def_name, &param_types, *rec_arg_hint)?;

                group_rec_args.push((def_name.as_str(), rec_arg_info));
            }

            // Check that all functions in the group have compatible decreasing arguments
            // For now, require they all decrease on the same position and same inductive type
            let first_rec_arg = group_rec_args.iter().find_map(|(_, info)| info.clone());

            let all_compatible = group_rec_args.iter().all(|(_, info)| {
                match (&first_rec_arg, info) {
                    (Some((pos1, ind1)), Some((pos2, ind2))) => pos1 == pos2 && ind1 == ind2,
                    (None, None) => true,
                    _ => false,
                }
            });

            if !all_compatible {
                return Err(TypeError::TerminationError {
                    def_name: group.join(", "),
                    details: TerminationErrorDetails::MutualRecursionError {
                        functions: group.iter().map(|s| s.to_string()).collect(),
                    },
                });
            }

            // Now check each function in the mutual group
            for (def_name, ty, body, rec_arg_hint) in &group_defs {
                // Check termination with awareness of mutual calls
                let rec_arg = check_termination_mutual(env, def_name, ty, body, &def_names, *rec_arg_hint)?;
                results.push((def_name.to_string(), rec_arg));
            }
        }
    }

    Ok(results)
}

/// Build a call graph from definitions
/// Returns a map from function name to set of called function names
fn build_call_graph(defs: &[(String, Rc<Term>, Rc<Term>)]) -> HashMap<String, Vec<String>> {
    let def_names: Vec<&str> = defs.iter().map(|(n, _, _)| n.as_str()).collect();
    let mut graph = HashMap::new();

    for (name, _, body) in defs {
        let mut calls = Vec::new();
        for other_name in &def_names {
            if contains_recursive_call(body, other_name, 0) {
                calls.push(other_name.to_string());
            }
        }
        graph.insert(name.clone(), calls);
    }

    graph
}

/// Find groups of mutually recursive functions
/// Returns a list of groups, where each group contains function names that call each other
fn find_mutual_groups<'a>(
    call_graph: &HashMap<String, Vec<String>>,
    def_names: &[&'a str],
) -> Vec<Vec<&'a str>> {
    // Simple algorithm: group functions that have cycles between them
    // For a more sophisticated approach, use Tarjan's SCC algorithm

    let mut visited = std::collections::HashSet::new();
    let mut groups = Vec::new();

    for &name in def_names {
        if visited.contains(name) {
            continue;
        }

        // Find all functions reachable from this one that can reach back
        let mut group = Vec::new();
        let mut to_check = vec![name];
        let mut reachable = std::collections::HashSet::new();

        // Find all reachable functions
        while let Some(curr) = to_check.pop() {
            if reachable.contains(curr) {
                continue;
            }
            reachable.insert(curr);
            if let Some(calls) = call_graph.get(curr) {
                for called in calls {
                    if def_names.contains(&called.as_str()) && !reachable.contains(called.as_str()) {
                        to_check.push(def_names.iter().find(|&&n| n == called).unwrap());
                    }
                }
            }
        }

        // Check which reachable functions can reach back to the start
        for &reached in &reachable {
            let can_reach_back = can_reach(call_graph, reached, name, def_names);
            if can_reach_back || reached == name {
                group.push(reached);
                visited.insert(reached);
            }
        }

        if !group.is_empty() {
            groups.push(group);
        }
    }

    groups
}

/// Check if src can reach dst in the call graph
fn can_reach(
    call_graph: &HashMap<String, Vec<String>>,
    src: &str,
    dst: &str,
    def_names: &[&str],
) -> bool {
    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![src];

    while let Some(curr) = stack.pop() {
        if curr == dst && curr != src {
            return true;
        }
        if visited.contains(curr) {
            continue;
        }
        visited.insert(curr);

        if let Some(calls) = call_graph.get(curr) {
            for called in calls {
                if def_names.contains(&called.as_str()) {
                    stack.push(called.as_str());
                }
            }
        }
    }

    false
}

/// Check termination for a function in a mutual recursion group
fn check_termination_mutual(
    env: &Env,
    def_name: &str,
    ty: &Rc<Term>,
    body: &Rc<Term>,
    mutual_names: &[&str],
    rec_arg_hint: Option<usize>,
) -> Result<Option<usize>, TypeError> {
    // Similar to check_termination but considers calls to any function in the mutual group
    let mut param_types = Vec::new();
    let mut curr_ty = ty.clone();
    while let Term::Pi(dom, cod, _) = &*curr_ty {
        param_types.push(dom.clone());
        curr_ty = cod.clone();
    }

    // Find first inductive parameter
    let rec_arg_info = select_rec_arg(env, def_name, &param_types, rec_arg_hint)?;

    let (rec_arg, ind_name) = match rec_arg_info {
        Some((idx, name)) => (idx, name),
        None => {
            // Check if any mutual function is called
            let has_mutual_call = mutual_names.iter()
                .any(|name| contains_recursive_call(body, name, 0));
            if has_mutual_call {
                return Err(TypeError::TerminationError {
                    def_name: def_name.to_string(),
                    details: TerminationErrorDetails::NoDecreasingArgument,
                });
            }
            return Ok(None);
        }
    };

    let num_params = param_types.len();
    let inner_body = peel_lambdas(body, num_params);
    let rec_arg_var = num_params - 1 - rec_arg;
    let ctx = TerminationCtx::new(rec_arg_var, ind_name.clone());

    // Check recursive calls to any function in the mutual group
    check_mutual_recursive_calls(env, def_name, mutual_names, &inner_body, &ctx)?;

    // Check if there are any calls to mutual functions or recursors
    let has_calls = mutual_names.iter()
        .any(|name| contains_recursive_call(body, name, 0))
        || contains_recursor_usage(body, &ind_name);

    if has_calls {
        Ok(Some(rec_arg))
    } else {
        Ok(None)
    }
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
            // Reference to a mutual function - OK if not applied
            Ok(())
        }
        Term::App(_, _) => {
            // Check if this is a recursor application
            if let Some((ind_name, rec_args)) = extract_rec_app(t) {
                return check_rec_app(env, def_name, &ind_name, &rec_args, ctx);
            }

            // Check if this is a call to any mutual function
            for mutual_name in mutual_names {
                if let Some(args) = extract_app_to_const(t, mutual_name) {
                    // Verify the recursive argument is smaller
                    if ctx.rec_arg_var < args.len() {
                        let rec_arg_term = &args[ctx.rec_arg_var];
                        if !is_smaller(rec_arg_term, ctx) {
                            return Err(TypeError::TerminationError {
                                def_name: def_name.to_string(),
                                details: TerminationErrorDetails::NonSmallerArgument {
                                    arg_term: rec_arg_term.clone(),
                                    arg_position: ctx.rec_arg_var,
                                    smaller_vars: ctx.smaller_vars.clone(),
                                },
                            });
                        }
                    }
                    // Check args recursively
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
                check_mutual_recursive_calls(env, def_name, mutual_names, arg, ctx)?;
            }
            Ok(())
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) | Term::Fix(ty, body) => {
            check_mutual_recursive_calls(env, def_name, mutual_names, ty, ctx)?;
            let body_ctx = ctx.shift();
            check_mutual_recursive_calls(env, def_name, mutual_names, body, &body_ctx)
        }
        Term::LetE(ty, val, body) => {
            check_mutual_recursive_calls(env, def_name, mutual_names, ty, ctx)?;
            check_mutual_recursive_calls(env, def_name, mutual_names, val, ctx)?;
            let body_ctx = ctx.shift();
            check_mutual_recursive_calls(env, def_name, mutual_names, body, &body_ctx)
        }
        _ => Ok(()),
    }
}

/// Collect an application spine: f a1 a2 ... an -> (f, [a1, a2, ..., an])
fn collect_app_spine(t: &Rc<Term>) -> (Rc<Term>, Vec<Rc<Term>>) {
    let mut args = Vec::new();
    let mut curr = t.clone();
    while let Term::App(f, a) = &*curr {
        args.push(a.clone());
        curr = f.clone();
    }
    args.reverse();
    (curr, args)
}

/// Get the inductive type name if a type is inductive (possibly applied)
fn get_inductive_name(env: &Env, ty: &Rc<Term>) -> Option<String> {
    let head = get_head(ty);
    match &*head {
        Term::Ind(name, _) if env.get_inductive(name).is_some() => Some(name.clone()),
        _ => None,
    }
}

/// Check if a type is an inductive type (possibly applied to arguments)
fn is_inductive_type(env: &Env, ty: &Rc<Term>) -> bool {
    get_inductive_name(env, ty).is_some()
}

/// Get the head of an application chain
fn get_head(t: &Rc<Term>) -> Rc<Term> {
    match &**t {
        Term::App(f, _) => get_head(f),
        _ => t.clone(),
    }
}

/// Peel n lambdas from a term, returning the body
fn peel_lambdas(t: &Rc<Term>, n: usize) -> Rc<Term> {
    if n == 0 {
        return t.clone();
    }
    match &**t {
        Term::Lam(_, body, _) => peel_lambdas(body, n - 1),
        _ => t.clone(),
    }
}

/// Check if a term contains a recursive call to the given definition
fn contains_recursive_call(t: &Rc<Term>, def_name: &str, depth: usize) -> bool {
    match &**t {
        Term::Const(name, _) if name == def_name => true,
        Term::App(f, a) => {
            contains_recursive_call(f, def_name, depth)
                || contains_recursive_call(a, def_name, depth)
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => {
            contains_recursive_call(ty, def_name, depth)
                || contains_recursive_call(body, def_name, depth + 1)
        }
        Term::Fix(ty, body) => {
            contains_recursive_call(ty, def_name, depth)
                || contains_recursive_call(body, def_name, depth + 1)
        }
        Term::LetE(ty, val, body) => {
            contains_recursive_call(ty, def_name, depth)
                || contains_recursive_call(val, def_name, depth)
                || contains_recursive_call(body, def_name, depth + 1)
        }
        Term::Meta(_) => false,
        _ => false,
    }
}

/// Check if a term contains a recursor usage for the given inductive type.
/// This indicates structural recursion via the recursor primitive.
fn contains_recursor_usage(t: &Rc<Term>, ind_name: &str) -> bool {
    match &**t {
        Term::Rec(name, _) if name == ind_name => true,
        Term::App(f, a) => {
            contains_recursor_usage(f, ind_name) || contains_recursor_usage(a, ind_name)
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) | Term::Fix(ty, body) => {
            contains_recursor_usage(ty, ind_name) || contains_recursor_usage(body, ind_name)
        }
        Term::LetE(ty, val, body) => {
            contains_recursor_usage(ty, ind_name)
                || contains_recursor_usage(val, ind_name)
                || contains_recursor_usage(body, ind_name)
        }
        Term::Meta(_) => false,
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
        Term::Const(name, _) if name == def_name => {
            // Bare reference - OK (checked when applied)
            Ok(())
        }
        Term::App(_, _) => {
            // Check if this is an application of the recursor
            if let Some((ind_name, rec_args)) = extract_rec_app(t) {
                return check_rec_app(env, def_name, &ind_name, &rec_args, ctx);
            }

            // Check if this is a recursive call
            if let Some(args) = extract_app_to_const(t, def_name) {
                // Verify the recursive argument is smaller
                if ctx.rec_arg_var < args.len() {
                    let rec_arg_term = &args[ctx.rec_arg_var];
                    if !is_smaller(rec_arg_term, ctx) {
                        return Err(TypeError::TerminationError {
                            def_name: def_name.to_string(),
                            details: TerminationErrorDetails::NonSmallerArgument {
                                arg_term: rec_arg_term.clone(),
                                arg_position: ctx.rec_arg_var,
                                smaller_vars: ctx.smaller_vars.clone(),
                            },
                        });
                    }
                }
                // Check arguments for nested recursive calls
                for arg in &args {
                    check_recursive_calls_ctx(env, def_name, arg, ctx)?;
                }
                Ok(())
            } else {
                // Not a recursive call, check subterms
                let (f, a) = match &**t {
                    Term::App(f, a) => (f, a),
                    _ => unreachable!(),
                };
                check_recursive_calls_ctx(env, def_name, f, ctx)?;
                check_recursive_calls_ctx(env, def_name, a, ctx)
            }
        }
        Term::Lam(ty, body, _) => {
            check_recursive_calls_ctx(env, def_name, ty, ctx)?;
            check_recursive_calls_ctx(env, def_name, body, &ctx.shift())
        }
        Term::Pi(dom, cod, _) => {
            check_recursive_calls_ctx(env, def_name, dom, ctx)?;
            check_recursive_calls_ctx(env, def_name, cod, &ctx.shift())
        }
        Term::Fix(ty, body) => {
            check_recursive_calls_ctx(env, def_name, ty, ctx)?;
            check_recursive_calls_ctx(env, def_name, body, &ctx.shift())
        }
        Term::LetE(ty, val, body) => {
            check_recursive_calls_ctx(env, def_name, ty, ctx)?;
            check_recursive_calls_ctx(env, def_name, val, ctx)?;
            // If val is a smaller variable, body's bound var is also smaller
            let body_ctx = if is_smaller(val, ctx) {
                ctx.shift().add_smaller(0)
            } else {
                ctx.shift()
            };
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

    while let Term::App(f, a) = &*curr {
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

/// Check a recursor application for termination
/// Rec applications are inherently terminating because the recursor
/// encodes structural recursion - minor premises receive strictly smaller arguments
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

    // Check each minor premise
    for i in minor_start..minor_end.min(args.len()) {
        let minor = &args[i];
        // Minor premises bind constructor arguments and IH arguments
        // The IH arguments are automatically smaller
        check_minor_premise(env, def_name, decl, i - minor_start, minor, ctx)?;
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

/// Check a minor premise of a recursor
fn check_minor_premise(
    env: &Env,
    def_name: &str,
    decl: &InductiveDecl,
    ctor_idx: usize,
    minor: &Rc<Term>,
    ctx: &TerminationCtx,
) -> Result<(), TypeError> {
    // Count the arguments this minor premise binds
    let ctor = match decl.ctors.get(ctor_idx) {
        Some(c) => c,
        None => return Ok(()),
    };

    // Count constructor fields (pi binders in constructor type after params)
    let mut num_fields = 0;
    let mut num_rec_fields = 0;
    let mut curr = &ctor.ty;

    // Skip params
    for _ in 0..decl.num_params {
        if let Term::Pi(_, body, _) = &**curr {
            curr = body;
        }
    }

    // Count remaining fields
    while let Term::Pi(dom, body, _) = &**curr {
        num_fields += 1;
        // Check if this is a recursive field
        if is_recursive_field(dom, &decl.name) {
            num_rec_fields += 1;
        }
        curr = body;
    }

    // Minor premise binds: field args + IH args
    let total_bindings = num_fields + num_rec_fields;

    // Peel lambdas and check the body
    let body = peel_lambdas(minor, total_bindings);

    // Create context where IH variables are smaller
    // IH variables are at positions after the field variables
    let mut new_ctx = ctx.clone();
    for _ in 0..total_bindings {
        new_ctx = new_ctx.shift();
    }
    // The IH variables (last num_rec_fields bindings before the body) are smaller
    new_ctx = new_ctx.add_smaller_range(0, num_rec_fields);

    check_recursive_calls_ctx(env, def_name, &body, &new_ctx)
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

    while let Term::App(f, a) = &*curr {
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

/// Check if a term is "smaller" than the original recursive argument
fn is_smaller(t: &Rc<Term>, ctx: &TerminationCtx) -> bool {
    match &**t {
        Term::Var(v) => ctx.smaller_vars.contains(v),
        // Applications of projections from smaller things are also smaller
        Term::App(_, _) => {
            if let Some(args) = extract_app_to_const(t, "proj") {
                // proj applications from smaller things
                args.first().map_or(false, |arg| is_smaller(arg, ctx))
            } else {
                false
            }
        }
        Term::Meta(_) => false,
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
    NoAccessibilityProof {
        value: Rc<Term>,
    },
    /// The relation is not defined
    UndefinedRelation(String),
    /// Acc type is not in the environment
    AccTypeNotFound,
    /// Well-founded definition is missing an Acc proof parameter
    MissingAccParameter {
        relation: String,
    },
    /// Recursive call uses an Acc proof that does not match the decreasing argument
    MismatchedAccTarget {
        expected: Rc<Term>,
        actual: Rc<Term>,
    },
}

impl std::fmt::Display for WellFoundedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WellFoundedError::InvalidAccProof { expected_type, actual_type } => {
                write!(f, "invalid accessibility proof: expected {}, got {}", expected_type, actual_type)
            }
            WellFoundedError::NoAccessibilityProof { value } => {
                write!(f, "recursive call on {:?} without accessibility proof", value)
            }
            WellFoundedError::UndefinedRelation(name) => {
                write!(f, "undefined well-founded relation: {}", name)
            }
            WellFoundedError::AccTypeNotFound => {
                write!(f, "Acc type not found in environment (required for well-founded recursion)")
            }
            WellFoundedError::MissingAccParameter { relation } => {
                write!(f, "missing Acc proof parameter for relation {}", relation)
            }
            WellFoundedError::MismatchedAccTarget { expected, actual } => {
                write!(f, "recursive call uses Acc proof for {:?}, but decreasing argument is {:?}", expected, actual)
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

    // 1. Acc must exist in the environment.
    let acc_decl = env
        .get_inductive("Acc")
        .ok_or_else(|| wf_error(def_name, WellFoundedError::AccTypeNotFound))?;

    // 2. Relation must exist.
    if env.get_definition(&spec.relation).is_none()
        && env.get_inductive(&spec.relation).is_none()
    {
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
    while let Term::Pi(dom, cod, _) = &*curr_ty {
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
    check_wellfounded_calls(env, def_name, &inner_body, &wf_ctx, acc_decl)?;
    Ok(())
}

/// Check if a type represents a well-foundedness proof: forall x : T, Acc R x
fn is_wellfoundedness_proof_type(ty: &Rc<Term>, relation: &str, value_type: &Rc<Term>) -> bool {
    // Expected structure: Pi (x : T) (Acc R x)
    if let Term::Pi(dom, body, _) = &**ty {
        if &**dom != &**value_type {
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
            return Some(args[0].clone());
        }
    }
    None
}

/// Check that recursive calls in a well-founded recursive function are valid
fn check_wellfounded_calls(
    env: &Env,
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
        Term::App(_, _) => {
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
                        check_wellfounded_calls(env, def_name, arg, ctx, acc_decl)?;
                    }

                    // Minor premises (Acc.rec body)
                    for arg in args.iter().skip(minors_start).take(num_ctors) {
                        let minor_ctx = ctx.enter_acc_rec();
                        check_wellfounded_calls(env, def_name, arg, &minor_ctx, acc_decl)?;
                    }

                    // Indices + major (and any extra args, if over-applied)
                    for arg in args.iter().skip(minors_end) {
                        check_wellfounded_calls(env, def_name, arg, ctx, acc_decl)?;
                    }

                    return Ok(());
                }

                for arg in &args {
                    check_wellfounded_calls(env, def_name, arg, ctx, acc_decl)?;
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
                let target = acc_proof_target_from_term(acc_arg, ctx)
                    .ok_or_else(|| wf_error(WellFoundedError::NoAccessibilityProof {
                        value: acc_arg.clone(),
                    }))?;

                if &**dec_arg != &*target {
                    return Err(wf_error(WellFoundedError::MismatchedAccTarget {
                        expected: target,
                        actual: dec_arg.clone(),
                    }));
                }

                for arg in &args {
                    check_wellfounded_calls(env, def_name, arg, ctx, acc_decl)?;
                }
                return Ok(());
            }

            // Regular application - check both parts
            let (f, args) = collect_app_spine(t);
            check_wellfounded_calls(env, def_name, &f, ctx, acc_decl)?;
            for arg in &args {
                check_wellfounded_calls(env, def_name, arg, ctx, acc_decl)?;
            }
            Ok(())
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) | Term::Fix(ty, body) => {
            check_wellfounded_calls(env, def_name, ty, ctx, acc_decl)?;
            let mut next_ctx = ctx.shift();
            if ctx.in_acc_rec() {
                if is_acc_fn_type(ty, &ctx.relation) {
                    next_ctx = next_ctx.add_acc_fn(0);
                }
                if let Some(target) = acc_type_target(ty, &ctx.relation) {
                    next_ctx = next_ctx.add_acc_proof(0, target.shift(0, 1));
                }
            }
            check_wellfounded_calls(env, def_name, body, &next_ctx, acc_decl)
        }
        Term::LetE(ty, val, body) => {
            check_wellfounded_calls(env, def_name, ty, ctx, acc_decl)?;
            check_wellfounded_calls(env, def_name, val, ctx, acc_decl)?;
            let mut next_ctx = ctx.shift();
            if ctx.in_acc_rec() {
                if let Some(target) = acc_proof_target_from_term(val, ctx) {
                    next_ctx = next_ctx.add_acc_proof(0, target.shift(0, 1));
                }
            }
            check_wellfounded_calls(env, def_name, body, &next_ctx, acc_decl)
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

fn level_leq(left: &Level, right: &Level) -> bool {
    let left_norm = reduce_level(left.clone());
    let right_norm = reduce_level(right.clone());

    if left_norm == right_norm {
        return true;
    }

    match &left_norm {
        Level::Zero => return true,
        Level::Max(a, b) => {
            return level_leq(a, &right_norm) && level_leq(b, &right_norm);
        }
        _ => {}
    }

    match &right_norm {
        Level::Max(a, b) => {
            return level_leq(&left_norm, a) || level_leq(&left_norm, b);
        }
        Level::Succ(b) => {
            return level_leq(&left_norm, b);
        }
        _ => {}
    }

    match (&left_norm, &right_norm) {
        (Level::Succ(a), Level::Succ(b)) => level_leq(a, b),
        _ => false,
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
        minor_types.push(compute_minor_premise_type(&decl.name, ctor_idx, ctor, num_ctors, num_params));
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
    for (ty, info) in index_binders.iter().rev() {
         // Ty refers to Params (outer) and previous Indices.
         // Previous Indices are valid.
         // Params need shifting?
         // In `decl.ty`, params are outside.
         // In Rec, params are outside Minors/Motive.
         // When checking `ty` of Index k, context is [Params] [PreviousIndices].
         // Here context is [Params] [Motive] [Minors] [PreviousIndices].
         // So we shift Params references by (Motive + Minors).
         // Shift amount = 1 + minors.len().
         result_body = Term::pi(ty.shift(0, 1 + minor_types.len()), result_body, *info);
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
            Term::Pi(ty, body, info) => {
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

/// Compute the type of a minor premise for a constructor.
/// This handles constructors with arbitrary arguments and recursive arguments.
///
/// For a constructor `ctor : (x1 : A1) -> ... -> (xn : An) -> Ind`:
/// The minor premise is:
/// `(x1 : A1) -> ... -> (xn : An) -> (ih_j : Cxj)* -> C (ctor x1 ... xn)`
/// where `ih_j` are induction hypotheses for recursive arguments.
fn compute_minor_premise_type(ind_name: &str, ctor_idx: usize, ctor: &Constructor, _num_ctors: usize, num_params: usize) -> Rc<Term> {
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
        if let Term::Pi(_, body, _) = &*instantiated_ty {
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
    let result_indices = extract_inductive_indices(&ctor_result, ind_name, num_params)
        .unwrap_or_else(|| Vec::new());

    struct Binder {
        ty: Rc<Term>,
        info: BinderInfo,
        is_arg_idx: Option<usize>,
    }

    let mut binders: Vec<Binder> = Vec::new();
    let mut ih_count = 0usize;

    for (arg_idx, (arg_ty, arg_info)) in ctor_args.iter().enumerate() {
        let shifted_arg_ty = arg_ty.shift(0, ih_count);
        binders.push(Binder {
            ty: shifted_arg_ty,
            info: *arg_info,
            is_arg_idx: Some(arg_idx),
        });

        if let Some(rec_indices) = extract_inductive_indices(arg_ty, ind_name, num_params) {
            let c_idx = binders.len() + ctor_idx;
            let mut ih_ty = Term::var(c_idx);
            for idx_term in rec_indices.iter() {
                let shifted_idx = idx_term.shift(0, ih_count + 1);
                ih_ty = Term::app(ih_ty, shifted_idx);
            }
            ih_ty = Term::app(ih_ty, Term::var(0));

            binders.push(Binder {
                ty: ih_ty,
                info: *arg_info,
                is_arg_idx: None,
            });
            ih_count += 1;
        }
    }

    // 3. Build result: C indices... (ctor parameters... args...)
    let total_depth = binders.len();
    let c_idx_final = total_depth + ctor_idx;

    let mut result_ty = Term::var(c_idx_final);
    for idx_term in result_indices.iter() {
        let shifted_idx = idx_term.shift(0, ih_count);
        result_ty = Term::app(result_ty, shifted_idx);
    }

    let ctor_term = Rc::new(Term::Ctor(ind_name.to_string(), ctor_idx, vec![]));
    let mut app_term = ctor_term;

    for i in 0..num_params {
        let param_var_idx = c_idx_final + 1 + (num_params - 1 - i);
        app_term = Term::app(app_term, Term::var(param_var_idx));
    }

    for arg_idx in 0..ctor_args.len() {
        let mut depth_from_end = 0;
        let mut found_depth = 0;
        for b in binders.iter().rev() {
            if b.is_arg_idx == Some(arg_idx) {
                found_depth = depth_from_end;
                break;
            }
            depth_from_end += 1;
        }
        app_term = Term::app(app_term, Term::var(found_depth));
    }

    result_ty = Term::app(result_ty, app_term);

    let mut final_term = result_ty;
    for binder in binders.iter().rev() {
        final_term = Term::pi(binder.ty.clone(), final_term, binder.info);
    }

    final_term
}

fn peel_pi_binders(ty: &Rc<Term>) -> (Vec<(Rc<Term>, BinderInfo)>, Rc<Term>) {
    let mut binders = Vec::new();
    let mut current = ty.clone();
    loop {
        match &*current {
            Term::Pi(dom, body, info) => {
                binders.push((dom.clone(), *info));
                current = body.clone();
            }
            _ => break,
        }
    }
    (binders, current)
}

fn extract_inductive_args(term: &Rc<Term>, ind_name: &str) -> Option<Vec<Rc<Term>>> {
    fn go(t: &Rc<Term>, acc: &mut Vec<Rc<Term>>) -> Option<String> {
        match &**t {
            Term::App(f, a) => {
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

fn extract_inductive_indices(term: &Rc<Term>, ind_name: &str, num_params: usize) -> Option<Vec<Rc<Term>>> {
    let args = extract_inductive_args(term, ind_name)?;
    if args.len() < num_params {
        return None;
    }
    Some(args[num_params..].to_vec())
}

fn extract_ctor_args(ty: &Rc<Term>, ind_name: &str) -> Vec<(Option<String>, Rc<Term>, bool)> {
    let mut current = ty.clone();
    let mut args = Vec::new();
    
    loop {
        match &*current {
            Term::Pi(arg_ty, body, _) => {
                // Check if arg type is the inductive type (possibly applied)
                let is_rec = {
                    let mut t = arg_ty.clone();
                    loop {
                         match &*t {
                             Term::Ind(name, _) if name == ind_name => break true,
                             Term::App(f, _) => t = f.clone(),
                             _ => break false,
                         }
                    }
                };
                
                args.push((None, arg_ty.clone(), is_rec));
                current = body.clone();
            }
            _ => break,
        }
    }
    args
}

fn count_pi_binders(ty: &Rc<Term>) -> usize {
    let mut count = 0;
    let mut current = ty.clone();
    while let Term::Pi(_, body, _) = &*current {
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
    while let Term::Pi(_, body, _) = &*current {
        binder_count += 1;
        current = body.clone();
    }

    let (head, args) = collect_app_spine(&current);
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
        let (binder_count, args) = ctor_return_inductive_args(
            &decl.name,
            &ctor.name,
            &ctor.ty,
            total_binders,
        )?;

        let max = std::cmp::min(binder_count, args.len());
        let mut prefix = 0;
        for i in 0..max {
            match &*args[i] {
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
        nbe::NbeError::FuelExhausted => TypeError::DefEqFuelExhausted,
        nbe::NbeError::NonFunctionApplication => TypeError::NbeNonFunctionApplication,
    }
}

/// Weak Head Normal Form reduction (via NbE)
pub fn whnf(
    env: &Env,
    t: Rc<Term>,
    transparency: crate::Transparency,
) -> Result<Rc<Term>, TypeError> {
    let fuel = nbe::default_eval_fuel();
    let val = nbe::eval_with_fuel(&t, &vec![], env, transparency, fuel)
        .map_err(map_nbe_error)?;
    nbe::quote_with_fuel(val, 0, env, transparency, fuel).map_err(map_nbe_error)
}

fn eval_env_from_ctx(ctx: &Context) -> Vec<crate::nbe::Value> {
    let mut eval_env = Vec::with_capacity(ctx.len());
    for level in 0..ctx.len() {
        eval_env.push(crate::nbe::Value::var(level));
    }
    eval_env
}

pub fn whnf_in_ctx(
    env: &Env,
    ctx: &Context,
    t: Rc<Term>,
    transparency: crate::Transparency,
) -> Result<Rc<Term>, TypeError> {
    let eval_env = eval_env_from_ctx(ctx);
    let fuel = nbe::default_eval_fuel();
    let val = nbe::eval_with_fuel(&t, &eval_env, env, transparency, fuel)
        .map_err(map_nbe_error)?;
    nbe::quote_with_fuel(val, eval_env.len(), env, transparency, fuel).map_err(map_nbe_error)
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
    nbe::is_def_eq_result(t1, t2, env, transparency, fuel).map_err(map_nbe_error)
}

pub fn is_def_eq_with_fuel(
    env: &Env,
    t1: Rc<Term>,
    t2: Rc<Term>,
    transparency: crate::Transparency,
    fuel: usize,
) -> Result<bool, TypeError> {
    nbe::is_def_eq_result(t1, t2, env, transparency, fuel).map_err(map_nbe_error)
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
    nbe::is_def_eq_in_ctx_result(t1, t2, &eval_env, env, transparency, fuel)
        .map_err(map_nbe_error)
}

pub fn check(env: &Env, ctx: &Context, term: Rc<Term>, expected_type: Rc<Term>) -> Result<(), TypeError> {
    // println!("Checking {:?} against {:?}", term, expected_type);
    ensure_type_safe(env, &expected_type)?;
    let inferred = infer(env, ctx, term.clone())?;
    if !is_def_eq_in_ctx(env, ctx, inferred.clone(), expected_type.clone(), crate::Transparency::Reducible)? {
        return Err(TypeError::TypeMismatch { expected: expected_type, got: inferred });
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
        Term::App(f, a) => {
            validate_core_term(f)?;
            validate_core_term(a)
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => {
            validate_core_term(ty)?;
            validate_core_term(body)
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

fn is_copy_type(env: &Env, ctx: &Context, ty: &Rc<Term>) -> Result<bool, TypeError> {
    let ty_norm = whnf_in_ctx(env, ctx, ty.clone(), crate::Transparency::Reducible)?;
    match &*ty_norm {
        Term::Sort(_) | Term::Pi(_, _, _) => Ok(true),
        _ => {
            if let Some(ind_name) = get_inductive_name(env, &ty_norm) {
                Ok(env
                    .get_inductive(&ind_name)
                    .map(|decl| decl.is_copy)
                    .unwrap_or(false))
            } else {
                Ok(false)
            }
        }
    }
}

fn check_ownership_in_term(
    env: &Env,
    ctx: &Context,
    term: &Rc<Term>,
    usage: &mut UsageContext,
    mode: UsageMode,
) -> Result<(), TypeError> {
    match &**term {
        Term::Var(idx) => usage.use_var(*idx, mode).map_err(TypeError::from),
        Term::App(f, a) => {
            check_ownership_in_term(env, ctx, f, usage, mode)?;
            check_ownership_in_term(env, ctx, a, usage, mode)
        }
        Term::Lam(ty, body, _) => {
            check_ownership_in_term(env, ctx, ty, usage, UsageMode::Observational)?;
            let is_copy = is_copy_type(env, ctx, ty)?;
            usage.push(is_copy);
            let new_ctx = ctx.push(ty.clone());
            let res = check_ownership_in_term(env, &new_ctx, body, usage, mode);
            usage.pop();
            res
        }
        Term::Pi(ty, body, _) => {
            check_ownership_in_term(env, ctx, ty, usage, UsageMode::Observational)?;
            let is_copy = is_copy_type(env, ctx, ty)?;
            usage.push(is_copy);
            let new_ctx = ctx.push(ty.clone());
            let res = check_ownership_in_term(env, &new_ctx, body, usage, UsageMode::Observational);
            usage.pop();
            res
        }
        Term::LetE(ty, val, body) => {
            check_ownership_in_term(env, ctx, ty, usage, UsageMode::Observational)?;
            check_ownership_in_term(env, ctx, val, usage, mode)?;
            let is_copy = is_copy_type(env, ctx, ty)?;
            usage.push(is_copy);
            let new_ctx = ctx.push(ty.clone());
            let res = check_ownership_in_term(env, &new_ctx, body, usage, mode);
            usage.pop();
            res
        }
        Term::Fix(ty, body) => {
            check_ownership_in_term(env, ctx, ty, usage, UsageMode::Observational)?;
            let is_copy = is_copy_type(env, ctx, ty)?;
            usage.push(is_copy);
            let new_ctx = ctx.push(ty.clone());
            let res = check_ownership_in_term(env, &new_ctx, body, usage, mode);
            usage.pop();
            res
        }
        Term::Const(_, _)
        | Term::Sort(_)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _)
        | Term::Meta(_) => Ok(()),
    }
}

/// Enforce Prop -> Type elimination restriction for inductives in Prop.
/// Allowed only for empty inductives or singleton inductives whose non-parameter
/// fields are all in Prop. Elimination into Prop is always allowed.
pub fn check_elimination_restriction(env: &Env, ind_name: &str, levels: &[Level]) -> Result<(), TypeError> {
    let decl = env.get_inductive(ind_name).ok_or_else(|| TypeError::UnknownInductive(ind_name.to_string()))?;
    
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
    
    // 3. Determine if Inductive is Prop
    // Extract result level from decl.ty
    let (_binders, result_sort) = extract_pi_binders(&decl.ty);
    
    let is_prop = result_sort.as_ref().map_or(false, |level| level_is_zero(level));
    
    if is_prop {
        // Controlled exception: allow equality eliminator (transport) into Type
        // for inductives that match the shape of Eq.
        if is_equality_inductive(decl) {
            return Ok(());
        }

        // 4. Large Elimination Restriction
        // Allowed only if 0 constructors, OR 1 constructor where all non-parameter fields are in Prop.
        
        if decl.ctors.len() > 1 {
            return Err(TypeError::LargeElimination(ind_name.to_string()));
        }
        
        if decl.ctors.len() == 1 {
             // Check all constructor arguments (including parameters).
             // Large elimination is allowed only if every binder lives in Prop.
             let ctor = &decl.ctors[0];
             let mut ctx = Context::new();
             let mut curr = &ctor.ty;

             while let Term::Pi(dom, body, _) = &**curr {
                 // dom is the type of the argument.
                 // infer(dom) should be Sort(Zero) (Prop).
                 let sort = infer(env, &ctx, dom.clone())?;
                 let sort_norm = whnf_in_ctx(env, &ctx, sort, crate::Transparency::Reducible)?;
                 let level = extract_level(&sort_norm);

                 if level.as_ref().map_or(true, |lvl| !level_is_zero(lvl)) {
                      return Err(TypeError::LargeElimination(ind_name.to_string()));
                 }

                 ctx = ctx.push(dom.clone());
                 curr = body;
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
        Term::Lam(ty, body, info) => {
            infer(env, ctx, ty.clone())?;
            ensure_type_safe(env, &ty)?;
            let new_ctx = ctx.push(ty.clone());
            let body_ty = infer(env, &new_ctx, body.clone())?;
            ensure_type_safe(env, &body_ty)?;
            Ok(Term::pi(ty.clone(), body_ty, *info))
        }
        Term::Pi(ty, body, _) => {
            // Pi (x : A) -> B has type Sort(imax(level(A), level(B)))
            let s1 = infer(env, ctx, ty.clone())?;
            let s1_norm = whnf_in_ctx(env, ctx, s1, crate::Transparency::Reducible)?;
            ensure_type_safe(env, &ty)?;
            
            let new_ctx = ctx.push(ty.clone());
            let s2 = infer(env, &new_ctx, body.clone())?;
            let s2_norm = whnf_in_ctx(env, &new_ctx, s2, crate::Transparency::Reducible)?;
            ensure_type_safe(env, &body)?;
            
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
            let f_ty_norm = whnf_in_ctx(env, ctx, f_ty, crate::Transparency::Reducible)?;
            
            if let Term::Pi(arg_ty, body_ty, _) = &*f_ty_norm {
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
            ensure_type_safe(env, &ty)?;
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
            // Check ty is a type
            let _ = infer(env, ctx, ty.clone())?; // Should verify it returns a Sort?
            ensure_type_safe(env, &ty)?;
            // Usually we want to ensure ty is a type, but `infer` returns the type of ty.
            // Strict check:
            // let s = infer(env, ctx, ty.clone())?;
            // if !matches!(&*whnf(env, s, Transparency::Reducible), Term::Sort(_)) { error }
            // For now, restrict fixpoints to function types (Pi) for codegen soundness.
            let ty_whnf = whnf_in_ctx(env, ctx, ty.clone(), crate::Transparency::Reducible)?;
            if !matches!(&*ty_whnf, Term::Pi(_, _, _)) {
                return Err(TypeError::ExpectedFunction(ty_whnf));
            }
            
            // Push ty to context (this is the type of the recursive variable Var(0))
            let new_ctx = ctx.push(ty.clone());
            // Check body has type ty
            check(env, &new_ctx, body.clone(), ty.clone())?;
            Ok(ty.clone())
        }
        Term::Meta(id) => Err(TypeError::UnresolvedMeta(*id)),
    }
}

// =============================================================================
// Soundness Checks
// =============================================================================

/// Check if a term contains references to non-type-safe (partial) definitions
pub fn contains_partial_def(env: &Env, t: &Rc<Term>) -> Option<String> {
    match &**t {
        Term::Var(_) | Term::Sort(_) => None,
        Term::Const(name, _) => {
            if !env.is_type_safe(name) {
                Some(name.clone())
            } else {
                None
            }
        }
        Term::App(f, a) => {
            contains_partial_def(env, f).or_else(|| contains_partial_def(env, a))
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => {
            contains_partial_def(env, ty).or_else(|| contains_partial_def(env, body))
        }
        Term::LetE(ty, val, body) => {
            contains_partial_def(env, ty)
                .or_else(|| contains_partial_def(env, val))
                .or_else(|| contains_partial_def(env, body))
        }
        Term::Fix(_, _) => Some("fix".to_string()),
        Term::Ind(_, _) | Term::Ctor(_, _, _) | Term::Rec(_, _) => None,
        Term::Meta(_) => None,
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
        Term::App(f, a) => contains_const(f, name) || contains_const(a, name),
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) | Term::Fix(ty, body) => contains_const(ty, name) || contains_const(body, name),
        Term::LetE(ty, val, body) => contains_const(ty, name) || contains_const(val, name) || contains_const(body, name),
        Term::Meta(_) => false,
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Polarity {
    Positive,
    Negative,
}

impl Polarity {
    fn flip(self) -> Self {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
        }
    }
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

    for param_idx in 0..num_params {
        let expected = depth - 1 - param_idx;
        match &*args[param_idx] {
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

/// Strict positivity check with polarity tracking for a constructor argument type.
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
        Term::App(_, _) => {
            let (head, args) = collect_app_spine(term);
            if let Term::Ind(name, _) = &*head {
                if name == ind_name {
                    if polarity == Polarity::Negative {
                        return Err(format!(
                            "inductive {} occurs in negative position",
                            ind_name
                        ));
                    }
                    check_inductive_params(ind_name, num_params, &args, depth)?;
                    for arg in &args {
                        check_strict_positivity(ind_name, num_params, arg, depth, polarity)?;
                    }
                    return Ok(());
                }
            }

            check_strict_positivity(ind_name, num_params, &head, depth, polarity)?;
            for arg in &args {
                check_strict_positivity(ind_name, num_params, arg, depth, polarity)?;
            }
            Ok(())
        }
        Term::Ind(name, _) if name == ind_name => {
            if polarity == Polarity::Negative {
                return Err(format!("inductive {} occurs in negative position", ind_name));
            }
            check_inductive_params(ind_name, num_params, &[], depth)?;
            Ok(())
        }
        Term::Pi(dom, body, _) => {
            check_strict_positivity(ind_name, num_params, dom, depth, polarity.flip())?;
            check_strict_positivity(ind_name, num_params, body, depth + 1, polarity)
        }
        Term::Lam(dom, body, _) | Term::Fix(dom, body) => {
            check_strict_positivity(ind_name, num_params, dom, depth, polarity)?;
            check_strict_positivity(ind_name, num_params, body, depth + 1, polarity)
        }
        Term::LetE(ty, val, body) => {
            check_strict_positivity(ind_name, num_params, ty, depth, polarity)?;
            check_strict_positivity(ind_name, num_params, val, depth, polarity)?;
            check_strict_positivity(ind_name, num_params, body, depth + 1, polarity)
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
    if !matches!(&*args[0], Term::Var(1)) {
        return false;
    }
    if !matches!(&*args[1], Term::Var(0)) {
        return false;
    }
    if !matches!(&*args[2], Term::Var(0)) {
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
        Term::App(f, a) => {
            collect_level_params_in_term(f, out);
            collect_level_params_in_term(a, out);
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) | Term::Fix(ty, body) => {
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

/// Check universe levels for an inductive type
fn check_universe_levels(env: &Env, decl: &InductiveDecl) -> Result<(), String> {
    let (_decl_binders, result_sort) = extract_pi_binders(&decl.ty);
    let ind_level = match result_sort {
        Some(level) => reduce_level(level),
        None => return Ok(()),
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

    let (binders, _) = extract_pi_binders(&decl.ty);
    let mut decl_ctx = Context::new();
    let mut param_ctx = Context::new();
    for (idx, (ty, _)) in binders.iter().enumerate() {
        let arg_level = match &**ty {
            Term::Sort(level) => Some(reduce_level(level.clone())),
            _ => {
                let sort = infer(env, &decl_ctx, ty.clone())
                    .map_err(|err| format!("inductive {} binder {}: {:?}", decl.name, idx, err))?;
                let sort_norm = whnf_in_ctx(env, &decl_ctx, sort, crate::Transparency::Reducible)
                    .map_err(|err| format!("inductive {} binder {}: {:?}", decl.name, idx, err))?;
                extract_level(&sort_norm).map(reduce_level)
            }
        };
        if let Some(level) = arg_level {
            if !level_leq(&level, &ind_level) {
                return Err(format!(
                    "inductive {} binder {} has level {:?} which is above inductive level {:?}",
                    decl.name, idx, level, ind_level
                ));
            }
        }
        decl_ctx = decl_ctx.push(ty.clone());
        if idx < decl.num_params {
            param_ctx = param_ctx.push(ty.clone());
        }
    }

    for ctor in &decl.ctors {
        let mut ctx = param_ctx.clone();
        let mut curr = ctor.ty.clone();
        let mut arg_idx = 0usize;

        while let Term::Pi(dom, body, _) = &*curr {
            let arg_level = match &**dom {
                Term::Sort(level) => Some(reduce_level(level.clone())),
                _ => {
                    let sort = infer(env, &ctx, dom.clone())
                        .map_err(|err| format!("constructor {} argument {}: {:?}", ctor.name, arg_idx, err))?;
                    let sort_norm = whnf_in_ctx(env, &ctx, sort, crate::Transparency::Reducible)
                        .map_err(|err| format!("constructor {} argument {}: {:?}", ctor.name, arg_idx, err))?;
                    extract_level(&sort_norm).map(reduce_level)
                }
            };
            if let Some(level) = arg_level {
                if !level_leq(&level, &ind_level) {
                    return Err(format!(
                        "constructor {} argument {} has level {:?} which is above inductive level {:?}",
                        ctor.name, arg_idx, level, ind_level
                    ));
                }
            }

            ctx = ctx.push(dom.clone());
            curr = body.clone();
            arg_idx += 1;
        }
    }

    Ok(())
}

pub fn check_inductive_soundness(env: &Env, decl: &InductiveDecl) -> Result<(), TypeError> {
    // 0. Constructor return type must be the inductive applied to all params/indices
    let total_binders = count_pi_binders(&decl.ty);
    for ctor in &decl.ctors {
        let (_binder_count, _args) = ctor_return_inductive_args(
            &decl.name,
            &ctor.name,
            &ctor.ty,
            total_binders,
        )?;
    }

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

    // 2. Disallow Prop-typed fields in data inductives
    let (_decl_binders, result_sort) = extract_pi_binders(&decl.ty);
    let is_prop_ind = result_sort.as_ref().map_or(false, |level| level_is_zero(level));
    if !is_prop_ind {
        for ctor in &decl.ctors {
            let mut ctx = Context::new();
            let mut curr = ctor.ty.clone();
            let mut binder_idx = 0usize;

            while let Term::Pi(dom, body, _) = &*curr {
                if binder_idx >= decl.num_params {
                    let sort = infer(env, &ctx, dom.clone())?;
                    let sort_norm = whnf_in_ctx(env, &ctx, sort, crate::Transparency::Reducible)?;
                    if extract_level(&sort_norm)
                        .as_ref()
                        .map_or(false, |level| level_is_zero(level))
                    {
                        let field_idx = binder_idx - decl.num_params;
                        return Err(TypeError::PropFieldInData {
                            ind: decl.name.clone(),
                            ctor: ctor.name.clone(),
                            field: field_idx,
                        });
                    }
                }

                ctx = ctx.push(dom.clone());
                curr = body.clone();
                binder_idx += 1;
            }
        }
    }

    // 3. Universe check
    if let Err(msg) = check_universe_levels(env, decl) {
         return Err(TypeError::UniverseLevelTooSmall(decl.name.clone(), "type".to_string(), "ctor".to_string(), msg));
    }
    
    Ok(())
}

fn collect_axioms_rec(env: &Env, t: &Rc<Term>, axioms: &mut HashSet<String>) {
    match &**t {
        Term::Const(name, _) => {
            if let Some(def) = env.get_definition(name) {
                for ax in &def.axioms {
                    axioms.insert(ax.clone());
                }
            }
        }
        Term::App(f, a) => {
            collect_axioms_rec(env, f, axioms);
            collect_axioms_rec(env, a, axioms);
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => {
            collect_axioms_rec(env, ty, axioms);
            collect_axioms_rec(env, body, axioms);
        }
        Term::LetE(ty, val, body) => {
            collect_axioms_rec(env, ty, axioms);
            collect_axioms_rec(env, val, axioms);
            collect_axioms_rec(env, body, axioms);
        }
        Term::Fix(ty, body) => {
            collect_axioms_rec(env, ty, axioms);
            collect_axioms_rec(env, body, axioms);
        }
        _ => {}
    }
}

// =============================================================================
// Classical Axiom Tracking
// =============================================================================

/// Extract the subset of axiom dependencies that are classified as classical.
pub fn classical_axiom_dependencies(env: &Env, def: &Definition) -> Vec<String> {
    let mut deps: Vec<String> = def
        .axioms
        .iter()
        .filter(|ax| {
            env.get_definition(ax.as_str())
                .map(|def| def.is_classical_axiom())
                .unwrap_or(false)
        })
        .cloned()
        .collect();
    deps.sort();
    deps.dedup();
    deps
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
    match allowed_context {
        Totality::Unsafe => return Ok(()), // Unsafe code can do anything
        _ => {}
    }

    match &**t {
        Term::Const(name, _) => {
             if let Some(def) = env.get_definition(name) {
                 match (allowed_context, def.totality) {
                     // Total cannot call Partial or Unsafe
                     (Totality::Total | Totality::WellFounded, Totality::Partial) => {
                         return Err(TypeError::EffectError("Total".to_string(), "Partial".to_string(), name.clone()));
                     }
                     (Totality::Total | Totality::WellFounded, Totality::Unsafe) => {
                         return Err(TypeError::EffectError("Total".to_string(), "Unsafe".to_string(), name.clone()));
                     }
                     
                     // Partial cannot call Unsafe
                     (Totality::Partial, Totality::Unsafe) => {
                         return Err(TypeError::EffectError("Partial".to_string(), "Unsafe".to_string(), name.clone()));
                     }
                     
                     _ => {}
                 }

             }
             Ok(())
        }
        Term::App(f, a) => {
            check_effects(env, allowed_context, f)?;
            check_effects(env, allowed_context, a)
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => {
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
                Totality::Total | Totality::WellFounded => {
                    Err(TypeError::EffectError("Total".to_string(), "Partial".to_string(), "fix".to_string()))
                }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    #[test]
    fn test_effect_boundaries() {
        let mut env = Env::new();
        let sort = Rc::new(Term::Sort(Level::Zero));
        let val = Rc::new(Term::Sort(Level::Zero)); // Dummies
        
        // Define constants with different totalities
        env.definitions.insert("total_def".to_string(), Definition {
            name: "total_def".to_string(),
            ty: sort.clone(),
            value: Some(val.clone()),
            totality: Totality::Total,
            rec_arg: None,
            wf_info: None,
            wf_checked: true,
            transparency: Transparency::Reducible,
            axiom_tags: vec![],
            axioms: vec![],
        });
        
        env.definitions.insert("partial_def".to_string(), Definition {
            name: "partial_def".to_string(),
            ty: sort.clone(),
            value: Some(val.clone()),
            totality: Totality::Partial,
            rec_arg: None,
            wf_info: None,
            wf_checked: true,
            transparency: Transparency::Reducible,
            axiom_tags: vec![],
            axioms: vec![],
        });
        
        env.definitions.insert("unsafe_def".to_string(), Definition {
            name: "unsafe_def".to_string(),
            ty: sort.clone(),
            value: Some(val.clone()),
            totality: Totality::Unsafe,
            rec_arg: None,
            wf_info: None,
            wf_checked: true,
            transparency: Transparency::Reducible,
            axiom_tags: vec![],
            axioms: vec![],
        });

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
    fn test_wellfounded_unfold_requires_check() {
        let mut env = Env::new();
        let ty = Rc::new(Term::Sort(Level::Zero));
        let body = Rc::new(Term::Lam(ty.clone(), Term::var(0), BinderInfo::Default));
        let wf_info = WellFoundedInfo {
            relation: "lt".to_string(),
            decreasing_arg: 0,
        };
        let def = Definition::wellfounded("wf_fn".to_string(), ty.clone(), body, wf_info);
        assert!(!def.wf_checked);
        env.definitions.insert("wf_fn".to_string(), def);

        let term = Rc::new(Term::Const("wf_fn".to_string(), vec![]));
        let val = crate::nbe::eval(&term, &vec![], &env, Transparency::All)
            .expect("nbe eval failed");

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
        let use_choice_def = Definition::total(
            "use_choice".to_string(), 
            prop.clone(), 
            Rc::new(Term::Const("Choice".to_string(), vec![]))
        );
        env.add_definition(use_choice_def).unwrap();
        
        let stored_use = env.get_definition("use_choice").unwrap();
        assert!(stored_use.axioms.contains(&"Choice".to_string()));
        
        // 3. Define Theorem that does NOT use Choice
        // def no_choice := Prop
        let no_choice_def = Definition::total(
            "no_choice".to_string(),
            Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero)))), // Type 0
            prop.clone()
        );
        env.add_definition(no_choice_def).unwrap();
        
        let stored_no = env.get_definition("no_choice").unwrap();
        assert!(stored_no.axioms.is_empty());
    }
}
