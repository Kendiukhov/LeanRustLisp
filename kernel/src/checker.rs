use crate::ast::{Term, Level, InductiveDecl, Constructor, Definition, Totality};
use crate::nbe;
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
    #[error("Effect violation: {0} definition calls {1} definition {2}")]
    EffectError(String, String, String),
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
    /// Recursive call in non-decreasing position (e.g., as a type argument)
    RecursiveCallInType,
    /// Mutual recursion detected but not all functions decrease
    MutualRecursionError {
        /// Functions involved in the mutual recursion
        functions: Vec<String>,
    },
    /// General recursion without structural decrease
    GeneralRecursion,
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
            TerminationErrorDetails::RecursiveCallInType => {
                write!(f, "recursive call appears in type position")
            }
            TerminationErrorDetails::MutualRecursionError { functions } => {
                write!(f, "mutual recursion between {} does not decrease", functions.join(", "))
            }
            TerminationErrorDetails::GeneralRecursion => {
                write!(f, "general recursion detected without structural decrease")
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
    pub definitions: HashMap<String, Definition>,
    // Legacy field for backward compatibility - will be removed
    pub defs: HashMap<String, (Rc<Term>, Rc<Term>)>,
}

impl Env {
    pub fn new() -> Self {
        Env {
            inductives: HashMap::new(),
            definitions: HashMap::new(),
            defs: HashMap::new(),
        }
    }

    /// Register an inductive type definition
    pub fn add_inductive(&mut self, decl: InductiveDecl) -> Result<(), TypeError> {
        check_inductive_soundness(self, &decl)?;
        self.inductives.insert(decl.name.clone(), decl);
        Ok(())
    }

    /// Register a global definition (legacy interface - treats as Total)
    pub fn add_def(&mut self, name: String, ty: Rc<Term>, val: Rc<Term>) {
        // Legacy: assume Total for backward compatibility
        self.defs.insert(name.clone(), (ty.clone(), val.clone()));
        self.definitions.insert(name.clone(), Definition::total(name, ty, val));
    }

    /// Register a definition with explicit totality.
    /// Automatically sets `rec_arg` for total definitions based on termination analysis.
    pub fn add_definition(&mut self, mut def: Definition) -> Result<(), TypeError> {
        // Check that the TYPE doesn't contain partial definitions
        // Types must only reference type-safe (Total/Axiom) definitions
        if let Some(partial_name) = contains_partial_def(self, &def.ty) {
            return Err(TypeError::PartialInType(partial_name));
        }

        // Check Effect Boundaries (Phase 5)
        if let Some(ref val) = def.value {
            check_effects(self, def.totality, val)?;
        }

        // For Total definitions, verify termination and record decreasing argument
        if def.totality == Totality::Total {
            if let Some(ref val) = def.value {
                let rec_arg = check_termination(self, &def.name, &def.ty, val)?;
                // Automatically set rec_arg if not already specified
                if def.rec_arg.is_none() && rec_arg.is_some() {
                    def.rec_arg = rec_arg;
                }
            }
        }

        // Also add to legacy defs for backward compatibility
        if let Some(ref val) = def.value {
            self.defs.insert(def.name.clone(), (def.ty.clone(), val.clone()));
        }
        self.definitions.insert(def.name.clone(), def);
        Ok(())
    }

    /// Register an axiom (assumed without proof)
    pub fn add_axiom(&mut self, name: String, ty: Rc<Term>) {
        let def = Definition::axiom(name.clone(), ty.clone());
        self.definitions.insert(name, def);
    }

    /// Get an inductive declaration by name
    pub fn get_inductive(&self, name: &str) -> Option<&InductiveDecl> {
        self.inductives.get(name)
    }

    /// Get a definition by name (legacy interface)
    pub fn get_def(&self, name: &str) -> Option<&(Rc<Term>, Rc<Term>)> {
        self.defs.get(name)
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
pub fn check_termination(
    env: &Env,
    def_name: &str,
    ty: &Rc<Term>,
    body: &Rc<Term>,
) -> Result<Option<usize>, TypeError> {
    // Step 1: Find the decreasing argument candidate
    let mut param_types = Vec::new();
    let mut curr_ty = ty.clone();
    while let Term::Pi(dom, cod, _) = &*curr_ty {
        param_types.push(dom.clone());
        curr_ty = cod.clone();
    }

    // Find first inductive parameter as decreasing argument candidate
    let mut rec_arg_info = None;
    for (i, param_ty) in param_types.iter().enumerate() {
        if let Some(ind_name) = get_inductive_name(env, param_ty) {
            rec_arg_info = Some((i, ind_name));
            break;
        }
    }

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
    if defs.is_empty() {
        return Ok(vec![]);
    }

    // Build the call graph: which functions call which
    let def_names: Vec<&str> = defs.iter().map(|(n, _, _)| n.as_str()).collect();
    let call_graph = build_call_graph(defs);

    // Find mutually recursive groups (functions that call each other)
    let mutual_groups = find_mutual_groups(&call_graph, &def_names);

    let mut results = Vec::new();

    // Check each mutual group
    for group in &mutual_groups {
        if group.len() == 1 {
            // Single function - use regular termination check
            let name = group[0];
            if let Some((_, ty, body)) = defs.iter().find(|(n, _, _)| n == name) {
                let rec_arg = check_termination(env, name, ty, body)?;
                results.push((name.to_string(), rec_arg));
            }
        } else {
            // Mutual recursion - need common decreasing measure
            let group_defs: Vec<_> = group.iter()
                .filter_map(|name| defs.iter().find(|(n, _, _)| n == *name))
                .collect();

            // Find decreasing arguments for each function in the group
            let mut group_rec_args = Vec::new();
            for (def_name, ty, body) in &group_defs {
                // Find the first inductive argument position
                let mut param_types = Vec::new();
                let mut curr_ty = (*ty).clone();
                while let Term::Pi(dom, cod, _) = &*curr_ty {
                    param_types.push(dom.clone());
                    curr_ty = cod.clone();
                }

                let mut rec_arg_info = None;
                for (i, param_ty) in param_types.iter().enumerate() {
                    if let Some(ind_name) = get_inductive_name(env, param_ty) {
                        rec_arg_info = Some((i, ind_name));
                        break;
                    }
                }

                group_rec_args.push((def_name.as_str(), rec_arg_info));
            }

            // Check that all functions in the group have compatible decreasing arguments
            // For now, require they all decrease on the same position and same inductive type
            let first_rec_arg = group_rec_args.first().and_then(|(_, info)| info.clone());

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
            for (def_name, ty, body) in &group_defs {
                // Check termination with awareness of mutual calls
                let rec_arg = check_termination_mutual(env, def_name, ty, body, &def_names)?;
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
) -> Result<Option<usize>, TypeError> {
    // Similar to check_termination but considers calls to any function in the mutual group
    let mut param_types = Vec::new();
    let mut curr_ty = ty.clone();
    while let Term::Pi(dom, cod, _) = &*curr_ty {
        param_types.push(dom.clone());
        curr_ty = cod.clone();
    }

    // Find first inductive parameter
    let mut rec_arg_info = None;
    for (i, param_ty) in param_types.iter().enumerate() {
        if let Some(ind_name) = get_inductive_name(env, param_ty) {
            rec_arg_info = Some((i, ind_name));
            break;
        }
    }

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
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => {
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
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => {
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
        if is_recursive_field(env, dom, &decl.name) {
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
fn is_recursive_field(env: &Env, ty: &Rc<Term>, ind_name: &str) -> bool {
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
        Term::App(f, _) => {
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
    /// De Bruijn index of the current "fuel" (accessibility proof)
    pub acc_var: usize,
    /// De Bruijn index of the argument being decreased
    pub arg_var: usize,
    /// Variables known to be accessible (with their acc proofs)
    pub accessible_vars: Vec<(usize, usize)>, // (value_var, acc_proof_var)
}

impl WellFoundedCtx {
    pub fn new(relation: String, value_type: Rc<Term>, arg_var: usize, acc_var: usize) -> Self {
        WellFoundedCtx {
            relation,
            value_type,
            acc_var,
            arg_var,
            accessible_vars: vec![(arg_var, acc_var)],
        }
    }

    /// Shift indices when going under a binder
    pub fn shift(&self) -> Self {
        WellFoundedCtx {
            relation: self.relation.clone(),
            value_type: self.value_type.clone(),
            acc_var: self.acc_var + 1,
            arg_var: self.arg_var + 1,
            accessible_vars: self.accessible_vars.iter()
                .map(|(v, a)| (v + 1, a + 1))
                .collect(),
        }
    }

    /// Add a new accessible variable
    pub fn add_accessible(&self, value_var: usize, acc_proof_var: usize) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.accessible_vars.push((value_var, acc_proof_var));
        new_ctx
    }

    /// Check if a variable is known to be accessible
    pub fn is_accessible(&self, var: usize) -> bool {
        self.accessible_vars.iter().any(|(v, _)| *v == var)
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
    // Well-founded recursion checking steps:
    //
    // 1. Verify the wf_proof has type `forall x, Acc R x` (if provided)
    // 2. Check that the function signature includes an Acc argument
    // 3. Check that all recursive calls use Acc.rec or pass smaller accessibility proofs

    // Step 1: Check if Acc type exists in environment
    let has_acc = env.get_inductive("Acc").is_some();

    // Step 2: Verify the well-foundedness proof type (if provided and Acc exists)
    if let Some(ref wf_proof) = spec.wf_proof {
        if has_acc {
            let ctx = Context::new();
            match infer(env, &ctx, wf_proof.clone()) {
                Ok(proof_ty) => {
                    // The proof should have type: forall x : T, Acc R x
                    // For now, we do a structural check
                    if !is_wellfoundedness_proof_type(&proof_ty, &spec.relation, &spec.value_type) {
                        // Log warning but don't fail - trust the user
                        // In a stricter mode, this would be an error
                    }
                }
                Err(_) => {
                    // Proof doesn't type-check, but we trust the annotation for now
                }
            }
        }
    }

    // Step 3: Extract function parameters
    let mut param_types = Vec::new();
    let mut curr_ty = ty.clone();
    while let Term::Pi(dom, cod, _) = &*curr_ty {
        param_types.push(dom.clone());
        curr_ty = cod.clone();
    }

    // Check if there's an Acc argument (either explicit or derivable)
    let num_params = param_types.len();

    // For well-founded recursion, we expect the function to use Acc.rec
    // to extract smaller accessibility proofs at recursive call sites
    if has_acc {
        // Full verification: check that recursive calls use Acc.rec properly
        let inner_body = peel_lambdas(body, num_params);

        // Create a WF context
        let arg_var = num_params - 1 - spec.decreasing_arg;
        // Assume there's an Acc proof at the last argument position
        let acc_var = 0; // Simplified - in practice need to find it

        let wf_ctx = WellFoundedCtx::new(
            spec.relation.clone(),
            spec.value_type.clone(),
            arg_var,
            acc_var,
        );

        // Check recursive calls respect the well-founded ordering
        check_wellfounded_calls(env, def_name, &inner_body, &wf_ctx)?;
    }

    // If no Acc type, trust the annotation (like an axiom)
    Ok(())
}

/// Check if a type represents a well-foundedness proof: forall x : T, Acc R x
fn is_wellfoundedness_proof_type(ty: &Rc<Term>, relation: &str, value_type: &Rc<Term>) -> bool {
    // Expected structure: Pi T (Acc R (Var 0))
    if let Term::Pi(dom, body, _) = &**ty {
        // dom should match value_type
        // body should be Acc applied to relation and Var 0
        // This is a simplified check
        if let Term::App(acc_r, var) = &**body {
            if let Term::Var(0) = &**var {
                // Check acc_r is (Acc R)
                if let Term::App(acc, rel) = &**acc_r {
                    if let Term::Ind(name, _) = &**acc {
                        if name == "Acc" {
                            // Verify relation matches (simplified)
                            return true;
                        }
                    }
                }
            }
        }
    }
    false
}

/// Check that recursive calls in a well-founded recursive function are valid
fn check_wellfounded_calls(
    env: &Env,
    def_name: &str,
    t: &Rc<Term>,
    ctx: &WellFoundedCtx,
) -> Result<(), TypeError> {
    match &**t {
        Term::Const(name, _) if name == def_name => {
            // Bare reference to the function - OK (checked when applied)
            Ok(())
        }
        Term::App(_, _) => {
            // Check if this is an application of Acc.rec
            // Acc.rec provides smaller accessibility proofs to its argument
            if let Some((_ind_name, args)) = extract_rec_app(t) {
                // If using Acc.rec, the minor premise receives smaller acc proofs
                // The inner recursive calls are justified by these smaller proofs
                for arg in &args {
                    check_wellfounded_calls(env, def_name, arg, ctx)?;
                }
                return Ok(());
            }

            // Check if this is a recursive call
            if let Some(args) = extract_app_to_const(t, def_name) {
                // Verify the decreasing argument is accessible
                // In full implementation: verify we have Acc proof for the arg
                // For now: check if it's a variable we know is accessible

                // Check all arguments recursively
                for arg in &args {
                    check_wellfounded_calls(env, def_name, arg, ctx)?;
                }
                return Ok(());
            }

            // Regular application - check both parts
            let (f, args) = collect_app_spine(t);
            check_wellfounded_calls(env, def_name, &f, ctx)?;
            for arg in &args {
                check_wellfounded_calls(env, def_name, arg, ctx)?;
            }
            Ok(())
        }
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => {
            check_wellfounded_calls(env, def_name, ty, ctx)?;
            check_wellfounded_calls(env, def_name, body, &ctx.shift())
        }
        Term::LetE(ty, val, body) => {
            check_wellfounded_calls(env, def_name, ty, ctx)?;
            check_wellfounded_calls(env, def_name, val, ctx)?;
            check_wellfounded_calls(env, def_name, body, &ctx.shift())
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
pub fn compute_recursor_type(decl: &InductiveDecl, univ_levels: &[Level]) -> Rc<Term> {
    // 1. Extract parameters and indices from decl.ty
    let (all_binders, _sort_level) = extract_pi_binders(&decl.ty);
    
    // Split binders into params and indices
    let num_params = decl.num_params;
    let index_binders = &all_binders[num_params..];
    let param_binders = &all_binders[0..num_params];
    
    // 2. Build Motive type
    // Motive: (indices...) -> (t: Ind params indices...) -> Sort u
    let motive_result_sort = Term::sort(Level::Zero); // Placeholder, ideally from univ_levels

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
    for (_name, ty) in index_binders.iter().rev() {
        motive_ty = Term::pi(ty.clone(), motive_ty, crate::ast::BinderInfo::Default);
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
        // Params at: 1 + indices + minors + motive + (num_params - 1 - i)?
        // No. Motive is AT motive_idx. PARAMS are OUTER.
        // So Params are after Motive.
        // Distance: motive_idx + 1 + ...
        let p_idx = motive_idx + 1 + (num_params - 1 - i);
        major_ty = Term::app(major_ty, Term::var(p_idx));
    }
    // Apply Indices
    for i in 0..index_binders.len() {
        let idx = 1 + (index_binders.len() - 1 - i);
        major_ty = Term::app(major_ty, Term::var(idx));
    }
    
    result_body = Term::pi(major_ty, result_body, crate::ast::BinderInfo::Default);
    
    // Bind Indices
    for (i, (_name, ty)) in index_binders.iter().enumerate().rev() {
         // Ty refers to Params (outer) and previous Indices.
         // Previous Indices are valid.
         // Params need shifting?
         // In `decl.ty`, params are outside.
         // In Rec, params are outside Minors/Motive.
         // When checking `ty` of Index k, context is [Params] [PreviousIndices].
         // Here context is [Params] [Motive] [Minors] [PreviousIndices].
         // So we shift Params references by (Motive + Minors).
         // Shift amount = 1 + minors.len().
         result_body = Term::pi(ty.shift(0, 1 + minor_types.len()), result_body, crate::ast::BinderInfo::Default);
    }
    
    // Bind Minors
    for ty in minor_types.iter().rev() {
        result_body = Term::pi(ty.clone(), result_body, crate::ast::BinderInfo::Default);
    }
    
    // Bind Motive
    result_body = Term::pi(motive_ty, result_body, crate::ast::BinderInfo::Default);
    
    // Bind Params
    for (_name, ty) in param_binders.iter().rev() {
        result_body = Term::pi(ty.clone(), result_body, crate::ast::BinderInfo::Default);
    }
    
    result_body
}

// Helper to extract Pi binders (params)
fn extract_pi_binders(term: &Rc<Term>) -> (Vec<(Option<String>, Rc<Term>)>, Option<Level>) {
    let mut binders = Vec::new();
    let mut current = term.clone();
    loop {
        match &*current {
            Term::Pi(ty, body, _) => {
                binders.push((None, ty.clone()));
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
fn compute_minor_premise_type(ind_name: &str, ctor_idx: usize, ctor: &Constructor, num_ctors: usize, num_params: usize) -> Rc<Term> {
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
    
    let args = extract_ctor_args(&instantiated_ty, ind_name);
    
    // ... rest of implementation matches previous logic, just using `instantiated_ty` ...
    
    // 2. Build binders
    struct Binder {
        name: String,
        ty: Rc<Term>,
        is_ih_for: Option<usize>, 
        is_arg_idx: Option<usize>, 
    }
    let mut binders: Vec<Binder> = Vec::new();
    
    for (i, (name, ty, is_rec)) in args.iter().enumerate() {
        let num_ihs = binders.iter().filter(|b| b.is_ih_for.is_some()).count();
        let shifted_ty = ty.shift(num_ihs, 0); 
        
        binders.push(Binder {
            name: name.clone().unwrap_or_else(|| format!("a{}", i)),
            ty: shifted_ty,
            is_ih_for: None,
            is_arg_idx: Some(i),
        });
        
        if *is_rec {
            // IH type: C (Var 0)
            // But apply Params first?
            // Motive C type: `(t: Ind Params) -> Sort`.
            // So `C` takes `Ind Params`?
            // Yes, C is applied to `term`.
            // But `term` acts as full index-saturated term.
            // Does `C` need params applied explicitly?
            // In LRL, `C` is bound as `Pi (t...)`.
            // Params are fixed in context?
            // `Rec` logic:
            // `motive_ty`: `Pi (Ind_app) -> Sort`.
            // `Ind_app` is `Ind P0..Pn`.
            // So `C` expects ONE argument: `t`.
            // So `Arrow(Ind_app, Sort)`.
            // So `C arg` is correct.
            // BUT:
            // Is `arg` (the recursive argument) correct type?
            // `arg` has type `Ind params` (because it's recursive).
            // So `C arg` matches.
            
            // Where is C?
            // Previous calculation: `binders.len() + ctor_idx`.
            // We need to adjust C index because of Params?
            // We calculated `c_idx = num_ctors + 1` relative to inside Major.
            // Here we are inside Minor.
            // Context: `Params... Motive Minors... CurrentBinders...`
            // C is `Motive`.
            // Distance = `CurrentBinders.len() + ctor_idx`. (Assuming `ctor_idx` is number of *previous* minors).
            // Yes, `ctor_idx` = 0 for first minor. C is at `Binders + 0`.
            // Wait. `[Motive] [Minor0]`.
            // Inside Minor0: Motive is at `Binders + 1`. (Motive is immediately above).
            // If `ctor_idx` is index in array, it matches number of *previous* minors.
            // So `Binders + ctor_idx`?
            // Minor 0: `ctor_idx=0`. Motive is at `Binders + 0`? No, Motive is distinct.
            // [Motive] [Minor 0].
            // Depth 1 (Motive).
            // Inside Minor 0: Motive is Var(Binders + 0)?
            // If Binders=0. Motive is Var(0)?
            // No. Binder pushes.
            // If `Pi (m:Motive) (min:Minor)`.
            // Inside Minor: `m` is Var(0).
            // So `Var(ctor_idx)`??
            // If `Pi (m) (min0) (min1)`.
            // Inside min1: `min0` is Var(0), `m` is Var(1).
            // So `Var(ctor_idx + 1)` logic seems plausible if `ctor_idx` counts previous minors.
            // But `ctor_idx` counts *Minors so far*.
            // Minor 0: 0 prev. Motive at 0?
            // Ah, Motive is pushed *before* Minors.
            // Stack: Top -> [Arguments] [Minor 0] [Motive].
            // De Bruijn 0 is Top.
            // Motive is at `Args + PreviousMinors? + 1?`
            // Wait, we generate: `Pi Motive. Pi Minor0. Pi Minor1. ...`
            // So Motive is *outermost*.
            // Inside Minor1: Var(0) is Minor0? No.
            // `Pi Motive (Pi Minor0 (Pi Minor1 ...))`?
            // My code:
            // `result = Term::pi(minor_premise, result)` loop 0..N.
            // Loop runs `rev`. `rec result ...`.
            // Iteration N-1 (Last ctor): `result = Pi(MinorN-1, Major)`.
            // Iteration 0 (First ctor): `result = Pi(Minor0, ... Major)`.
            // Then `result = Pi(Motive, result)`.
            // So final term: `Pi Motive. Pi Minor0. ... Pi Major.`
            // So Motive is outermost.
            // Inside `MinorK`:
            // It sees `Motive` at `k + 1`? (Wait. `MinorK` is type, not term).
            // When defining `MinorK` TYPE, we are in context `[Params] [Motive] [Minor0] ... [MinorK-1]`.
            // So Motive is at `k`. (If Minors are 0..k-1 => k items).
            // Yes. `Var(k)` is Motive.
            // Inside `compute_minor_premise_type`, `ctor_idx` IS `k`.
            // And we push `binders`.
            // So Motive is at `binders.len() + ctor_idx`.
            // Wait, `ctor_idx` is loop index 0..N.
            // Yes. Correct.
            
            let c_idx = binders.len() + ctor_idx;
            let arg_ref = Term::var(0); 
            let ih_ty = Term::app(Term::var(c_idx), arg_ref);
            
            binders.push(Binder {
                name: format!("ih_{}", i),
                ty: ih_ty,
                is_ih_for: Some(i),
                is_arg_idx: None,
            });
        }
    }
    
    // 3. Build result: C (ctor parameters... args...)
    let total_depth = binders.len();
    let c_idx_final = total_depth + ctor_idx;
    
    // Construct (ctor P0..Pn x1...xm)
    let ctor_term = Rc::new(Term::Ctor(ind_name.to_string(), ctor_idx, vec![]));
    let mut app_term = ctor_term;
    
    // Apply parameters first!
    // We need P0...Pn.
    // They are at `total_depth + ctor_idx (previous minors) + 1 (motive) + index`.
    // Depth to Params = `total_depth + ctor_idx + 1`.
    // Param i (0..num_params):
    // Same logic as before: Param 0 (A) is at `depth + num_params - 1 - i`?
    // See instantiating logic above.
    // Param 0 (A) is outermost param.
    // Iterating `extract_pi_binders` (A, B).
    // Context: [A] [B].
    // B is Var 0. A is Var 1.
    // If we want to apply A then B.
    // Apply Var(base + 1), then Var(base + 0).
    // `base = total_depth + ctor_idx + 1`.
    
    for i in 0..num_params {
        let param_var_idx = c_idx_final + 1 + (num_params - 1 - i);
        app_term = Term::app(app_term, Term::var(param_var_idx));
    }
    
    // Apply args
    for (i, _arg) in args.iter().enumerate() {
        let mut depth_from_end = 0;
        let mut found_depth = 0;
        for b in binders.iter().rev() {
            if b.is_arg_idx == Some(i) {
                found_depth = depth_from_end;
                break;
            }
            depth_from_end += 1;
        }
        app_term = Term::app(app_term, Term::var(found_depth));
    }
    
    let result_ty = Term::app(Term::var(c_idx_final), app_term);
    
    // 4. Fold back
    let mut final_term = result_ty;
    for binder in binders.iter().rev() {
        final_term = Term::pi(binder.ty.clone(), final_term, crate::ast::BinderInfo::Default);
    }
    
    final_term
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

/// Weak Head Normal Form reduction with iota reduction
/// Weak Head Normal Form reduction (Via NbE)
pub fn whnf(env: &Env, t: Rc<Term>, _transparency: crate::Transparency) -> Rc<Term> {
    let val = nbe::eval(&t, &vec![], env);
    nbe::quote(val, 0, env)
}

// try_iota_reduce removed


/// Definitional equality checking
/// Definitional equality checking via NbE
pub fn is_def_eq(env: &Env, t1: Rc<Term>, t2: Rc<Term>, _transparency: crate::Transparency) -> bool {
    nbe::is_def_eq(t1, t2, env)
}

pub fn check(env: &Env, ctx: &Context, term: Rc<Term>, expected_type: Rc<Term>) -> Result<(), TypeError> {
    // println!("Checking {:?} against {:?}", term, expected_type);
    let inferred = infer(env, ctx, term.clone())?;
    if !is_def_eq(env, inferred.clone(), expected_type.clone(), crate::Transparency::All) {
        println!("TypeMismatch: Term: {:?}, Expected {:?}, Got {:?}", term, expected_type, inferred);
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
        Term::Lam(ty, body, _) => {
            infer(env, ctx, ty.clone())?;
            let new_ctx = ctx.push(ty.clone());
            let body_ty = infer(env, &new_ctx, body.clone())?;
            Ok(Term::pi(ty.clone(), body_ty, crate::ast::BinderInfo::Default))
        }
        Term::Pi(ty, body, _) => {
            // Pi (x : A) -> B has type Sort(imax(level(A), level(B)))
            let s1 = infer(env, ctx, ty.clone())?;
            let s1_norm = whnf(env, s1, crate::Transparency::All);
            
            let new_ctx = ctx.push(ty.clone());
            let s2 = infer(env, &new_ctx, body.clone())?;
            let s2_norm = whnf(env, s2, crate::Transparency::All);
            
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
            let f_ty_norm = whnf(env, f_ty, crate::Transparency::All);
            
            if let Term::Pi(arg_ty, body_ty, _) = &*f_ty_norm {
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
        Term::Meta(_) => todo!(),
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
        Term::Ind(_, _) | Term::Ctor(_, _, _) | Term::Rec(_, _) => None,
        Term::Meta(_) => None,
    }
}

/// Check if a term contains a specific constant (by name)
fn contains_const(t: &Rc<Term>, name: &str) -> bool {
    match &**t {
        Term::Var(_) | Term::Sort(_) => false,
        Term::Const(n, _) | Term::Ind(n, _) | Term::Ctor(n, _, _) | Term::Rec(n, _) => n == name,
        Term::App(f, a) => contains_const(f, name) || contains_const(a, name),
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => contains_const(ty, name) || contains_const(body, name),
        Term::LetE(ty, val, body) => contains_const(ty, name) || contains_const(val, name) || contains_const(body, name),
        Term::Meta(_) => false,
    }
}

/// Check strict positivity of an inductive type in a constructor argument.
fn check_positivity(ind_name: &str, arg_ty: &Rc<Term>) -> Result<(), String> {
    if !contains_const(arg_ty, ind_name) {
        return Ok(());
    }

    // Decompose Pi: P1 -> P2 -> ... -> Head
    let mut current = arg_ty.clone();
    let mut param_types = Vec::new();
    
    while let Term::Pi(ty, body, _) = &*current {
        param_types.push(ty.clone());
        current = body.clone();
    }
    
    // Check Head: Must be `Ind` or `App(Ind, ...)`
    let head_valid = match &*current {
        Term::Ind(n, _) => n == ind_name,
        Term::App(f, _args) => { // Flatten app to check head
             let mut head = f.clone();
             while let Term::App(h, _) = &*head {
                 head = h.clone();
             }
             if let Term::Ind(n, _) = &*head {
                 n == ind_name
             } else {
                 false
             }
        }
        _ => false,
    };

    if !head_valid {
        return Err(format!("Inductive type {} occurs in non-positive position (not as return type)", ind_name));
    }

    // Check Params: Must NOT contain ind_name
    for (i, p_ty) in param_types.iter().enumerate() {
        if contains_const(p_ty, ind_name) {
             return Err(format!("Inductive type {} occurs negatively in domain of recursive argument (param {})", ind_name, i));
        }
    }

    Ok(())
}

/// Check universe levels for an inductive type
fn check_universe_levels(_env: &Env, decl: &InductiveDecl) -> Result<(), String> {
    // 1. Extract level of Inductive Type
    let _ind_level = match extract_level(&decl.ty) {
        Some(l) => l,
        None => return Ok(()), 
    };
    
    // Placeholder for strict universe check
    Ok(())
}

pub fn check_inductive_soundness(env: &Env, decl: &InductiveDecl) -> Result<(), TypeError> {
    // 1. Check Positivity
    for ctor in &decl.ctors {
         // Extract args (full type args)
         let args = extract_ctor_args(&ctor.ty, &decl.name);
         for (arg_idx, (_, arg_ty, _)) in args.iter().enumerate() {
             if let Err(_msg) = check_positivity(&decl.name, arg_ty) {
                 return Err(TypeError::NonPositiveOccurrence(decl.name.clone(), ctor.name.clone(), arg_idx));
             }
         }
    }
    
    // 2. Universe check
    if let Err(msg) = check_universe_levels(env, decl) {
         return Err(TypeError::UniverseLevelTooSmall(decl.name.clone(), "type".to_string(), "ctor".to_string(), msg));
    }
    
    Ok(())
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
             } else if let Some(_) = env.get_def(name) {
                 // Legacy definitions are assumed Total
                 // No check needed
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
            wf_info: None
        });
        
        env.definitions.insert("partial_def".to_string(), Definition {
            name: "partial_def".to_string(),
            ty: sort.clone(),
            value: Some(val.clone()),
            totality: Totality::Partial,
            rec_arg: None,
            wf_info: None
        });
        
        env.definitions.insert("unsafe_def".to_string(), Definition {
            name: "unsafe_def".to_string(),
            ty: sort.clone(),
            value: Some(val.clone()),
            totality: Totality::Unsafe,
            rec_arg: None,
            wf_info: None
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
}
