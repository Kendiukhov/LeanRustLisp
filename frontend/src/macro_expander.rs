use crate::diagnostics::Diagnostic;
use crate::surface::{
    normalize_scopes, scopes_with, scopes_without, ScopeId, Span, Syntax, SyntaxKind,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use thiserror::Error;

const CODE_EXPANSION_TRANSFORMATION: &str = "F0100";
const CODE_EXPANSION_ARG_COUNT: &str = "F0101";
const CODE_EXPANSION_INVALID_SYNTAX: &str = "F0102";
const CODE_EXPANSION_UNKNOWN_FORM: &str = "F0103";
const CODE_EXPANSION_MACRO_BOUNDARY: &str = "F0104";
const CODE_EXPANSION_ALLOWLIST_REDEF: &str = "F0105";
const CODE_EXPANSION_LIMIT: &str = "F0106";
const CODE_EXPANSION_CYCLE: &str = "F0107";

const DEFAULT_EXPANSION_STEP_LIMIT: usize = 10_000;
const DEFAULT_EXPANSION_DEPTH_LIMIT: usize = 128;

#[derive(Error, Debug)]
pub enum ExpansionError {
    #[error("Transformation failed: {0}")]
    TransformationError(String),
    #[error("Invalid argument count for '{0}': expected {1}, got {2}")]
    ArgumentCountMismatch(String, usize, usize),
    #[error("Invalid syntax for '{0}': {1}")]
    InvalidSyntax(String, String),
    #[error("Unknown macro or form: {0}")]
    UnknownForm(String),
    #[error("Macro boundary denied for '{macro_name}': {hits:?}")]
    MacroBoundaryDenied {
        macro_name: String,
        hits: Vec<String>,
    },
    #[error("Macro expansion step limit exceeded (limit {limit})")]
    ExpansionStepLimitExceeded { limit: usize },
    #[error("Macro expansion depth limit exceeded (limit {limit})")]
    ExpansionDepthLimitExceeded { limit: usize },
    #[error("Macro expansion cycle detected: {cycle:?}")]
    MacroExpansionCycle { cycle: Vec<String> },
}

impl ExpansionError {
    pub fn diagnostic_code(&self) -> &'static str {
        match self {
            ExpansionError::TransformationError(_) => CODE_EXPANSION_TRANSFORMATION,
            ExpansionError::ArgumentCountMismatch(_, _, _) => CODE_EXPANSION_ARG_COUNT,
            ExpansionError::InvalidSyntax(_, _) => CODE_EXPANSION_INVALID_SYNTAX,
            ExpansionError::UnknownForm(_) => CODE_EXPANSION_UNKNOWN_FORM,
            ExpansionError::MacroBoundaryDenied { .. } => CODE_EXPANSION_MACRO_BOUNDARY,
            ExpansionError::ExpansionStepLimitExceeded { .. }
            | ExpansionError::ExpansionDepthLimitExceeded { .. } => CODE_EXPANSION_LIMIT,
            ExpansionError::MacroExpansionCycle { .. } => CODE_EXPANSION_CYCLE,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MacroDef {
    pub args: Vec<String>,
    pub body: Syntax,
    pub origin_module: String,
}

#[derive(Clone, Debug)]
struct MacroModule {
    macros: BTreeMap<String, MacroDef>,
    imports: BTreeSet<String>,
    version: u64,
    loaded: bool,
}

impl MacroModule {
    fn new() -> Self {
        MacroModule {
            macros: BTreeMap::new(),
            imports: BTreeSet::new(),
            version: 0,
            loaded: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroTraceEntry {
    pub name: String,
    pub span: Span,
    pub depth: usize,
}

#[derive(Debug, Clone)]
struct MacroCallFrame {
    key: String,
    name: String,
    span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExpansionLimit {
    Full,
    SingleStep,
}

#[derive(Debug, Clone, Copy)]
struct ExpansionBudget {
    remaining: usize,
    limit: usize,
}

impl ExpansionBudget {
    fn new(limit: usize) -> Self {
        ExpansionBudget {
            remaining: limit,
            limit,
        }
    }

    fn consume(&mut self) -> bool {
        if self.remaining == 0 {
            return false;
        }
        self.remaining -= 1;
        true
    }
}

// Shared mutable state threaded through recursive expansion calls.
#[derive(Debug)]
struct ExpansionState<'a> {
    budget: &'a mut ExpansionBudget,
    trace: &'a mut Vec<MacroTraceEntry>,
    trace_enabled: bool,
    did_expand: &'a mut bool,
}

impl<'a> ExpansionState<'a> {
    fn new(
        budget: &'a mut ExpansionBudget,
        trace: &'a mut Vec<MacroTraceEntry>,
        trace_enabled: bool,
        did_expand: &'a mut bool,
    ) -> Self {
        Self {
            budget,
            trace,
            trace_enabled,
            did_expand,
        }
    }

    fn single_step_done(&self, limit: ExpansionLimit) -> bool {
        limit == ExpansionLimit::SingleStep && *self.did_expand
    }

    fn mark_expanded(&mut self) {
        *self.did_expand = true;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum MacroBoundaryKind {
    UnsafeForm,
    Eval,
    Axiom,
    UnsafeAxiom,
    ClassicalAxiom,
    ClassicalImport,
}

impl MacroBoundaryKind {
    fn label(self) -> &'static str {
        match self {
            MacroBoundaryKind::UnsafeForm => "unsafe",
            MacroBoundaryKind::Eval => "eval",
            MacroBoundaryKind::Axiom => "axiom",
            MacroBoundaryKind::UnsafeAxiom => "axiom unsafe",
            MacroBoundaryKind::ClassicalAxiom => "axiom classical",
            MacroBoundaryKind::ClassicalImport => "import classical",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroBoundaryPolicy {
    Deny,
    Warn,
}

const RESERVED_MACRO_NAMES: &[&str] = &[
    "axiom",
    "def",
    "defmacro",
    "eval",
    "import",
    "import-macros",
    "inductive",
    "instance",
    "module",
    "open",
    "opaque",
    "partial",
    "noncomputable",
    "structure",
    "transparent",
    "unsafe",
];

pub fn is_reserved_macro_name(name: &str) -> bool {
    RESERVED_MACRO_NAMES.contains(&name)
}

fn empty_syntax() -> Syntax {
    Syntax {
        kind: SyntaxKind::List(vec![]),
        span: Span {
            start: 0,
            end: 0,
            line: 0,
            col: 0,
        },
        scopes: vec![],
    }
}

fn format_trace_entries(trace: &[MacroTraceEntry]) -> String {
    let mut output = String::from("Macro Trace:");
    if trace.is_empty() {
        output.push_str("\n  (none)");
        return output;
    }

    for entry in trace {
        let indent = "  ".repeat(entry.depth);
        output.push('\n');
        output.push_str(&format!(
            "{}- {} @ {}:{} [{}..{}]",
            indent, entry.name, entry.span.line, entry.span.col, entry.span.start, entry.span.end
        ));
    }

    output
}

pub struct Expander {
    scope_counter: usize,
    modules: BTreeMap<String, MacroModule>, // module -> macros/imports
    current_module: String,
    default_imports: BTreeSet<String>,
    last_env_version: Option<u64>,
    pub expansion_trace: Vec<(String, Span)>,
    pending_diagnostics: Vec<Diagnostic>,
    macro_boundary_policy: MacroBoundaryPolicy,
    macro_boundary_allowlist: BTreeMap<String, BTreeSet<String>>,
    macro_boundary_allowlist_active: bool,
    expansion_step_limit: usize,
    expansion_depth_limit: usize,
    expansion_cache: HashMap<String, Syntax>,
    expansion_cache_env_fingerprint: Option<String>,
    active_macro_keys: BTreeSet<String>,
    macro_call_stack: Vec<MacroCallFrame>,
    pub verbose: bool,
    pub trace_verbose: bool,
}

impl Default for Expander {
    fn default() -> Self {
        Self::new()
    }
}

impl Expander {
    pub fn new() -> Self {
        let mut expander = Expander {
            scope_counter: 0,
            modules: BTreeMap::new(),
            current_module: "repl".to_string(),
            default_imports: BTreeSet::new(),
            last_env_version: None,
            expansion_trace: Vec::new(),
            pending_diagnostics: Vec::new(),
            macro_boundary_policy: MacroBoundaryPolicy::Deny,
            macro_boundary_allowlist: BTreeMap::new(),
            macro_boundary_allowlist_active: false,
            expansion_step_limit: DEFAULT_EXPANSION_STEP_LIMIT,
            expansion_depth_limit: DEFAULT_EXPANSION_DEPTH_LIMIT,
            expansion_cache: HashMap::new(),
            expansion_cache_env_fingerprint: None,
            active_macro_keys: BTreeSet::new(),
            macro_call_stack: Vec::new(),
            verbose: false,
            trace_verbose: false,
        };
        expander.ensure_module("repl");
        expander
    }

    pub fn set_macro_boundary_policy(&mut self, policy: MacroBoundaryPolicy) {
        self.macro_boundary_policy = policy;
    }

    pub fn set_macro_expansion_limits(&mut self, step_limit: usize, depth_limit: usize) {
        self.expansion_step_limit = step_limit;
        self.expansion_depth_limit = depth_limit;
    }

    pub fn set_macro_boundary_allowlist<I, S, M>(&mut self, module: M, allowlist: I)
    where
        M: Into<String>,
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let module = module.into();
        let entries: BTreeSet<String> = allowlist.into_iter().map(Into::into).collect();
        if entries.is_empty() {
            self.macro_boundary_allowlist.remove(&module);
        } else {
            self.macro_boundary_allowlist.insert(module, entries);
        }
        self.macro_boundary_allowlist_active = true;
    }

    pub fn clear_macro_boundary_allowlist(&mut self) {
        self.macro_boundary_allowlist_active = false;
    }

    fn ensure_module(&mut self, module: &str) -> &mut MacroModule {
        if !self.modules.contains_key(module) {
            let mut env = MacroModule::new();
            for import in &self.default_imports {
                if import != module {
                    env.imports.insert(import.clone());
                }
            }
            self.modules.insert(module.to_string(), env);
        }
        self.modules.get_mut(module).expect("module missing")
    }

    pub fn enter_module<S: Into<String>>(&mut self, module: S) {
        let module = module.into();
        self.current_module.clone_from(&module);
        self.ensure_module(&module);
    }

    pub fn current_module(&self) -> &str {
        &self.current_module
    }

    pub fn has_module(&self, module: &str) -> bool {
        self.modules.contains_key(module)
    }

    pub fn is_module_loaded(&self, module: &str) -> bool {
        self.modules
            .get(module)
            .map(|env| env.loaded)
            .unwrap_or(false)
    }

    pub fn mark_module_loaded(&mut self, module: &str) {
        if let Some(env) = self.modules.get_mut(module) {
            env.loaded = true;
        }
    }

    pub fn set_default_imports<I>(&mut self, imports: I)
    where
        I: IntoIterator<Item = String>,
    {
        self.default_imports = imports.into_iter().collect();
        for (module, env) in self.modules.iter_mut() {
            let mut changed = false;
            for import in &self.default_imports {
                if import == module {
                    continue;
                }
                if env.imports.insert(import.clone()) {
                    changed = true;
                }
            }
            if changed {
                env.version = env.version.saturating_add(1);
            }
        }
    }

    pub fn import_module(&mut self, module: String) {
        if module == self.current_module {
            return;
        }
        self.ensure_module(&module);
        let env = self.ensure_module(&self.current_module.clone());
        if env.imports.insert(module.clone()) {
            env.version = env.version.saturating_add(1);
        }
    }

    fn stable_fingerprint_hash(fingerprint: &str) -> u64 {
        const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
        const FNV_PRIME: u64 = 0x00000100000001B3;

        let mut hash = FNV_OFFSET_BASIS;
        for byte in fingerprint.as_bytes() {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash
    }

    fn collect_transitive_module_ids(&self, root_module: &str) -> BTreeSet<String> {
        // Use a stable set to ensure deterministic ordering independent of
        // module insertion order in the current process.
        let mut reachable = BTreeSet::new();
        let mut pending = vec![root_module.to_string()];

        while let Some(module_id) = pending.pop() {
            if !reachable.insert(module_id.clone()) {
                continue;
            }

            if let Some(env) = self.modules.get(&module_id) {
                for import in env.imports.iter().rev() {
                    if !reachable.contains(import) {
                        pending.push(import.clone());
                    }
                }
            }
        }

        reachable
    }

    fn macro_env_fingerprint(&self) -> String {
        // Cache invalidation is keyed by the full transitive macro environment,
        // not only direct imports, so downstream import changes are observed.
        let transitive_modules = self.collect_transitive_module_ids(&self.current_module);
        let mut fingerprint = String::new();

        fingerprint.push_str("macro-env-v2|");
        Self::append_text_key(&mut fingerprint, &self.current_module);
        fingerprint.push('|');
        fingerprint.push_str(&transitive_modules.len().to_string());
        fingerprint.push('|');

        for module_id in transitive_modules {
            Self::append_text_key(&mut fingerprint, &module_id);
            fingerprint.push('#');

            if let Some(env) = self.modules.get(&module_id) {
                fingerprint.push_str(&env.version.to_string());
                fingerprint.push('#');
                fingerprint.push_str(&env.imports.len().to_string());
                fingerprint.push('#');
                for import in &env.imports {
                    Self::append_text_key(&mut fingerprint, import);
                    fingerprint.push(',');
                }
            } else {
                fingerprint.push_str("missing");
            }

            fingerprint.push('|');
        }

        fingerprint
    }

    pub fn macro_env_version(&self) -> u64 {
        Self::stable_fingerprint_hash(&self.macro_env_fingerprint())
    }

    pub fn last_expansion_env_version(&self) -> Option<u64> {
        self.last_env_version
    }

    /// Create a new unique scope identifier for hygiene tracking.
    pub fn new_scope(&mut self) -> ScopeId {
        let id = self.scope_counter;
        self.scope_counter += 1;
        ScopeId(id)
    }

    pub fn scopes_compatible(reference_scopes: &[ScopeId], definition_scopes: &[ScopeId]) -> bool {
        let ref_norm = normalize_scopes(reference_scopes);
        let def_norm = normalize_scopes(definition_scopes);

        if def_norm.is_empty() {
            return ref_norm.is_empty();
        }

        let mut ref_idx = 0usize;
        let mut def_idx = 0usize;
        while ref_idx < ref_norm.len() && def_idx < def_norm.len() {
            match ref_norm[ref_idx].cmp(&def_norm[def_idx]) {
                std::cmp::Ordering::Equal => {
                    ref_idx += 1;
                    def_idx += 1;
                }
                std::cmp::Ordering::Less => {
                    ref_idx += 1;
                }
                std::cmp::Ordering::Greater => {
                    return false;
                }
            }
        }
        def_idx == def_norm.len()
    }

    pub fn add_scope(syntax: &Syntax, scope: ScopeId) -> Syntax {
        Syntax {
            scopes: scopes_with(&syntax.scopes, scope),
            ..syntax.clone()
        }
    }

    pub fn remove_scope(syntax: &Syntax, scope: ScopeId) -> Syntax {
        Syntax {
            scopes: scopes_without(&syntax.scopes, scope),
            ..syntax.clone()
        }
    }

    pub fn expand(&mut self, syntax: Syntax) -> Result<Option<Syntax>, ExpansionError> {
        let (expanded, trace) = if self.trace_verbose {
            self.expand_all_macros_with_trace(syntax)?
        } else {
            (self.expand_all_macros(syntax)?, Vec::new())
        };

        if self.trace_verbose && !trace.is_empty() {
            println!("{}", format_trace_entries(&trace));
        }

        if let Some(expanded_syntax) = expanded {
            if self.verbose {
                println!("Expanded: {}", expanded_syntax.pretty_print());
            }
            Ok(Some(expanded_syntax))
        } else {
            Ok(None)
        }
    }

    /// Public method to expand macros only (returns Syntax), useful for tooling (:expand)
    pub fn expand_syntax(&mut self, syntax: Syntax) -> Result<Syntax, ExpansionError> {
        let res = self.expand_all_macros(syntax)?;
        Ok(res.unwrap_or_else(empty_syntax))
    }

    /// Expand only a single macro step (returns Syntax), useful for :expand-1.
    pub fn expand_syntax_once(&mut self, syntax: Syntax) -> Result<Syntax, ExpansionError> {
        self.last_env_version = Some(self.macro_env_version());
        self.begin_expansion_session();
        let mut trace = Vec::new();
        let mut did_expand = false;
        let mut budget = ExpansionBudget::new(self.expansion_step_limit);
        let mut state = ExpansionState::new(&mut budget, &mut trace, false, &mut did_expand);
        let res = self.expand_macros_internal(syntax, ExpansionLimit::SingleStep, &mut state, 0)?;
        Ok(res.unwrap_or_else(empty_syntax))
    }

    /// Expand macros fully while collecting a trace of macro invocations.
    pub fn expand_syntax_with_trace(
        &mut self,
        syntax: Syntax,
    ) -> Result<(Syntax, Vec<MacroTraceEntry>), ExpansionError> {
        let (res, trace) = self.expand_all_macros_with_trace(syntax)?;
        Ok((res.unwrap_or_else(empty_syntax), trace))
    }

    pub fn expand_all_macros_with_trace(
        &mut self,
        syntax: Syntax,
    ) -> Result<(Option<Syntax>, Vec<MacroTraceEntry>), ExpansionError> {
        self.last_env_version = Some(self.macro_env_version());
        self.begin_expansion_session();
        let mut trace = Vec::new();
        let mut did_expand = false;
        let mut budget = ExpansionBudget::new(self.expansion_step_limit);
        let res = {
            let mut state = ExpansionState::new(&mut budget, &mut trace, true, &mut did_expand);
            self.expand_macros_internal(syntax, ExpansionLimit::Full, &mut state, 0)?
        };
        Ok((res, trace))
    }

    pub fn add_macro(&mut self, name: String, args: Vec<String>, body: Syntax) {
        let origin_module = self.current_module.clone();
        let env = self.ensure_module(&origin_module);
        env.macros.insert(
            name,
            MacroDef {
                args,
                body,
                origin_module,
            },
        );
        env.version = env.version.saturating_add(1);
    }

    pub fn take_expansion_trace(&mut self) -> Vec<MacroTraceEntry> {
        let trace = self
            .expansion_trace
            .iter()
            .enumerate()
            .map(|(depth, (name, span))| MacroTraceEntry {
                name: name.clone(),
                span: *span,
                depth,
            })
            .collect();
        self.expansion_trace.clear();
        trace
    }

    pub fn take_pending_diagnostics(&mut self) -> Vec<Diagnostic> {
        std::mem::take(&mut self.pending_diagnostics)
    }

    fn current_trace_entries(&self) -> Vec<MacroTraceEntry> {
        self.expansion_trace
            .iter()
            .enumerate()
            .map(|(depth, (name, span))| MacroTraceEntry {
                name: name.clone(),
                span: *span,
                depth,
            })
            .collect()
    }

    fn record_expansion_limit_diagnostic(&mut self, span: Span, message: String) {
        let trace = self.current_trace_entries();
        let mut diagnostic = Diagnostic::error(message)
            .with_code(CODE_EXPANSION_LIMIT)
            .with_span(span);
        for entry in trace {
            diagnostic =
                diagnostic.with_label(entry.span, format!("macro expansion: {}", entry.name));
        }
        self.pending_diagnostics.push(diagnostic);
    }

    fn record_expansion_cycle_diagnostic(&mut self, span: Span, cycle: &[String]) {
        let mut diagnostic = Diagnostic::error(format!(
            "Macro expansion cycle detected: {}",
            cycle.join(" -> ")
        ))
        .with_code(CODE_EXPANSION_CYCLE)
        .with_span(span);
        for frame in &self.macro_call_stack {
            diagnostic =
                diagnostic.with_label(frame.span, format!("macro expansion: {}", frame.name));
        }
        for entry in self.current_trace_entries() {
            diagnostic =
                diagnostic.with_label(entry.span, format!("macro expansion: {}", entry.name));
        }
        self.pending_diagnostics.push(diagnostic);
    }

    fn ensure_expansion_cache_fingerprint(&mut self) {
        let fingerprint = self.macro_env_fingerprint();
        // A changed fingerprint means at least one transitive module dependency
        // changed, so cached expansions are no longer valid.
        if self.expansion_cache_env_fingerprint.as_ref() != Some(&fingerprint) {
            self.expansion_cache.clear();
            self.expansion_cache_env_fingerprint = Some(fingerprint);
        }
    }

    fn begin_expansion_session(&mut self) {
        self.ensure_expansion_cache_fingerprint();
        self.expansion_trace.clear();
        self.active_macro_keys.clear();
        self.macro_call_stack.clear();
    }

    fn append_text_key(out: &mut String, text: &str) {
        out.push_str(&text.len().to_string());
        out.push(':');
        out.push_str(text);
    }

    fn append_scopes_key(out: &mut String, scopes: &[ScopeId]) {
        let normalized = normalize_scopes(scopes);
        out.push('[');
        for (idx, scope) in normalized.iter().enumerate() {
            if idx > 0 {
                out.push(',');
            }
            out.push_str(&scope.0.to_string());
        }
        out.push(']');
    }

    fn append_syntax_key(out: &mut String, syntax: &Syntax) {
        match &syntax.kind {
            SyntaxKind::List(items) => {
                out.push_str("L(");
                for item in items {
                    Self::append_syntax_key(out, item);
                    out.push(';');
                }
                out.push(')');
            }
            SyntaxKind::BracedList(items) => {
                out.push_str("B(");
                for item in items {
                    Self::append_syntax_key(out, item);
                    out.push(';');
                }
                out.push(')');
            }
            SyntaxKind::Index(base, index) => {
                out.push_str("I(");
                Self::append_syntax_key(out, base);
                out.push(';');
                Self::append_syntax_key(out, index);
                out.push(')');
            }
            SyntaxKind::Symbol(symbol) => {
                out.push('S');
                Self::append_text_key(out, symbol);
            }
            SyntaxKind::String(string) => {
                out.push('Q');
                Self::append_text_key(out, string);
            }
            SyntaxKind::Int(value) => {
                out.push('N');
                out.push_str(&value.to_string());
            }
            SyntaxKind::Hole => out.push('H'),
        }
        out.push('@');
        Self::append_scopes_key(out, &syntax.scopes);
    }

    fn macro_call_key(&self, macro_name: &str, args: &[Syntax]) -> String {
        let mut key = String::new();
        key.push_str("M:");
        Self::append_text_key(&mut key, &self.current_module);
        key.push('|');
        Self::append_text_key(&mut key, macro_name);
        key.push('|');
        key.push_str(&args.len().to_string());
        key.push('|');
        for arg in args {
            Self::append_syntax_key(&mut key, arg);
            key.push('|');
        }
        key
    }

    fn macro_cycle_from_key(&self, key: &str, macro_name: &str) -> Vec<String> {
        if let Some(start) = self
            .macro_call_stack
            .iter()
            .position(|frame| frame.key == key)
        {
            let mut cycle: Vec<String> = self.macro_call_stack[start..]
                .iter()
                .map(|frame| frame.name.clone())
                .collect();
            cycle.push(macro_name.to_string());
            return cycle;
        }
        vec![macro_name.to_string()]
    }

    fn check_macro_boundary(
        &mut self,
        macro_name: &str,
        macro_origin: &str,
        call_site: Span,
        expanded: &Syntax,
    ) -> Result<(), ExpansionError> {
        if self.is_macro_allowlisted(macro_name, macro_origin) {
            return Ok(());
        }
        let mut hits = BTreeSet::new();
        Self::collect_macro_boundary_hits(expanded, &mut hits);
        if hits.is_empty() {
            return Ok(());
        }

        let labels: Vec<&'static str> = hits.iter().map(|hit| hit.label()).collect();

        let mut message = format!(
            "Macro expansion for '{}' produced macro boundary form(s): {}",
            macro_name,
            labels.join(", ")
        );
        let mut diagnostic = match self.macro_boundary_policy {
            MacroBoundaryPolicy::Warn => Diagnostic::warning(message.clone())
                .with_code(CODE_EXPANSION_MACRO_BOUNDARY),
            MacroBoundaryPolicy::Deny => {
                message.push_str(" (macro boundary violations are errors; use --macro-boundary-warn to allow warnings)");
                Diagnostic::error(message).with_code(CODE_EXPANSION_MACRO_BOUNDARY)
            }
        }
        .with_span(call_site);
        for (name, span) in &self.expansion_trace {
            diagnostic = diagnostic.with_label(*span, format!("macro expansion: {}", name));
        }
        self.pending_diagnostics.push(diagnostic);

        if self.macro_boundary_policy == MacroBoundaryPolicy::Deny {
            return Err(ExpansionError::MacroBoundaryDenied {
                macro_name: macro_name.to_string(),
                hits: labels.iter().map(|label| (*label).to_string()).collect(),
            });
        }

        Ok(())
    }

    fn is_macro_allowlisted(&self, macro_name: &str, macro_origin: &str) -> bool {
        if !self.macro_boundary_allowlist_active {
            return false;
        }
        self.macro_boundary_allowlist
            .get(macro_origin)
            .map_or(false, |names| names.contains(macro_name))
    }

    fn allowlist_origin_for_name(&self, macro_name: &str) -> Option<&str> {
        self.macro_boundary_allowlist
            .iter()
            .find_map(|(module, names)| {
                if names.contains(macro_name) {
                    Some(module.as_str())
                } else {
                    None
                }
            })
    }

    fn is_macro_name_allowlisted_in_module(&self, macro_name: &str, module: &str) -> bool {
        self.macro_boundary_allowlist
            .get(module)
            .map_or(false, |names| names.contains(macro_name))
    }

    fn record_allowlist_redefinition_warning(&mut self, macro_name: &str, span: Span) {
        let current_module = self.current_module.clone();
        if self.is_macro_name_allowlisted_in_module(macro_name, &current_module) {
            return;
        }
        if let Some(allowed_module) = self.allowlist_origin_for_name(macro_name) {
            if allowed_module != current_module {
                let message = format!(
                    "Macro name '{}' is allowlisted for module '{}', but was redefined in module '{}'; this redefinition will not inherit macro-boundary privileges.",
                    macro_name, allowed_module, current_module
                );
                self.pending_diagnostics.push(
                    Diagnostic::warning(message)
                        .with_code(CODE_EXPANSION_ALLOWLIST_REDEF)
                        .with_span(span),
                );
            }
        }
    }

    fn collect_macro_boundary_hits(syntax: &Syntax, hits: &mut BTreeSet<MacroBoundaryKind>) {
        match &syntax.kind {
            SyntaxKind::List(list) => {
                Self::collect_macro_boundary_hits_in_list(list, hits);
                for item in list {
                    Self::collect_macro_boundary_hits(item, hits);
                }
            }
            SyntaxKind::BracedList(list) => {
                Self::collect_macro_boundary_hits_in_list(list, hits);
                for item in list {
                    Self::collect_macro_boundary_hits(item, hits);
                }
            }
            SyntaxKind::Index(base, index) => {
                Self::collect_macro_boundary_hits(base, hits);
                Self::collect_macro_boundary_hits(index, hits);
            }
            _ => {}
        }
    }

    fn collect_macro_boundary_hits_in_list(
        list: &[Syntax],
        hits: &mut BTreeSet<MacroBoundaryKind>,
    ) {
        if list.is_empty() {
            return;
        }

        let head = match &list[0].kind {
            SyntaxKind::Symbol(s) => s.as_str(),
            _ => return,
        };

        match head {
            "unsafe" => {
                if list.len() >= 3 {
                    hits.insert(MacroBoundaryKind::UnsafeForm);
                }
            }
            "eval" => {
                hits.insert(MacroBoundaryKind::Eval);
            }
            "import" => {
                if list.len() >= 2 {
                    if let SyntaxKind::Symbol(tag) = &list[1].kind {
                        if tag == "classical" {
                            hits.insert(MacroBoundaryKind::ClassicalImport);
                        }
                    }
                }
            }
            "axiom" => {
                let mut tagged = false;
                if list.len() >= 4 {
                    tagged = Self::collect_axiom_tag_hits(&list[1], hits);
                }
                if !tagged {
                    hits.insert(MacroBoundaryKind::Axiom);
                }
            }
            _ => {}
        }
    }

    fn collect_axiom_tag_hits(tag_node: &Syntax, hits: &mut BTreeSet<MacroBoundaryKind>) -> bool {
        let mut inserted = false;
        match &tag_node.kind {
            SyntaxKind::Symbol(tag) => {
                inserted |= Self::maybe_insert_axiom_tag_hit(tag, hits);
            }
            SyntaxKind::List(items) | SyntaxKind::BracedList(items) => {
                for item in items {
                    if let SyntaxKind::Symbol(tag) = &item.kind {
                        inserted |= Self::maybe_insert_axiom_tag_hit(tag, hits);
                    }
                }
            }
            _ => {}
        }
        inserted
    }

    fn maybe_insert_axiom_tag_hit(tag: &str, hits: &mut BTreeSet<MacroBoundaryKind>) -> bool {
        match tag {
            "classical" => {
                hits.insert(MacroBoundaryKind::ClassicalAxiom);
                true
            }
            "unsafe" => {
                hits.insert(MacroBoundaryKind::UnsafeAxiom);
                true
            }
            _ => false,
        }
    }

    fn resolve_macro(&self, name: &str) -> Option<MacroDef> {
        let env = self.modules.get(&self.current_module)?;
        if let Some(def) = env.macros.get(name) {
            return Some(def.clone());
        }
        for import in &env.imports {
            if let Some(import_env) = self.modules.get(import) {
                if let Some(def) = import_env.macros.get(name) {
                    return Some(def.clone());
                }
            }
        }
        None
    }

    fn expand_quasiquote_internal(
        &mut self,
        syntax: &Syntax,
        limit: ExpansionLimit,
        state: &mut ExpansionState<'_>,
        macro_depth: usize,
    ) -> Result<Option<Syntax>, ExpansionError> {
        self.expand_quasiquote_with_depth(syntax, limit, state, macro_depth, 1)
    }

    fn expand_quasiquote_with_depth(
        &mut self,
        syntax: &Syntax,
        limit: ExpansionLimit,
        state: &mut ExpansionState<'_>,
        macro_depth: usize,
        quasiquote_depth: usize,
    ) -> Result<Option<Syntax>, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::List(list) => {
                if !list.is_empty() {
                    if let SyntaxKind::Symbol(s) = &list[0].kind {
                        if s == "quasiquote" {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "quasiquote".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            let inner = self
                                .expand_quasiquote_with_depth(
                                    &list[1],
                                    limit,
                                    state,
                                    macro_depth,
                                    quasiquote_depth + 1,
                                )?
                                .ok_or(ExpansionError::InvalidSyntax(
                                    "quasiquote".to_string(),
                                    "Nested quasiquote expansion failed".to_string(),
                                ))?;
                            return Ok(Some(Syntax {
                                kind: SyntaxKind::List(vec![list[0].clone(), inner]),
                                span: syntax.span,
                                scopes: syntax.scopes.clone(),
                            }));
                        }

                        if s == "unquote" {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "unquote".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            if quasiquote_depth == 1 {
                                return self
                                    .expand_macros_internal(
                                        list[1].clone(),
                                        limit,
                                        state,
                                        macro_depth,
                                    )?
                                    .ok_or(ExpansionError::InvalidSyntax(
                                        "unquote".to_string(),
                                        "Expression expanded to empty".to_string(),
                                    ))
                                    .map(Some);
                            }
                            let inner = self
                                .expand_quasiquote_with_depth(
                                    &list[1],
                                    limit,
                                    state,
                                    macro_depth,
                                    quasiquote_depth - 1,
                                )?
                                .ok_or(ExpansionError::InvalidSyntax(
                                    "unquote".to_string(),
                                    "Nested unquote expansion failed".to_string(),
                                ))?;
                            return Ok(Some(Syntax {
                                kind: SyntaxKind::List(vec![list[0].clone(), inner]),
                                span: syntax.span,
                                scopes: syntax.scopes.clone(),
                            }));
                        }

                        if s == "unquote-splicing" {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "unquote-splicing".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            if quasiquote_depth == 1 {
                                return Err(ExpansionError::InvalidSyntax(
                                    "unquote-splicing".to_string(),
                                    "unquote-splicing is only valid within list contexts"
                                        .to_string(),
                                ));
                            }
                            let inner = self
                                .expand_quasiquote_with_depth(
                                    &list[1],
                                    limit,
                                    state,
                                    macro_depth,
                                    quasiquote_depth - 1,
                                )?
                                .ok_or(ExpansionError::InvalidSyntax(
                                    "unquote-splicing".to_string(),
                                    "Nested unquote-splicing expansion failed".to_string(),
                                ))?;
                            return Ok(Some(Syntax {
                                kind: SyntaxKind::List(vec![list[0].clone(), inner]),
                                span: syntax.span,
                                scopes: syntax.scopes.clone(),
                            }));
                        }
                    }
                }

                let mut new_items = Vec::new();
                for item in list {
                    if quasiquote_depth == 1 {
                        if let SyntaxKind::List(sub) = &item.kind {
                            if !sub.is_empty() {
                                if let SyntaxKind::Symbol(s) = &sub[0].kind {
                                    if s == "unquote-splicing" {
                                        if sub.len() != 2 {
                                            return Err(ExpansionError::ArgumentCountMismatch(
                                                "unquote-splicing".to_string(),
                                                1,
                                                sub.len() - 1,
                                            ));
                                        }
                                        let expanded = self
                                            .expand_macros_internal(
                                                sub[1].clone(),
                                                limit,
                                                state,
                                                macro_depth,
                                            )?
                                            .ok_or(ExpansionError::InvalidSyntax(
                                                "unquote-splicing".to_string(),
                                                "Expression expanded to empty".to_string(),
                                            ))?;
                                        match expanded.kind {
                                            SyntaxKind::List(items) => {
                                                new_items.extend(items);
                                            }
                                            SyntaxKind::BracedList(items) => {
                                                new_items.extend(items);
                                            }
                                            _ => {
                                                return Err(ExpansionError::InvalidSyntax(
                                                    "unquote-splicing".to_string(),
                                                    "Expected a list of syntax objects".to_string(),
                                                ));
                                            }
                                        }
                                        continue;
                                    }
                                }
                            }
                        }
                    }

                    let expanded_item = self
                        .expand_quasiquote_with_depth(
                            item,
                            limit,
                            state,
                            macro_depth,
                            quasiquote_depth,
                        )?
                        .ok_or(ExpansionError::InvalidSyntax(
                            "quasiquote".to_string(),
                            "Item expansion failed".to_string(),
                        ))?;
                    new_items.push(expanded_item);
                }

                Ok(Some(Syntax {
                    kind: SyntaxKind::List(new_items),
                    span: syntax.span,
                    scopes: syntax.scopes.clone(),
                }))
            }
            SyntaxKind::BracedList(list) => {
                let mut new_items = Vec::new();
                for item in list {
                    if quasiquote_depth == 1 {
                        if let SyntaxKind::List(sub) = &item.kind {
                            if !sub.is_empty() {
                                if let SyntaxKind::Symbol(s) = &sub[0].kind {
                                    if s == "unquote-splicing" {
                                        if sub.len() != 2 {
                                            return Err(ExpansionError::ArgumentCountMismatch(
                                                "unquote-splicing".to_string(),
                                                1,
                                                sub.len() - 1,
                                            ));
                                        }
                                        let expanded = self
                                            .expand_macros_internal(
                                                sub[1].clone(),
                                                limit,
                                                state,
                                                macro_depth,
                                            )?
                                            .ok_or(ExpansionError::InvalidSyntax(
                                                "unquote-splicing".to_string(),
                                                "Expression expanded to empty".to_string(),
                                            ))?;
                                        match expanded.kind {
                                            SyntaxKind::List(items) => {
                                                new_items.extend(items);
                                            }
                                            SyntaxKind::BracedList(items) => {
                                                new_items.extend(items);
                                            }
                                            _ => {
                                                return Err(ExpansionError::InvalidSyntax(
                                                    "unquote-splicing".to_string(),
                                                    "Expected a list of syntax objects".to_string(),
                                                ));
                                            }
                                        }
                                        continue;
                                    }
                                }
                            }
                        }
                    }

                    let expanded_item = self
                        .expand_quasiquote_with_depth(
                            item,
                            limit,
                            state,
                            macro_depth,
                            quasiquote_depth,
                        )?
                        .ok_or(ExpansionError::InvalidSyntax(
                            "quasiquote".to_string(),
                            "Item expansion failed".to_string(),
                        ))?;
                    new_items.push(expanded_item);
                }

                Ok(Some(Syntax {
                    kind: SyntaxKind::BracedList(new_items),
                    span: syntax.span,
                    scopes: syntax.scopes.clone(),
                }))
            }
            SyntaxKind::Index(base, index) => {
                let new_base = self
                    .expand_quasiquote_with_depth(
                        base,
                        limit,
                        state,
                        macro_depth,
                        quasiquote_depth,
                    )?
                    .ok_or(ExpansionError::InvalidSyntax(
                        "quasiquote".to_string(),
                        "Index base expansion failed".to_string(),
                    ))?;
                let new_index = self
                    .expand_quasiquote_with_depth(
                        index,
                        limit,
                        state,
                        macro_depth,
                        quasiquote_depth,
                    )?
                    .ok_or(ExpansionError::InvalidSyntax(
                        "quasiquote".to_string(),
                        "Index expression expansion failed".to_string(),
                    ))?;
                Ok(Some(Syntax {
                    kind: SyntaxKind::Index(Box::new(new_base), Box::new(new_index)),
                    span: syntax.span,
                    scopes: syntax.scopes.clone(),
                }))
            }
            _ => Ok(Some(syntax.clone())),
        }
    }

    fn expand_macros_internal(
        &mut self,
        syntax: Syntax,
        limit: ExpansionLimit,
        state: &mut ExpansionState<'_>,
        depth: usize,
    ) -> Result<Option<Syntax>, ExpansionError> {
        if state.single_step_done(limit) {
            return Ok(Some(syntax));
        }

        match &syntax.kind {
            SyntaxKind::List(list) => {
                if list.is_empty() {
                    return Ok(Some(Syntax {
                        kind: SyntaxKind::List(vec![]),
                        ..syntax.clone()
                    }));
                }

                if let SyntaxKind::Symbol(s) = &list[0].kind {
                    if s == "quote" {
                        return Ok(Some(syntax.clone()));
                    }

                    if s == "quasiquote" {
                        if list.len() != 2 {
                            return Err(ExpansionError::ArgumentCountMismatch(
                                "quasiquote".to_string(),
                                1,
                                list.len() - 1,
                            ));
                        }
                        if limit == ExpansionLimit::SingleStep {
                            return Ok(Some(syntax.clone()));
                        }
                        return self.expand_quasiquote_internal(&list[1], limit, state, depth);
                    }

                    if s == "defmacro" {
                        if list.len() != 4 {
                            return Err(ExpansionError::ArgumentCountMismatch(
                                "defmacro".to_string(),
                                3,
                                list.len() - 1,
                            ));
                        }

                        let name = if let SyntaxKind::Symbol(s) = &list[1].kind {
                            s.clone()
                        } else {
                            return Err(ExpansionError::InvalidSyntax(
                                "defmacro".to_string(),
                                "Name must be a symbol".to_string(),
                            ));
                        };
                        if is_reserved_macro_name(&name) {
                            return Err(ExpansionError::InvalidSyntax(
                                "defmacro".to_string(),
                                format!("'{}' is a reserved macro name", name),
                            ));
                        }

                        let mut args = Vec::new();
                        if let SyntaxKind::List(arg_list) = &list[2].kind {
                            for arg in arg_list {
                                if let SyntaxKind::Symbol(a) = &arg.kind {
                                    args.push(a.clone());
                                } else {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "defmacro".to_string(),
                                        "Arguments must be symbols".to_string(),
                                    ));
                                }
                            }
                        } else {
                            return Err(ExpansionError::InvalidSyntax(
                                "defmacro".to_string(),
                                "Argument list expected".to_string(),
                            ));
                        }

                        let body = list[3].clone();
                        self.record_allowlist_redefinition_warning(&name, syntax.span);
                        self.add_macro(name, args, body);

                        if limit == ExpansionLimit::SingleStep {
                            state.mark_expanded();
                        }

                        return Ok(None);
                    }

                    if is_reserved_macro_name(s) {
                        // Reserved forms are not macro-expandable; expand their arguments only.
                    } else if let Some(def) = self.resolve_macro(s) {
                        let args = list[1..].to_vec();
                        let call_key = self.macro_call_key(s, &args);

                        if limit == ExpansionLimit::Full {
                            if let Some(cached) = self.expansion_cache.get(&call_key).cloned() {
                                if state.trace_enabled {
                                    state.trace.push(MacroTraceEntry {
                                        name: s.clone(),
                                        span: syntax.span,
                                        depth,
                                    });
                                }
                                self.check_macro_boundary(
                                    s,
                                    &def.origin_module,
                                    syntax.span,
                                    &cached,
                                )?;
                                return Ok(Some(cached));
                            }
                        }

                        if self.active_macro_keys.contains(&call_key) {
                            let cycle = self.macro_cycle_from_key(&call_key, s);
                            self.record_expansion_cycle_diagnostic(syntax.span, &cycle);
                            return Err(ExpansionError::MacroExpansionCycle { cycle });
                        }

                        if state.trace_enabled {
                            state.trace.push(MacroTraceEntry {
                                name: s.clone(),
                                span: syntax.span,
                                depth,
                            });
                        }

                        self.expansion_trace.push((s.clone(), syntax.span));
                        self.active_macro_keys.insert(call_key.clone());
                        self.macro_call_stack.push(MacroCallFrame {
                            key: call_key.clone(),
                            name: s.clone(),
                            span: syntax.span,
                        });

                        let result = (|| -> Result<Option<Syntax>, ExpansionError> {
                            if depth >= self.expansion_depth_limit {
                                let message = format!(
                                    "Macro expansion depth limit exceeded (limit {}). Possible recursive macro expansion.",
                                    self.expansion_depth_limit
                                );
                                self.record_expansion_limit_diagnostic(syntax.span, message);
                                return Err(ExpansionError::ExpansionDepthLimitExceeded {
                                    limit: self.expansion_depth_limit,
                                });
                            }

                            if !state.budget.consume() {
                                let message = format!(
                                    "Macro expansion step limit exceeded (limit {}). Possible recursive macro expansion.",
                                    state.budget.limit
                                );
                                self.record_expansion_limit_diagnostic(syntax.span, message);
                                return Err(ExpansionError::ExpansionStepLimitExceeded {
                                    limit: state.budget.limit,
                                });
                            }

                            let expanded = self.substitute_macro_args(&def, &args, syntax.span)?;

                            if limit == ExpansionLimit::SingleStep {
                                self.check_macro_boundary(
                                    s,
                                    &def.origin_module,
                                    syntax.span,
                                    &expanded,
                                )?;
                                state.mark_expanded();
                                return Ok(Some(expanded));
                            }

                            let res =
                                self.expand_macros_internal(expanded, limit, state, depth + 1)?;

                            if let Some(expanded_full) = &res {
                                self.check_macro_boundary(
                                    s,
                                    &def.origin_module,
                                    syntax.span,
                                    expanded_full,
                                )?;
                                self.expansion_cache
                                    .insert(call_key.clone(), expanded_full.clone());
                            }

                            Ok(res)
                        })();

                        self.macro_call_stack.pop();
                        self.active_macro_keys.remove(&call_key);
                        self.expansion_trace.pop();

                        return result;
                    }
                }

                let mut new_list = Vec::new();
                for item in list.iter() {
                    let expanded_item = if state.single_step_done(limit) {
                        Some(item.clone())
                    } else {
                        self.expand_macros_internal(item.clone(), limit, state, depth)?
                    };
                    if let Some(expanded_item) = expanded_item {
                        new_list.push(expanded_item);
                    }
                }

                Ok(Some(Syntax {
                    kind: SyntaxKind::List(new_list),
                    ..syntax.clone()
                }))
            }
            SyntaxKind::BracedList(list) => {
                let mut new_list = Vec::new();
                for item in list.iter() {
                    let expanded_item = if state.single_step_done(limit) {
                        Some(item.clone())
                    } else {
                        self.expand_macros_internal(item.clone(), limit, state, depth)?
                    };
                    if let Some(expanded_item) = expanded_item {
                        new_list.push(expanded_item);
                    }
                }

                Ok(Some(Syntax {
                    kind: SyntaxKind::BracedList(new_list),
                    ..syntax.clone()
                }))
            }
            SyntaxKind::Index(base, index) => {
                let new_base = if state.single_step_done(limit) {
                    Some((**base).clone())
                } else {
                    self.expand_macros_internal((**base).clone(), limit, state, depth)?
                }
                .ok_or(ExpansionError::InvalidSyntax(
                    "index".to_string(),
                    "Index base expanded to empty".to_string(),
                ))?;
                let new_index = if state.single_step_done(limit) {
                    Some((**index).clone())
                } else {
                    self.expand_macros_internal((**index).clone(), limit, state, depth)?
                }
                .ok_or(ExpansionError::InvalidSyntax(
                    "index".to_string(),
                    "Index expression expanded to empty".to_string(),
                ))?;

                Ok(Some(Syntax {
                    kind: SyntaxKind::Index(Box::new(new_base), Box::new(new_index)),
                    ..syntax.clone()
                }))
            }
            _ => Ok(Some(syntax.clone())),
        }
    }

    pub fn expand_all_macros(&mut self, syntax: Syntax) -> Result<Option<Syntax>, ExpansionError> {
        self.last_env_version = Some(self.macro_env_version());
        self.begin_expansion_session();
        let mut trace = Vec::new();
        let mut did_expand = false;
        let mut budget = ExpansionBudget::new(self.expansion_step_limit);
        let mut state = ExpansionState::new(&mut budget, &mut trace, false, &mut did_expand);
        self.expand_macros_internal(syntax, ExpansionLimit::Full, &mut state, 0)
    }

    fn substitute_macro_args(
        &mut self,
        def: &MacroDef,
        args: &[Syntax],
        call_site_span: Span,
    ) -> Result<Syntax, ExpansionError> {
        if args.len() != def.args.len() {
            return Err(ExpansionError::ArgumentCountMismatch(
                "macro call".to_string(),
                def.args.len(),
                args.len(),
            ));
        }

        let macro_scope = self.new_scope();

        let mut subst_env = HashMap::new(); // Use HashMap for local subst, order doesn't matter as we lookup by name
        for (i, arg_name) in def.args.iter().enumerate() {
            subst_env.insert(arg_name.clone(), args[i].clone());
        }

        let substituted = Self::substitute_rec_with_scope(&def.body, &subst_env, macro_scope)?;
        Ok(Self::remap_spans_for_scope(
            &substituted,
            macro_scope,
            call_site_span,
        ))
    }

    fn substitute_rec_with_scope(
        syntax: &Syntax,
        subst_env: &HashMap<String, Syntax>,
        macro_scope: ScopeId,
    ) -> Result<Syntax, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::Symbol(s) => {
                if let Some(replacement) = subst_env.get(s) {
                    return Ok(replacement.clone());
                }
                Ok(Syntax {
                    kind: SyntaxKind::Symbol(s.clone()),
                    span: syntax.span,
                    scopes: scopes_with(&syntax.scopes, macro_scope),
                })
            }
            SyntaxKind::List(list) => {
                let new_list = list
                    .iter()
                    .map(|item| Self::substitute_rec_with_scope(item, subst_env, macro_scope))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Syntax {
                    kind: SyntaxKind::List(new_list),
                    span: syntax.span,
                    scopes: scopes_with(&syntax.scopes, macro_scope),
                })
            }
            SyntaxKind::BracedList(list) => {
                let new_list = list
                    .iter()
                    .map(|item| Self::substitute_rec_with_scope(item, subst_env, macro_scope))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Syntax {
                    kind: SyntaxKind::BracedList(new_list),
                    span: syntax.span,
                    scopes: scopes_with(&syntax.scopes, macro_scope),
                })
            }
            SyntaxKind::Index(base, index) => {
                let new_base = Self::substitute_rec_with_scope(base, subst_env, macro_scope)?;
                let new_index = Self::substitute_rec_with_scope(index, subst_env, macro_scope)?;
                Ok(Syntax {
                    kind: SyntaxKind::Index(Box::new(new_base), Box::new(new_index)),
                    span: syntax.span,
                    scopes: scopes_with(&syntax.scopes, macro_scope),
                })
            }
            _ => Ok(Syntax {
                scopes: scopes_with(&syntax.scopes, macro_scope),
                ..syntax.clone()
            }),
        }
    }

    fn remap_spans_for_scope(syntax: &Syntax, scope: ScopeId, call_site_span: Span) -> Syntax {
        let span = if syntax.scopes.contains(&scope) {
            call_site_span
        } else {
            syntax.span
        };

        let kind = match &syntax.kind {
            SyntaxKind::List(list) => SyntaxKind::List(
                list.iter()
                    .map(|item| Self::remap_spans_for_scope(item, scope, call_site_span))
                    .collect(),
            ),
            SyntaxKind::BracedList(list) => SyntaxKind::BracedList(
                list.iter()
                    .map(|item| Self::remap_spans_for_scope(item, scope, call_site_span))
                    .collect(),
            ),
            SyntaxKind::Index(base, index) => SyntaxKind::Index(
                Box::new(Self::remap_spans_for_scope(base, scope, call_site_span)),
                Box::new(Self::remap_spans_for_scope(index, scope, call_site_span)),
            ),
            _ => syntax.kind.clone(),
        };

        Syntax {
            kind,
            span,
            scopes: syntax.scopes.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn parse_single(input: &str) -> Syntax {
        let mut parser = Parser::new(input);
        let mut nodes = parser.parse().expect("parse should succeed");
        assert_eq!(nodes.len(), 1, "expected a single syntax node");
        nodes.remove(0)
    }

    #[test]
    fn transitive_import_change_invalidates_expansion_cache() {
        let mut expander = Expander::new();

        expander.enter_module("c");
        expander.add_macro("leaf".to_string(), vec![], parse_single("1"));

        expander.enter_module("b");
        expander.import_module("c".to_string());

        expander.enter_module("a");
        expander.import_module("b".to_string());
        expander.add_macro("id".to_string(), vec!["x".to_string()], parse_single("x"));

        let call = parse_single("(id 0)");
        let _ = expander
            .expand_all_macros(call)
            .expect("macro expansion should succeed")
            .expect("macro call should produce syntax");
        assert!(
            !expander.expansion_cache.is_empty(),
            "expansion cache should be populated after macro expansion"
        );

        expander
            .expansion_cache
            .insert("sentinel".to_string(), parse_single("999"));
        let before = expander.macro_env_fingerprint();

        expander.enter_module("c");
        expander.add_macro("leaf".to_string(), vec![], parse_single("2"));

        expander.enter_module("a");
        let after = expander.macro_env_fingerprint();
        assert_ne!(
            before, after,
            "changing module C must change A's transitive env fingerprint"
        );

        expander.begin_expansion_session();
        assert!(
            !expander.expansion_cache.contains_key("sentinel"),
            "cache entries must be cleared when transitive fingerprint changes"
        );
        assert_eq!(
            expander.expansion_cache_env_fingerprint.as_deref(),
            Some(after.as_str())
        );
    }

    fn build_equivalent_graph_order_a() -> Expander {
        let mut expander = Expander::new();

        expander.enter_module("c");
        expander.add_macro("leaf".to_string(), vec![], parse_single("1"));

        expander.enter_module("b");
        expander.import_module("c".to_string());

        expander.enter_module("a");
        expander.import_module("b".to_string());

        expander
    }

    fn build_equivalent_graph_order_b() -> Expander {
        let mut expander = Expander::new();

        expander.enter_module("b");
        expander.import_module("c".to_string());

        expander.enter_module("a");
        expander.import_module("b".to_string());

        expander.enter_module("c");
        expander.add_macro("leaf".to_string(), vec![], parse_single("1"));

        expander
    }

    #[test]
    fn macro_env_fingerprint_is_deterministic_for_equivalent_graphs() {
        let mut first = build_equivalent_graph_order_a();
        first.enter_module("a");
        let first_fingerprint = first.macro_env_fingerprint();

        let mut second = build_equivalent_graph_order_b();
        second.enter_module("a");
        let second_fingerprint = second.macro_env_fingerprint();

        assert_eq!(
            first_fingerprint, second_fingerprint,
            "equivalent module graphs must produce identical fingerprints"
        );
    }
}
