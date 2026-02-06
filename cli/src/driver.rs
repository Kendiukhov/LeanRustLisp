use frontend::declaration_parser::{DeclarationParseError, DeclarationParser};
use frontend::diagnostics::{Diagnostic, DiagnosticCollector, DiagnosticHandler};
use frontend::elaborator::{ElabError, Elaborator};
use frontend::macro_expander::{Expander, ExpansionError};
use frontend::parser::{ParseError, Parser};
use frontend::surface::{Declaration, Span, SurfaceTerm, SurfaceTermKind, Syntax, SyntaxKind};
use kernel::ast::{
    is_reserved_primitive_name, AxiomTag, BinderInfo, Constructor, CopyInstance,
    CopyInstanceSource, Definition, DefinitionKind, InductiveDecl, Level as KernelLevel, Term,
    Totality, Transparency,
};
use kernel::checker::{Context, Env};
use mir;
use mir::errors::{MirSpan, MirSpanMap, SourceSpan};
use std::collections::{BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

const CODE_DRIVER_MACRO_IMPORT_MISSING: &str = "C0001";
const CODE_DRIVER_MACRO_IMPORT_CYCLE: &str = "C0002";
const CODE_DRIVER_MACRO_IMPORT_READ: &str = "C0003";
const CODE_DRIVER_EVAL_BLOCKED: &str = "C0004";
const CODE_DRIVER_INTERIOR_MUTABILITY_GATED: &str = "C0005";
const CODE_DRIVER_LINT_PANIC_FREE: &str = "C0006";
const CODE_DRIVER_MACRO_IMPORT_FORM: &str = "C0007";

#[derive(Debug)]
pub enum DriverError {
    ParseValidations(Vec<String>),
    ElaborationErrors(Vec<String>),
    IoError(std::io::Error),
    Other(String),
}

pub fn module_id_for_source(filename: &str) -> String {
    if filename == "repl" || filename == "<repl>" {
        return "repl".to_string();
    }
    module_id_from_path(Path::new(filename))
}

fn module_id_from_path(path: &Path) -> String {
    match fs::canonicalize(path) {
        Ok(canon) => canon.to_string_lossy().to_string(),
        Err(_) => path.to_string_lossy().to_string(),
    }
}

fn resolve_import_path(base_filename: &str, import_path: &str) -> PathBuf {
    let base = Path::new(base_filename);
    let import = Path::new(import_path);
    if import.is_absolute() {
        import.to_path_buf()
    } else {
        let base_dir = base.parent().unwrap_or_else(|| Path::new("."));
        base_dir.join(import)
    }
}

pub(crate) fn apply_macro_imports(
    expander: &mut Expander,
    module_id: &str,
    syntax_nodes: Vec<Syntax>,
    diagnostics: &mut DiagnosticCollector,
) -> Result<Vec<Syntax>, DriverError> {
    expander.enter_module(module_id.to_string());

    let (syntax_nodes, imports) = extract_macro_imports(syntax_nodes, expander, diagnostics);
    if diagnostics.has_errors() {
        return Err(DriverError::ParseValidations(vec![
            "Macro import error".to_string()
        ]));
    }

    let mut loading = BTreeSet::new();
    for (import_path, span) in imports {
        let resolved = resolve_import_path(module_id, &import_path);
        if !resolved.exists() {
            handle_diagnostic(
                diagnostics,
                expander,
                Diagnostic::error(format!("Macro import '{}' not found", import_path))
                    .with_code(CODE_DRIVER_MACRO_IMPORT_MISSING)
                    .with_span(span),
            );
            return Err(DriverError::Other("Macro import not found".to_string()));
        }
        let import_id = load_macro_module(&resolved, expander, diagnostics, &mut loading)?;
        expander.import_module(import_id);
    }

    Ok(syntax_nodes)
}

fn handle_diagnostic(
    diagnostics: &mut DiagnosticCollector,
    expander: &mut Expander,
    diagnostic: Diagnostic,
) {
    let trace = expander.take_expansion_trace();
    if trace.is_empty() {
        diagnostics.handle(diagnostic);
        return;
    }

    let mut diagnostic = diagnostic;
    if let Some(last) = trace.last() {
        diagnostic = diagnostic.with_span(last.span);
    }
    for entry in trace {
        diagnostic = diagnostic.with_label(entry.span, format!("macro expansion: {}", entry.name));
    }

    diagnostics.handle(diagnostic);
}

fn drain_macro_diagnostics(expander: &mut Expander, diagnostics: &mut DiagnosticCollector) {
    for diagnostic in expander.take_pending_diagnostics() {
        diagnostics.handle(diagnostic);
    }
}

fn to_mir_span(span: Span) -> SourceSpan {
    SourceSpan {
        start: span.start,
        end: span.end,
        line: span.line,
        col: span.col,
    }
}

fn to_frontend_span(span: SourceSpan) -> Span {
    Span {
        start: span.start,
        end: span.end,
        line: span.line,
        col: span.col,
    }
}

fn build_term_span_map(elab: &Elaborator) -> mir::lower::TermSpanMap {
    let spans_by_id = elab
        .span_map()
        .iter()
        .map(|(id, span)| (id.0, to_mir_span(*span)))
        .collect();
    let term_ids_by_ptr = elab
        .term_id_map()
        .iter()
        .map(|(ptr, id)| (*ptr, id.0))
        .collect();
    mir::lower::TermSpanMap::new(spans_by_id, term_ids_by_ptr)
}

fn span_for_mir_location(location: Option<MirSpan>, span_table: &MirSpanMap) -> Option<Span> {
    location
        .and_then(|loc| span_table.get(&loc).copied())
        .map(to_frontend_span)
}

fn diagnostic_from_parse_error(err: &ParseError) -> Diagnostic {
    Diagnostic::error(format!("Parse error: {:?}", err))
        .with_code(err.diagnostic_code())
        .with_span(err.span())
}

fn diagnostic_from_decl_parse_error(err: &DeclarationParseError) -> Diagnostic {
    let mut diagnostic = Diagnostic::error(format!("Declaration parsing error: {:?}", err))
        .with_code(err.diagnostic_code());
    if let Some(span) = err.span() {
        diagnostic = diagnostic.with_span(span);
    }
    diagnostic
}

fn diagnostic_from_elab_error(context: &str, err: &ElabError) -> Diagnostic {
    let mut diagnostic = Diagnostic::error(format!("{}: {}", context, format_elab_error(err)))
        .with_code(err.diagnostic_code());
    if let Some(span) = err.span() {
        diagnostic = diagnostic.with_span(span);
    }
    diagnostic
}

fn attach_elab_metadata(mut diagnostic: Diagnostic, err: &ElabError) -> Diagnostic {
    diagnostic = diagnostic.with_code(err.diagnostic_code());
    if let Some(span) = err.span() {
        diagnostic = diagnostic.with_span(span);
    }
    diagnostic
}

fn diagnostic_from_kernel_error(
    context: &str,
    err: &kernel::checker::TypeError,
    span: Option<Span>,
) -> Diagnostic {
    let mut diagnostic = Diagnostic::error(format!("{}: {}", context, format_kernel_error(err)))
        .with_code(err.diagnostic_code());
    if let Some(span) = span {
        diagnostic = diagnostic.with_span(span);
    }
    diagnostic
}

fn reject_reserved_primitive_name(
    env: &Env,
    name: &str,
    expander: &mut Expander,
    diagnostics: &mut DiagnosticCollector,
) -> bool {
    if is_reserved_primitive_name(name) && !env.allows_reserved_primitives() {
        handle_diagnostic(
            diagnostics,
            expander,
            Diagnostic::error(format!(
                "Reserved primitive name '{}' can only be declared in the prelude as an axiom",
                name
            )),
        );
        return true;
    }
    false
}

fn reject_reserved_primitive_inductive(
    name: &str,
    expander: &mut Expander,
    diagnostics: &mut DiagnosticCollector,
) -> bool {
    if is_reserved_primitive_name(name) {
        handle_diagnostic(
            diagnostics,
            expander,
            Diagnostic::error(format!(
                "Reserved primitive name '{}' must be a prelude axiom, not an inductive declaration",
                name
            )),
        );
        return true;
    }
    false
}

fn reject_redefinition(
    env: &Env,
    name: &str,
    kind: &str,
    options: &PipelineOptions,
    expander: &mut Expander,
    diagnostics: &mut DiagnosticCollector,
) -> bool {
    if !options.prelude_frozen || options.allow_redefine {
        return false;
    }
    if env.get_definition(name).is_some() || env.get_inductive(name).is_some() {
        handle_diagnostic(
            diagnostics,
            expander,
            Diagnostic::error(format!(
                "Cannot redefine {} '{}': prelude is frozen (use --allow-redefine to override)",
                kind, name
            )),
        );
        return true;
    }
    false
}

fn extract_macro_imports(
    syntax_nodes: Vec<Syntax>,
    expander: &mut Expander,
    diagnostics: &mut DiagnosticCollector,
) -> (Vec<Syntax>, Vec<(String, Span)>) {
    let mut retained = Vec::new();
    let mut imports = Vec::new();

    for node in syntax_nodes {
        let items = match &node.kind {
            SyntaxKind::List(items) if !items.is_empty() => items,
            _ => {
                retained.push(node);
                continue;
            }
        };

        let head = match &items[0].kind {
            SyntaxKind::Symbol(s) if s == "import-macros" => s.as_str(),
            _ => {
                retained.push(node);
                continue;
            }
        };

        if items.len() < 2 {
            handle_diagnostic(
                diagnostics,
                expander,
                Diagnostic::error(format!("{} expects at least one string path", head))
                    .with_code(CODE_DRIVER_MACRO_IMPORT_FORM)
                    .with_span(node.span),
            );
            continue;
        }

        for arg in &items[1..] {
            match &arg.kind {
                SyntaxKind::String(path) => imports.push((path.clone(), arg.span)),
                _ => handle_diagnostic(
                    diagnostics,
                    expander,
                    Diagnostic::error(format!("{} expects string paths", head))
                        .with_code(CODE_DRIVER_MACRO_IMPORT_FORM)
                        .with_span(arg.span),
                ),
            }
        }
    }

    (retained, imports)
}

fn parse_defmacro_syntax(
    syntax: &Syntax,
) -> Result<Option<(String, Vec<String>, Syntax)>, ExpansionError> {
    let items = match &syntax.kind {
        SyntaxKind::List(items) if !items.is_empty() => items,
        _ => return Ok(None),
    };

    let head = match &items[0].kind {
        SyntaxKind::Symbol(s) if s == "defmacro" => s.as_str(),
        _ => return Ok(None),
    };

    if items.len() != 4 {
        return Err(ExpansionError::ArgumentCountMismatch(
            head.to_string(),
            3,
            items.len() - 1,
        ));
    }

    let name = if let SyntaxKind::Symbol(n) = &items[1].kind {
        n.clone()
    } else {
        return Err(ExpansionError::InvalidSyntax(
            head.to_string(),
            "Name must be a symbol".to_string(),
        ));
    };

    let mut args = Vec::new();
    if let SyntaxKind::List(arg_list) = &items[2].kind {
        for arg in arg_list {
            if let SyntaxKind::Symbol(a) = &arg.kind {
                args.push(a.clone());
            } else {
                return Err(ExpansionError::InvalidSyntax(
                    head.to_string(),
                    "Args must be symbols".to_string(),
                ));
            }
        }
    } else {
        return Err(ExpansionError::InvalidSyntax(
            head.to_string(),
            "Arg list expected".to_string(),
        ));
    }

    let body = items[3].clone();
    Ok(Some((name, args, body)))
}

fn load_macro_module(
    module_path: &Path,
    expander: &mut Expander,
    diagnostics: &mut DiagnosticCollector,
    loading: &mut BTreeSet<String>,
) -> Result<String, DriverError> {
    let module_id = module_id_from_path(module_path);
    if expander.is_module_loaded(&module_id) {
        return Ok(module_id);
    }

    if loading.contains(&module_id) {
        handle_diagnostic(
            diagnostics,
            expander,
            Diagnostic::error(format!("Macro import cycle detected at '{}'", module_id))
                .with_code(CODE_DRIVER_MACRO_IMPORT_CYCLE),
        );
        return Err(DriverError::Other("Macro import cycle".to_string()));
    }

    let content = match fs::read_to_string(module_path) {
        Ok(content) => content,
        Err(err) => {
            handle_diagnostic(
                diagnostics,
                expander,
                Diagnostic::error(format!(
                    "Failed to read macro import '{}': {:?}",
                    module_path.to_string_lossy(),
                    err
                ))
                .with_code(CODE_DRIVER_MACRO_IMPORT_READ),
            );
            return Err(DriverError::IoError(err));
        }
    };

    loading.insert(module_id.clone());
    let prev_module = expander.current_module().to_string();
    expander.enter_module(module_id.clone());

    let mut parser = Parser::new(&content);
    let syntax_nodes = match parser.parse() {
        Ok(nodes) => nodes,
        Err(e) => {
            let diagnostic = Diagnostic::error(format!(
                "Parse error in macro import '{}': {:?}",
                module_path.to_string_lossy(),
                e
            ))
            .with_code(e.diagnostic_code())
            .with_span(e.span());
            handle_diagnostic(diagnostics, expander, diagnostic);
            expander.enter_module(prev_module);
            loading.remove(&module_id);
            return Err(DriverError::ParseValidations(vec![format!("{:?}", e)]));
        }
    };

    let (syntax_nodes, imports) = extract_macro_imports(syntax_nodes, expander, diagnostics);
    if diagnostics.has_errors() {
        expander.enter_module(prev_module);
        loading.remove(&module_id);
        return Err(DriverError::Other("Macro import error".to_string()));
    }

    for (import_path, span) in imports {
        let resolved = resolve_import_path(&module_id, &import_path);
        if !resolved.exists() {
            handle_diagnostic(
                diagnostics,
                expander,
                Diagnostic::error(format!("Macro import '{}' not found", import_path))
                    .with_code(CODE_DRIVER_MACRO_IMPORT_MISSING)
                    .with_span(span),
            );
            expander.enter_module(prev_module);
            loading.remove(&module_id);
            return Err(DriverError::Other("Macro import not found".to_string()));
        }
        let import_id = load_macro_module(&resolved, expander, diagnostics, loading)?;
        expander.import_module(import_id);
    }

    for node in syntax_nodes {
        let node_span = node.span;
        match parse_defmacro_syntax(&node) {
            Ok(Some((name, args, body))) => {
                expander.add_macro(name, args, body);
                continue;
            }
            Ok(None) => {}
            Err(err) => {
                let diagnostic = Diagnostic::error(format!(
                    "Macro import error in '{}': {}",
                    module_path.to_string_lossy(),
                    err
                ))
                .with_code(err.diagnostic_code())
                .with_span(node_span);
                handle_diagnostic(diagnostics, expander, diagnostic);
                expander.enter_module(prev_module);
                loading.remove(&module_id);
                return Err(DriverError::Other("Macro import error".to_string()));
            }
        }

        let expanded = match expander.expand(node) {
            Ok(res) => res,
            Err(err) => {
                let diagnostic = Diagnostic::error(format!(
                    "Macro expansion failed in import '{}': {}",
                    module_path.to_string_lossy(),
                    err
                ))
                .with_code(err.diagnostic_code())
                .with_span(node_span);
                handle_diagnostic(diagnostics, expander, diagnostic);
                expander.enter_module(prev_module);
                loading.remove(&module_id);
                return Err(DriverError::Other(
                    "Macro import expansion failed".to_string(),
                ));
            }
        };
        drain_macro_diagnostics(expander, diagnostics);

        if let Some(expanded) = expanded {
            match parse_defmacro_syntax(&expanded) {
                Ok(Some((name, args, body))) => {
                    expander.add_macro(name, args, body);
                }
                Ok(None) => {}
                Err(err) => {
                    let diagnostic = Diagnostic::error(format!(
                        "Macro import error in '{}': {}",
                        module_path.to_string_lossy(),
                        err
                    ))
                    .with_code(err.diagnostic_code())
                    .with_span(expanded.span);
                    handle_diagnostic(diagnostics, expander, diagnostic);
                    expander.enter_module(prev_module);
                    loading.remove(&module_id);
                    return Err(DriverError::Other("Macro import error".to_string()));
                }
            }
        }
    }

    expander.mark_module_loaded(&module_id);
    expander.enter_module(prev_module);
    loading.remove(&module_id);
    Ok(module_id)
}

/// Compilation/Interpretation Options
pub struct PipelineOptions {
    pub show_types: bool,
    pub show_eval: bool,
    pub verbose: bool,
    pub collect_artifacts: bool,
    pub panic_free: bool,
    pub require_axiom_tags: bool,
    pub allow_axioms: bool,
    pub prelude_frozen: bool,
    pub allow_redefine: bool,
}

impl Default for PipelineOptions {
    fn default() -> Self {
        PipelineOptions {
            show_types: false,
            show_eval: false,
            verbose: false,
            collect_artifacts: false,
            panic_free: false,
            require_axiom_tags: false,
            allow_axioms: false,
            prelude_frozen: false,
            allow_redefine: false,
        }
    }
}

#[derive(Debug)]
pub enum Artifact {
    DefEqConfig {
        fuel: usize,
        source: String,
        transparency: Transparency,
    },
    ElaboratedDef {
        name: String,
        ty: String,
        val: String,
    },
    MirBody {
        name: String,
        body: String,
    },
    BorrowCheck {
        name: String,
        ownership_errors: Vec<String>,
        result: mir::analysis::nll::BorrowCheckResult,
    },
    AxiomDependencies {
        name: String,
        axioms: Vec<String>,
        classical: Vec<String>,
    },
}

/// The result of processing a chunk of code.
/// Contains the list of successfully elaborated definitions (for backend use).
pub struct ProcessingResult {
    pub deployed_definitions: Vec<String>, // Names of definitions added
    pub evaluated_terms: Vec<(Rc<Term>, Rc<Term>)>, // (Type, Value) of evaluated expressions
    pub artifacts: Vec<Artifact>,
    pub term_span_maps: HashMap<String, mir::lower::TermSpanMap>,
}

fn artifact_kind_order(artifact: &Artifact) -> u8 {
    match artifact {
        Artifact::DefEqConfig { .. } => 0,
        Artifact::ElaboratedDef { .. } => 1,
        Artifact::MirBody { .. } => 2,
        Artifact::BorrowCheck { .. } => 3,
        Artifact::AxiomDependencies { .. } => 4,
    }
}

fn artifact_name(artifact: &Artifact) -> &str {
    match artifact {
        Artifact::DefEqConfig { .. } => "",
        Artifact::ElaboratedDef { name, .. }
        | Artifact::MirBody { name, .. }
        | Artifact::BorrowCheck { name, .. }
        | Artifact::AxiomDependencies { name, .. } => name,
    }
}

fn sort_artifacts(artifacts: &mut Vec<Artifact>) {
    artifacts.sort_by(|a, b| {
        let key_a = (artifact_kind_order(a), artifact_name(a));
        let key_b = (artifact_kind_order(b), artifact_name(b));
        key_a.cmp(&key_b)
    });
}

fn rollback_failed_definition(
    env: &mut Env,
    env_snapshot: &Env,
    processed: &mut ProcessingResult,
    deployed_len: usize,
    artifacts_len: usize,
    name: &str,
    previous_term_span_map: Option<&mir::lower::TermSpanMap>,
) {
    *env = env_snapshot.clone();
    processed.deployed_definitions.truncate(deployed_len);
    processed.artifacts.truncate(artifacts_len);
    if let Some(previous) = previous_term_span_map {
        processed
            .term_span_maps
            .insert(name.to_string(), previous.clone());
    } else {
        processed.term_span_maps.remove(name);
    }
}

fn new_elaborator_with_imports<'a>(env: &'a Env, import_scopes: &[String]) -> Elaborator<'a> {
    let mut elab = Elaborator::new(env);
    elab.set_import_scopes(import_scopes.iter().cloned());
    elab
}

/// Unified Pipeline Driver
/// Takes source code, updates Env/Expander, and returns results/diagnostics.
pub fn process_code(
    source: &str,
    filename: &str,
    env: &mut Env,
    expander: &mut Expander,
    options: &PipelineOptions,
    diagnostics: &mut DiagnosticCollector,
) -> Result<ProcessingResult, DriverError> {
    let module_id = module_id_for_source(filename);

    let mut parser = Parser::new(source);
    let syntax_nodes = match parser.parse() {
        Ok(nodes) => nodes,
        Err(e) => {
            handle_diagnostic(diagnostics, expander, diagnostic_from_parse_error(&e));
            return Err(DriverError::ParseValidations(vec![format!("{:?}", e)]));
        }
    };

    let syntax_nodes = apply_macro_imports(expander, &module_id, syntax_nodes, diagnostics)?;

    let mut decl_parser = DeclarationParser::new(expander);
    let parse_result = decl_parser.parse(syntax_nodes);
    drop(decl_parser); // Release borrow of expander
    drain_macro_diagnostics(expander, diagnostics);

    let decls = match parse_result {
        Ok(decls) => decls,
        Err(e) => {
            handle_diagnostic(diagnostics, expander, diagnostic_from_decl_parse_error(&e));
            return Err(DriverError::ParseValidations(vec![format!("{:?}", e)]));
        }
    };

    let mut processed = ProcessingResult {
        deployed_definitions: Vec::new(),
        evaluated_terms: Vec::new(),
        artifacts: Vec::new(),
        term_span_maps: HashMap::new(),
    };

    if options.collect_artifacts {
        let policy = kernel::nbe::defeq_fuel_policy();
        processed.artifacts.push(Artifact::DefEqConfig {
            fuel: policy.fuel,
            source: policy.source.label().to_string(),
            transparency: Transparency::Reducible,
        });
    }

    let mut import_scopes: Vec<String> = Vec::new();

    for decl in decls {
        match decl {
            Declaration::Def {
                name,
                ty,
                val,
                totality,
                transparency,
                noncomputable,
            } => {
                let ty_span = ty.span;
                let val_span = val.span;
                if reject_reserved_primitive_name(env, &name, expander, diagnostics) {
                    continue;
                }
                if reject_redefinition(env, &name, "definition", options, expander, diagnostics) {
                    continue;
                }
                if totality != Totality::Partial {
                    if let Some(span) = val.find_fix_span().or_else(|| ty.find_fix_span()) {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            Diagnostic::error(format!(
                                "fix is only allowed in partial definitions; '{}' is {}",
                                name,
                                totality_label(totality)
                            ))
                            .with_span(span),
                        );
                        continue;
                    }
                }
                let mut elab = new_elaborator_with_imports(env, &import_scopes);

                // Infer Type
                let mut ty_core = match elab.infer_type(ty.clone()) {
                    Ok((t, s)) => {
                        // Ensure it's a type (Sort)
                        if !matches!(*s, Term::Sort(_)) {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                Diagnostic::error(format!(
                                    "Type of definition '{}' must be a Sort",
                                    name
                                ))
                                .with_span(ty_span),
                            );
                            continue;
                        }
                        let t = elab.instantiate_metas(&t);
                        if let Err(msg) = validate_core_invariants(&t) {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                Diagnostic::error(format!(
                                    "Type of definition '{}' violates core invariants: {}",
                                    name, msg
                                ))
                                .with_span(ty_span),
                            );
                            continue;
                        }
                        t
                    }
                    Err(e) => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            diagnostic_from_elab_error(
                                &format!("Elaboration error (Type) in '{}'", name),
                                &e,
                            ),
                        );
                        continue;
                    }
                };

                if totality == Totality::Partial {
                    let ctx = Context::new();
                    match kernel::checker::is_comp_return_type(env, &ctx, &ty_core) {
                        Ok(true) => {}
                        Ok(false) => {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                Diagnostic::error(format!(
                                    "Partial definition '{}' must return Comp A",
                                    name
                                ))
                                .with_span(ty.span),
                            );
                            continue;
                        }
                        Err(e) => {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                diagnostic_from_kernel_error(
                                    &format!("Failed to validate return type for '{}'", name),
                                    &e,
                                    Some(ty_span),
                                ),
                            );
                            continue;
                        }
                    }
                }

                // Check Value
                let val_core = match elab.check(val, &ty_core) {
                    Ok(t) => {
                        if let Err(e) = elab.solve_constraints() {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                attach_elab_metadata(
                                    Diagnostic::error(format!(
                                        "Unsolved constraints in '{}': {:?}",
                                        name, e
                                    )),
                                    &e,
                                ),
                            );
                            continue;
                        }
                        let t = elab.instantiate_metas(&t);
                        if let Err(msg) = validate_core_invariants(&t) {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                Diagnostic::error(format!(
                                    "Definition '{}' violates core invariants: {}",
                                    name, msg
                                ))
                                .with_span(val_span),
                            );
                            continue;
                        }
                        ty_core = elab.instantiate_metas(&ty_core);
                        t
                    }
                    Err(e) => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            diagnostic_from_elab_error(
                                &format!("Elaboration error (Value) in '{}'", name),
                                &e,
                            ),
                        );
                        continue;
                    }
                };

                let closure_ids = kernel::ownership::collect_closure_ids(&val_core, &name);
                let def_capture_modes = kernel::ownership::map_capture_modes_to_closures(
                    &closure_ids,
                    elab.capture_mode_map(),
                );

                // Kernel re-check to enforce the trusted kernel boundary.
                let ctx = Context::new();
                let ty_ty = match kernel::checker::infer(env, &ctx, ty_core.clone()) {
                    Ok(t) => t,
                    Err(e) => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            diagnostic_from_kernel_error(
                                &format!("Kernel re-check failed for type of '{}'", name),
                                &e,
                                Some(ty_span),
                            ),
                        );
                        continue;
                    }
                };
                let ty_ty_norm =
                    match kernel::checker::whnf(env, ty_ty, kernel::Transparency::Reducible) {
                        Ok(norm) => norm,
                        Err(e) => {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                diagnostic_from_kernel_error(
                                    &format!("Kernel re-check failed for type of '{}'", name),
                                    &e,
                                    Some(ty_span),
                                ),
                            );
                            continue;
                        }
                    };
                if !matches!(&*ty_ty_norm, Term::Sort(_)) {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        Diagnostic::error(format!(
                            "Kernel re-check failed for type of '{}': expected a Sort, got {:?}",
                            name, ty_ty_norm
                        ))
                        .with_span(ty_span),
                    );
                    continue;
                }
                if let Err(e) = kernel::checker::check(env, &ctx, val_core.clone(), ty_core.clone())
                {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        diagnostic_from_kernel_error(
                            &format!("Kernel re-check failed for '{}'", name),
                            &e,
                            Some(val_span),
                        ),
                    );
                    continue;
                }

                let term_span_map = Rc::new(build_term_span_map(&elab));
                let previous_term_span_map = processed
                    .term_span_maps
                    .insert(name.clone(), (*term_span_map).clone());

                // Add to Env
                let mut def = match totality {
                    Totality::Partial => kernel::ast::Definition::partial(
                        name.clone(),
                        ty_core.clone(),
                        val_core.clone(),
                    ),
                    Totality::Unsafe => kernel::ast::Definition::unsafe_def(
                        name.clone(),
                        ty_core.clone(),
                        val_core.clone(),
                    ),
                    Totality::Total | Totality::WellFounded => kernel::ast::Definition::total(
                        name.clone(),
                        ty_core.clone(),
                        val_core.clone(),
                    ),
                    Totality::Axiom => kernel::ast::Definition::total(
                        name.clone(),
                        ty_core.clone(),
                        val_core.clone(),
                    ),
                };
                def.transparency = transparency;
                def.capture_modes = def_capture_modes;
                def.noncomputable = noncomputable;

                let env_snapshot = env.clone();
                let deployed_len_checkpoint = processed.deployed_definitions.len();
                let artifacts_len_checkpoint = processed.artifacts.len();

                if options.collect_artifacts {
                    processed.artifacts.push(Artifact::ElaboratedDef {
                        name: name.clone(),
                        ty: format!("{:?}", ty_core),
                        val: format!("{:?}", val_core),
                    });
                }

                match env.add_definition(def) {
                    Ok(_) => {
                        let mut post_admission_failed = false;

                        if let Some(def) = env.get_definition(&name) {
                            if uses_interior_mutability_axioms(&def.axioms)
                                && def.totality != Totality::Unsafe
                                && !options.allow_axioms
                            {
                                handle_diagnostic(
                                    diagnostics,
                                    expander,
                                    Diagnostic::error(format!(
                                        "Interior mutability is gated: definition '{}' depends on RefCell/Mutex/Atomic, but runtime checks are not implemented. Rerun with --allow-axioms to opt in to runtime stubs or mark it unsafe.",
                                        name
                                    ))
                                    .with_code(CODE_DRIVER_INTERIOR_MUTABILITY_GATED),
                                );
                                rollback_failed_definition(
                                    env,
                                    &env_snapshot,
                                    &mut processed,
                                    deployed_len_checkpoint,
                                    artifacts_len_checkpoint,
                                    &name,
                                    previous_term_span_map.as_ref(),
                                );
                                continue;
                            }
                        }

                        // MIR Validation Pipeline (Unified)
                        // Even in REPL/Driver mode, we check safety constraints.
                        if let Some(d) = env.definitions().get(&name) {
                            if let Some(val) = &d.value {
                                let ids = mir::types::IdRegistry::from_env(&env);
                                if ids.has_errors() {
                                    for err in ids.errors() {
                                        let mut diagnostic = Diagnostic::error(err.to_string());
                                        if let Some(span) = err.span() {
                                            diagnostic =
                                                diagnostic.with_span(to_frontend_span(span));
                                        }
                                        handle_diagnostic(diagnostics, expander, diagnostic);
                                    }
                                    rollback_failed_definition(
                                        env,
                                        &env_snapshot,
                                        &mut processed,
                                        deployed_len_checkpoint,
                                        artifacts_len_checkpoint,
                                        &name,
                                        previous_term_span_map.as_ref(),
                                    );
                                    continue;
                                }
                                let mut ctx = mir::lower::LoweringContext::new_with_metadata(
                                    vec![],
                                    d.ty.clone(),
                                    &env,
                                    &ids,
                                    Some(term_span_map.clone()),
                                    Some(name.clone()),
                                    Some(Rc::new(d.capture_modes.clone())),
                                );
                                let dest = mir::Place::from(mir::Local(0));
                                let target = mir::BasicBlock(1);
                                ctx.body.basic_blocks.push(mir::BasicBlockData {
                                    statements: vec![],
                                    terminator: None,
                                });
                                if let Err(e) = ctx.lower_term(val, dest, target) {
                                    handle_diagnostic(
                                        diagnostics,
                                        expander,
                                        Diagnostic::error(format!(
                                            "Lowering error in {}: {}",
                                            name, e
                                        )),
                                    );
                                    rollback_failed_definition(
                                        env,
                                        &env_snapshot,
                                        &mut processed,
                                        deployed_len_checkpoint,
                                        artifacts_len_checkpoint,
                                        &name,
                                        previous_term_span_map.as_ref(),
                                    );
                                    continue;
                                }
                                ctx.set_block(target);
                                ctx.terminate_with_term_span(val, mir::Terminator::Return);

                                mir::transform::storage::insert_exit_storage_deads(&mut ctx.body);

                                if options.collect_artifacts {
                                    processed.artifacts.push(Artifact::MirBody {
                                        name: name.clone(),
                                        body: format!("{:?}", ctx.body),
                                    });
                                }

                                // Check MIR typing
                                let mut typing =
                                    mir::analysis::typing::TypingChecker::new(&ctx.body);
                                typing.check();
                                let typing_errors = typing.errors();
                                if !typing_errors.is_empty() {
                                    post_admission_failed = true;
                                }
                                for e in typing_errors {
                                    let mut diagnostic = Diagnostic::error(format!(
                                        "MIR typing error in {}: {}",
                                        name, e
                                    ))
                                    .with_code(e.diagnostic_code());
                                    if let Some(span) =
                                        span_for_mir_location(e.location(), &ctx.span_table)
                                    {
                                        diagnostic = diagnostic.with_span(span);
                                    }
                                    handle_diagnostic(diagnostics, expander, diagnostic);
                                }

                                // Check Ownership
                                let mut ownership =
                                    mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
                                ownership.analyze();
                                let ownership_errors = ownership.check_structured();
                                if !ownership_errors.is_empty() {
                                    post_admission_failed = true;
                                }
                                let ownership_error_strings: Vec<String> =
                                    ownership_errors.iter().map(|e| e.to_string()).collect();
                                for e in &ownership_errors {
                                    let mut diagnostic = Diagnostic::error(format!(
                                        "Ownership error in {}: {}",
                                        name, e
                                    ))
                                    .with_code(e.diagnostic_code());
                                    if let Some(span) =
                                        span_for_mir_location(e.location(), &ctx.span_table)
                                    {
                                        diagnostic = diagnostic.with_span(span);
                                    }
                                    handle_diagnostic(diagnostics, expander, diagnostic);
                                }

                                // Check Borrows
                                // Check NLL
                                let mut nll = mir::analysis::nll::NllChecker::new(&ctx.body);
                                nll.check();
                                let nll_result = nll.into_result();
                                if !nll_result.errors.is_empty() {
                                    post_admission_failed = true;
                                }
                                for e in &nll_result.errors {
                                    let mut diagnostic = Diagnostic::error(format!(
                                        "Borrow error in {}: {}",
                                        name, e
                                    ))
                                    .with_code(e.diagnostic_code());
                                    if let Some(span) =
                                        span_for_mir_location(e.location(), &ctx.span_table)
                                    {
                                        diagnostic = diagnostic.with_span(span);
                                    }
                                    handle_diagnostic(diagnostics, expander, diagnostic);
                                }
                                let panic_free_runtime_checks =
                                    options.panic_free && !nll_result.runtime_checks.is_empty();
                                if panic_free_runtime_checks {
                                    post_admission_failed = true;
                                    let mut diagnostic = Diagnostic::error(format!(
                                        "Panic-free profile violation in {}: borrow checking inserted {} runtime check(s).",
                                        name,
                                        nll_result.runtime_checks.len()
                                    ))
                                    .with_code(CODE_DRIVER_LINT_PANIC_FREE);
                                    if let Some(first_check) = nll_result.runtime_checks.first() {
                                        if let Some(span) = span_for_mir_location(
                                            Some(MirSpan {
                                                block: first_check.location.block,
                                                statement_index: first_check
                                                    .location
                                                    .statement_index,
                                            }),
                                            &ctx.span_table,
                                        ) {
                                            diagnostic = diagnostic.with_span(span);
                                        }
                                    }
                                    handle_diagnostic(diagnostics, expander, diagnostic);
                                }
                                if nll_result.is_ok() && !panic_free_runtime_checks {
                                    nll_result.inject_runtime_checks(&mut ctx.body);
                                }

                                if options.panic_free {
                                    // Check Lints (Panic Free)
                                    let mut linter = mir::lints::PanicFreeLinter::new(&ctx.body);
                                    linter.check();
                                    if !linter.errors.is_empty() {
                                        post_admission_failed = true;
                                    }
                                    for e in &linter.errors {
                                        handle_diagnostic(
                                            diagnostics,
                                            expander,
                                            Diagnostic::error(format!(
                                                "Lint error in {}: {}",
                                                name, e
                                            ))
                                            .with_code(CODE_DRIVER_LINT_PANIC_FREE),
                                        );
                                    }
                                }

                                let mut derived_bodies = ctx.derived_bodies.borrow_mut();
                                let derived_span_tables = ctx.derived_span_tables.borrow();
                                for (i, body) in derived_bodies.iter_mut().enumerate() {
                                    mir::transform::storage::insert_exit_storage_deads(body);

                                    let mut typing =
                                        mir::analysis::typing::TypingChecker::new(body);
                                    typing.check();
                                    let closure_typing_errors = typing.errors();
                                    if !closure_typing_errors.is_empty() {
                                        post_admission_failed = true;
                                    }
                                    for e in closure_typing_errors {
                                        let mut diagnostic = Diagnostic::error(format!(
                                            "MIR typing error in {} closure {}: {}",
                                            name, i, e
                                        ))
                                        .with_code(e.diagnostic_code());
                                        if let Some(span_table) = derived_span_tables.get(i) {
                                            if let Some(span) =
                                                span_for_mir_location(e.location(), span_table)
                                            {
                                                diagnostic = diagnostic.with_span(span);
                                            }
                                        }
                                        handle_diagnostic(diagnostics, expander, diagnostic);
                                    }

                                    let mut nll = mir::analysis::nll::NllChecker::new(body);
                                    nll.check();
                                    let nll_result = nll.into_result();
                                    if !nll_result.errors.is_empty() {
                                        post_admission_failed = true;
                                    }
                                    for e in &nll_result.errors {
                                        let mut diagnostic = Diagnostic::error(format!(
                                            "Borrow error in {} closure {}: {}",
                                            name, i, e
                                        ))
                                        .with_code(e.diagnostic_code());
                                        if let Some(span_table) = derived_span_tables.get(i) {
                                            if let Some(span) =
                                                span_for_mir_location(e.location(), span_table)
                                            {
                                                diagnostic = diagnostic.with_span(span);
                                            }
                                        }
                                        handle_diagnostic(diagnostics, expander, diagnostic);
                                    }
                                    let panic_free_runtime_checks =
                                        options.panic_free && !nll_result.runtime_checks.is_empty();
                                    if panic_free_runtime_checks {
                                        post_admission_failed = true;
                                        let mut diagnostic = Diagnostic::error(format!(
                                            "Panic-free profile violation in {} closure {}: borrow checking inserted {} runtime check(s).",
                                            name,
                                            i,
                                            nll_result.runtime_checks.len()
                                        ))
                                        .with_code(CODE_DRIVER_LINT_PANIC_FREE);
                                        if let Some(span_table) = derived_span_tables.get(i) {
                                            if let Some(first_check) =
                                                nll_result.runtime_checks.first()
                                            {
                                                if let Some(span) = span_for_mir_location(
                                                    Some(MirSpan {
                                                        block: first_check.location.block,
                                                        statement_index: first_check
                                                            .location
                                                            .statement_index,
                                                    }),
                                                    span_table,
                                                ) {
                                                    diagnostic = diagnostic.with_span(span);
                                                }
                                            }
                                        }
                                        handle_diagnostic(diagnostics, expander, diagnostic);
                                    }
                                    if nll_result.is_ok() && !panic_free_runtime_checks {
                                        nll_result.inject_runtime_checks(body);
                                    }

                                    if options.panic_free {
                                        let mut linter = mir::lints::PanicFreeLinter::new(body);
                                        linter.check();
                                        if !linter.errors.is_empty() {
                                            post_admission_failed = true;
                                        }
                                        for e in &linter.errors {
                                            handle_diagnostic(
                                                diagnostics,
                                                expander,
                                                Diagnostic::error(format!(
                                                    "Lint error in {} closure {}: {}",
                                                    name, i, e
                                                ))
                                                .with_code(CODE_DRIVER_LINT_PANIC_FREE),
                                            );
                                        }
                                    }
                                }

                                if options.collect_artifacts {
                                    processed.artifacts.push(Artifact::BorrowCheck {
                                        name: name.clone(),
                                        ownership_errors: ownership_error_strings,
                                        result: nll_result,
                                    });
                                }
                            }
                        }

                        if post_admission_failed {
                            rollback_failed_definition(
                                env,
                                &env_snapshot,
                                &mut processed,
                                deployed_len_checkpoint,
                                artifacts_len_checkpoint,
                                &name,
                                previous_term_span_map.as_ref(),
                            );
                            continue;
                        }

                        processed.deployed_definitions.push(name.clone());
                        if options.verbose || options.show_types {
                            println!("Defined {} ({})", name, totality_label(totality));
                        }

                        if let Some(def) = env.get_definition(&name) {
                            report_axiom_dependencies(env, def, expander, diagnostics);
                            if options.collect_artifacts && !def.axioms.is_empty() {
                                let classical =
                                    kernel::checker::classical_axiom_dependencies(env, def);
                                processed.artifacts.push(Artifact::AxiomDependencies {
                                    name: name.clone(),
                                    axioms: def.axioms.clone(),
                                    classical,
                                });
                            }
                        }
                    }
                    Err(e) => handle_diagnostic(
                        diagnostics,
                        expander,
                        diagnostic_from_kernel_error(
                            &format!("Environment error defining '{}'", name),
                            &e,
                            Some(val_span),
                        ),
                    ),
                }
            }

            Declaration::Axiom { name, ty, tags } => {
                let ty_span = ty.span;
                if reject_reserved_primitive_name(env, &name, expander, diagnostics) {
                    continue;
                }
                if reject_redefinition(env, &name, "axiom", options, expander, diagnostics) {
                    continue;
                }
                if options.require_axiom_tags && tags.is_empty() {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        Diagnostic::error(format!(
                            "Axiom '{}' must declare at least one tag (classical/unsafe) when --require-axiom-tags is enabled",
                            name
                        ))
                        .with_span(ty_span),
                    );
                    continue;
                }
                let mut elab = new_elaborator_with_imports(env, &import_scopes);
                let ty_core = match elab.infer_type(ty) {
                    Ok((t, s)) => {
                        if !matches!(*s, Term::Sort(_)) {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                Diagnostic::error(format!("Axiom '{}' type must be a Sort", name))
                                    .with_span(ty_span),
                            );
                            continue;
                        }
                        elab.instantiate_metas(&t)
                    }
                    Err(e) => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            diagnostic_from_elab_error(
                                &format!("Elaboration error (Axiom Type) in '{}'", name),
                                &e,
                            ),
                        );
                        continue;
                    }
                };

                if let Err(e) = env.add_definition(Definition::axiom_with_tags(
                    name.clone(),
                    ty_core,
                    tags.clone(),
                )) {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        diagnostic_from_kernel_error(
                            &format!("Kernel error declaring axiom '{}'", name),
                            &e,
                            Some(ty_span),
                        ),
                    );
                    continue;
                }
                if options.verbose || options.show_types {
                    println!("Axiom {} declared", name);
                }
                if let Some(def) = env.get_definition(&name) {
                    report_axiom_dependencies(env, def, expander, diagnostics);
                    if options.collect_artifacts && !def.axioms.is_empty() {
                        let classical = kernel::checker::classical_axiom_dependencies(env, def);
                        processed.artifacts.push(Artifact::AxiomDependencies {
                            name: name.clone(),
                            axioms: def.axioms.clone(),
                            classical,
                        });
                    }
                }
                processed.deployed_definitions.push(name);
            }

            Declaration::Inductive {
                name,
                ty,
                ctors,
                is_copy,
                attrs,
            } => {
                if reject_reserved_primitive_inductive(&name, expander, diagnostics) {
                    continue;
                }
                if reject_redefinition(env, &name, "inductive", options, expander, diagnostics) {
                    continue;
                }
                if options.prelude_frozen && !options.allow_redefine {
                    let mut has_conflict = false;
                    for (ctor_name, _) in &ctors {
                        if env.get_definition(ctor_name).is_some()
                            || env.get_inductive(ctor_name).is_some()
                        {
                            has_conflict = true;
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                Diagnostic::error(format!(
                                    "Constructor '{}' for inductive '{}' conflicts with an existing name (prelude is frozen; use --allow-redefine to override)",
                                    ctor_name, name
                                )),
                            );
                        }
                    }
                    if has_conflict {
                        continue;
                    }
                }
                let mut elab = new_elaborator_with_imports(env, &import_scopes);
                let ty_span = ty.span;
                let (ty_core, _) = match elab.infer_type(ty) {
                    Ok((t, s)) => (elab.instantiate_metas(&t), s),
                    Err(e) => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            diagnostic_from_elab_error(
                                &format!("Elaboration error (Inductive Type) '{}'", name),
                                &e,
                            ),
                        );
                        continue;
                    }
                };
                let markers = match elab.resolve_type_markers(&attrs, ty_span) {
                    Ok(markers) => markers,
                    Err(e) => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            diagnostic_from_elab_error(
                                &format!("Elaboration error (Inductive Markers) '{}'", name),
                                &e,
                            ),
                        );
                        continue;
                    }
                };

                // Placeholder
                let placeholder = InductiveDecl {
                    name: name.clone(),
                    univ_params: vec![],
                    num_params: 0,
                    ty: ty_core.clone(),
                    ctors: vec![],
                    is_copy,
                    markers: markers.clone(),
                    axioms: vec![],
                    primitive_deps: vec![],
                };
                let previous = env.insert_inductive_placeholder(placeholder);

                // Constructors
                let mut kernel_ctors = Vec::new();
                let mut ctor_spans = Vec::new();
                for (cname, cty) in ctors {
                    let ctor_span = cty.span;
                    let mut elab_c = new_elaborator_with_imports(env, &import_scopes);
                    let (cty_core, _) = match elab_c.infer_type(cty) {
                        Ok((t, _)) => (elab_c.instantiate_metas(&t), ()),
                        Err(e) => {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                diagnostic_from_elab_error(
                                    &format!("Elaboration error (Constructor '{}')", cname),
                                    &e,
                                ),
                            );
                            continue;
                        }
                    };
                    kernel_ctors.push(Constructor {
                        name: cname,
                        ty: cty_core,
                    });
                    ctor_spans.push(ctor_span);
                }

                // Final Register
                let decl = InductiveDecl {
                    name: name.clone(),
                    univ_params: vec![],
                    num_params: 0,
                    ty: ty_core,
                    ctors: kernel_ctors.clone(),
                    is_copy,
                    markers,
                    axioms: vec![],
                    primitive_deps: vec![],
                };

                env.inductives.remove(&name);
                if let Err(e) = env.add_inductive(decl) {
                    if let Some(prev) = previous {
                        env.restore_inductive(prev);
                    }
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        diagnostic_from_kernel_error(
                            &format!("Error registering inductive '{}'", name),
                            &e,
                            Some(ty_span),
                        ),
                    );
                    continue;
                }
                if let Some(decl) = env.get_inductive(&name) {
                    report_inductive_axiom_dependencies(env, decl, expander, diagnostics);
                }

                // Register constructors as definitions (for backend visibility)
                let constructor_is_axiom_dependent = env
                    .get_inductive(&name)
                    .map(|decl| !decl.axioms.is_empty())
                    .unwrap_or(false);
                for (i, ctor) in kernel_ctors.iter().enumerate() {
                    let val = Rc::new(Term::Ctor(name.clone(), i, vec![]));
                    let mut def =
                        Definition::total(ctor.name.clone(), ctor.ty.clone(), val.clone());
                    if constructor_is_axiom_dependent {
                        def.noncomputable = true;
                    }
                    if let Err(e) = env.add_definition(def) {
                        let span = ctor_spans.get(i).copied();
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            diagnostic_from_kernel_error(
                                &format!("Error registering constructor '{}'", ctor.name),
                                &e,
                                span,
                            ),
                        );
                    }
                }

                if options.verbose || options.show_types {
                    println!("Defined inductive {}", name);
                }
                processed.deployed_definitions.push(name);
            }

            Declaration::Instance {
                trait_name,
                head,
                requirements,
                is_unsafe,
            } => {
                let head_span = head.span;
                if !trait_name.eq_ignore_ascii_case("copy") {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        Diagnostic::error(format!(
                            "Unknown trait '{}' in instance declaration",
                            trait_name
                        )),
                    );
                    continue;
                }
                if !is_unsafe {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        Diagnostic::error(
                            "Explicit Copy instances must be declared unsafe: \
(unsafe instance copy ...)"
                                .to_string(),
                        ),
                    );
                    continue;
                }

                let (binders, _head_body) = peel_surface_pi_binders(head.clone());

                let head_core = match elaborate_instance_type(
                    env,
                    expander,
                    diagnostics,
                    &head,
                    &import_scopes,
                ) {
                    Some(term) => term,
                    None => continue,
                };

                let (binder_count, head_body_core) = peel_core_pi_binders(&head_core);
                let (head_term, head_args) = collect_core_app_spine(&head_body_core);
                let ind_name = match &*head_term {
                    Term::Ind(name, _) => name.clone(),
                    _ => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            Diagnostic::error(
                                "Instance head must be an inductive type application".to_string(),
                            ),
                        );
                        continue;
                    }
                };

                let decl = match env.get_inductive(&ind_name) {
                    Some(decl) => decl,
                    None => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            Diagnostic::error(format!(
                                "Unknown inductive type '{}' in instance head",
                                ind_name
                            )),
                        );
                        continue;
                    }
                };

                let expected_param_count = count_core_pi_binders(&decl.ty);
                if head_args.len() != expected_param_count {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        Diagnostic::error(format!(
                            "Instance head for '{}' expects {} parameters, got {}",
                            ind_name,
                            expected_param_count,
                            head_args.len()
                        )),
                    );
                    continue;
                }

                if binder_count != expected_param_count {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        Diagnostic::error(format!(
                            "Instance head for '{}' must bind {} parameters, got {}",
                            ind_name, expected_param_count, binder_count
                        )),
                    );
                    continue;
                }

                let mut head_ok = true;
                for (i, arg) in head_args.iter().enumerate() {
                    let expected = expected_param_count - 1 - i;
                    if !matches!(&**arg, Term::Var(idx) if *idx == expected) {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            Diagnostic::error(
                                "Instance head arguments must be distinct parameters".to_string(),
                            ),
                        );
                        head_ok = false;
                        break;
                    }
                }
                if !head_ok {
                    continue;
                }

                let mut req_terms = Vec::new();
                for req in requirements {
                    let wrapped_req = wrap_surface_with_binders(&binders, req);
                    let req_core = match elaborate_instance_type(
                        env,
                        expander,
                        diagnostics,
                        &wrapped_req,
                        &import_scopes,
                    ) {
                        Some(term) => term,
                        None => {
                            head_ok = false;
                            break;
                        }
                    };
                    let (req_binders, req_body) = peel_core_pi_binders(&req_core);
                    if req_binders != expected_param_count {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            Diagnostic::error(format!(
                                "Instance requirement must bind {} parameters, got {}",
                                expected_param_count, req_binders
                            )),
                        );
                        head_ok = false;
                        break;
                    }
                    req_terms.push(req_body);
                }
                if !head_ok {
                    continue;
                }

                if let Err(e) = env.add_copy_instance(CopyInstance {
                    ind_name: ind_name.clone(),
                    param_count: expected_param_count,
                    requirements: req_terms,
                    source: CopyInstanceSource::Explicit,
                    is_unsafe,
                }) {
                    handle_diagnostic(
                        diagnostics,
                        expander,
                        diagnostic_from_kernel_error(
                            "Error registering Copy instance",
                            &e,
                            Some(head_span),
                        ),
                    );
                } else if let Some(decl) = env.get_inductive(&ind_name) {
                    report_inductive_axiom_dependencies(env, decl, expander, diagnostics);
                }
            }

            Declaration::DefMacro { name, args, body } => {
                expander.add_macro(name.clone(), args, body);
                if options.verbose {
                    println!("Defined macro {}", name);
                }
            }

            Declaration::ImportClassical => {
                let name = "classical_choice".to_string();
                if env.get_definition(&name).is_none() {
                    let false_name = "False";
                    if env.get_inductive(false_name).is_none() {
                        if env.get_definition(false_name).is_some() {
                            diagnostics.handle(Diagnostic::error(format!(
                                "import classical requires inductive '{}', but a definition with that name already exists",
                                false_name
                            )));
                            continue;
                        }
                        let false_decl = InductiveDecl::new(
                            false_name.to_string(),
                            Term::sort(KernelLevel::Zero),
                            vec![],
                        );
                        let allow_reserved = env.allows_reserved_primitives();
                        env.set_allow_reserved_primitives(true);
                        if let Err(e) = env.add_inductive(false_decl) {
                            env.set_allow_reserved_primitives(allow_reserved);
                            diagnostics.handle(diagnostic_from_kernel_error(
                                &format!("Kernel error declaring '{}'", false_name),
                                &e,
                                None,
                            ));
                            continue;
                        }
                        env.set_allow_reserved_primitives(allow_reserved);
                    }
                    let ty = classical_choice_type(false_name);
                    match env.add_definition(Definition::axiom_classical(name.clone(), ty)) {
                        Ok(()) => {
                            if let Some(def) = env.get_definition(&name) {
                                report_axiom_dependencies(env, def, expander, diagnostics);
                                if options.collect_artifacts && !def.axioms.is_empty() {
                                    let classical =
                                        kernel::checker::classical_axiom_dependencies(env, def);
                                    processed.artifacts.push(Artifact::AxiomDependencies {
                                        name: name.clone(),
                                        axioms: def.axioms.clone(),
                                        classical,
                                    });
                                }
                            }
                            processed.deployed_definitions.push(name);
                        }
                        Err(e) => diagnostics.handle(diagnostic_from_kernel_error(
                            &format!("Kernel error declaring classical axiom '{}'", name),
                            &e,
                            None,
                        )),
                    }
                }
            }

            Declaration::ImportModule { module } => {
                if !import_scopes.contains(&module) {
                    import_scopes.push(module);
                    import_scopes.sort();
                    import_scopes.dedup();
                }
            }

            Declaration::Expr(term) => {
                let expr_span = term.span;
                let mut elab = new_elaborator_with_imports(env, &import_scopes);
                match elab.infer(term) {
                    Ok((core_term, ty)) => {
                        let mut valid = true;
                        if let Err(e) = elab.solve_constraints() {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                attach_elab_metadata(
                                    Diagnostic::error(format!(
                                        "Unsolved constraints in expression: {:?}",
                                        e
                                    )),
                                    &e,
                                ),
                            );
                            valid = false;
                        }

                        let core_term = elab.instantiate_metas(&core_term);
                        if valid {
                            if let Err(msg) = validate_core_invariants(&core_term) {
                                handle_diagnostic(
                                    diagnostics,
                                    expander,
                                    Diagnostic::error(format!(
                                        "Expression violates core invariants: {}",
                                        msg
                                    ))
                                    .with_span(expr_span),
                                );
                                valid = false;
                            }
                        }

                        let ty = elab.instantiate_metas(&ty);
                        if let Err(msg) = validate_core_invariants(&ty) {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                Diagnostic::error(format!(
                                    "Expression type violates core invariants: {}",
                                    msg
                                ))
                                .with_span(expr_span),
                            );
                            valid = false;
                        }

                        if !valid {
                            continue;
                        }

                        let ctx = Context::new();
                        if let Err(e) =
                            kernel::checker::check(env, &ctx, core_term.clone(), ty.clone())
                        {
                            handle_diagnostic(
                                diagnostics,
                                expander,
                                diagnostic_from_kernel_error(
                                    "Kernel re-check failed for expression",
                                    &e,
                                    Some(expr_span),
                                ),
                            );
                            continue;
                        }

                        // WHNF type if needed
                        let ty_norm = match kernel::checker::whnf(
                            env,
                            ty.clone(),
                            kernel::Transparency::Reducible,
                        ) {
                            Ok(norm) => norm,
                            Err(e) => {
                                handle_diagnostic(
                                    diagnostics,
                                    expander,
                                    diagnostic_from_kernel_error(
                                        "Failed to normalize type for display",
                                        &e,
                                        Some(expr_span),
                                    ),
                                );
                                continue;
                            }
                        };
                        processed
                            .evaluated_terms
                            .push((ty_norm.clone(), core_term.clone()));

                        if options.show_types {
                            println!(": {:?}", ty_norm);
                        }
                        if options.show_eval {
                            let mut allow_eval = true;
                            if !options.allow_axioms {
                                let deps =
                                    kernel::checker::term_axiom_dependencies(env, &core_term);
                                if !deps.is_empty() {
                                    allow_eval = false;
                                    let mut diagnostic = Diagnostic::error(format!(
                                        "Evaluation blocked: expression depends on axioms ({})",
                                        deps.join(", ")
                                    ))
                                    .with_code(CODE_DRIVER_EVAL_BLOCKED);
                                    diagnostic = diagnostic.with_span(expr_span);
                                    handle_diagnostic(diagnostics, expander, diagnostic);
                                }
                            }
                            if allow_eval {
                                let val_norm = nbe_normalize(env, core_term);
                                //let val_norm = nbe_eval(env, core_term); // Use eval for now? No, normalize for readable output
                                println!("Eval: {:?}", val_norm);
                            }
                        }
                    }
                    Err(e) => {
                        handle_diagnostic(
                            diagnostics,
                            expander,
                            diagnostic_from_elab_error("Elaboration error (Expression)", &e),
                        );
                    }
                }
            }
        }
    }
    if options.collect_artifacts {
        sort_artifacts(&mut processed.artifacts);
    }

    expander.mark_module_loaded(&module_id);
    Ok(processed)
}

fn defeq_fuel_diagnostic(context: Option<&kernel::checker::DefEqFuelContext>) -> String {
    let policy = kernel::nbe::defeq_fuel_policy();
    let (fuel, source) = match context.and_then(|ctx| ctx.fuel()) {
        Some(fuel) if fuel == policy.fuel => (fuel, Some(policy.source)),
        Some(fuel) => (fuel, None),
        None => (policy.fuel, Some(policy.source)),
    };
    let source_label = source.map(kernel::nbe::DefEqFuelSource::label);
    let policy_label = policy.source.label();
    let source_suffix = source_label
        .map(|label| format!(", source = {}", label))
        .unwrap_or_default();
    let mut message = format!(
        "Definitional equality fuel exhausted (fuel = {}{}).",
        fuel, source_suffix
    );
    if source_label.is_none() {
        message.push_str(&format!(
            " Policy: fuel = {}, source = {}.",
            policy.fuel, policy_label
        ));
    }
    message.push_str(
        " Try marking large definitions as `opaque`, or increase the budget with `--defeq-fuel <N>` (CLI) or LRL_DEFEQ_FUEL (env).",
    );
    if let Some(detail) = context.and_then(|ctx| ctx.diagnostic_detail()) {
        message.push_str(&format!(" Context: {}", detail));
    }
    message
}

fn defeq_fix_diagnostic() -> String {
    "Definitional equality refused to unfold `fix` (general recursion). Mark the definition `partial`, keep it out of types, or make it `opaque` if it should not reduce.".to_string()
}

fn peel_surface_pi_binders(
    term: SurfaceTerm,
) -> (
    Vec<(
        String,
        BinderInfo,
        Option<kernel::ast::FunctionKind>,
        SurfaceTerm,
    )>,
    SurfaceTerm,
) {
    let mut binders = Vec::new();
    let mut curr = term;
    loop {
        match curr.kind {
            SurfaceTermKind::Pi(name, info, kind, ty, body) => {
                binders.push((name, info, kind, *ty));
                curr = *body;
            }
            _ => break,
        }
    }
    (binders, curr)
}

fn wrap_surface_with_binders(
    binders: &[(
        String,
        BinderInfo,
        Option<kernel::ast::FunctionKind>,
        SurfaceTerm,
    )],
    body: SurfaceTerm,
) -> SurfaceTerm {
    let mut curr = body;
    for (name, info, kind, ty) in binders.iter().rev() {
        let span = curr.span;
        curr = SurfaceTerm {
            kind: SurfaceTermKind::Pi(
                name.clone(),
                *info,
                *kind,
                Box::new(ty.clone()),
                Box::new(curr),
            ),
            span,
        };
    }
    curr
}

fn collect_core_app_spine(term: &Rc<Term>) -> (Rc<Term>, Vec<Rc<Term>>) {
    let mut args = Vec::new();
    let mut head = term.clone();
    while let Term::App(f, a, _) = &*head {
        args.push(a.clone());
        head = f.clone();
    }
    args.reverse();
    (head, args)
}

fn count_core_pi_binders(term: &Rc<Term>) -> usize {
    let mut count = 0;
    let mut curr = term.clone();
    while let Term::Pi(_, body, _, _) = &*curr {
        count += 1;
        curr = body.clone();
    }
    count
}

fn peel_core_pi_binders(term: &Rc<Term>) -> (usize, Rc<Term>) {
    let mut count = 0;
    let mut curr = term.clone();
    while let Term::Pi(_, body, _, _) = &*curr {
        count += 1;
        curr = body.clone();
    }
    (count, curr)
}

fn elaborate_instance_type(
    env: &Env,
    expander: &mut Expander,
    diagnostics: &mut DiagnosticCollector,
    term: &SurfaceTerm,
    import_scopes: &[String],
) -> Option<Rc<Term>> {
    let mut elab = new_elaborator_with_imports(env, import_scopes);
    let (t, s) = match elab.infer_type(term.clone()) {
        Ok(pair) => pair,
        Err(e) => {
            handle_diagnostic(
                diagnostics,
                expander,
                diagnostic_from_elab_error("Elaboration error (Instance Type)", &e),
            );
            return None;
        }
    };

    if !matches!(*s, Term::Sort(_)) {
        handle_diagnostic(
            diagnostics,
            expander,
            Diagnostic::error("Instance term must be a type".to_string()).with_span(term.span),
        );
        return None;
    }

    if let Err(e) = elab.solve_constraints() {
        handle_diagnostic(
            diagnostics,
            expander,
            attach_elab_metadata(
                Diagnostic::error(format!("Unsolved constraints in instance: {:?}", e)),
                &e,
            ),
        );
        return None;
    }

    let t = elab.instantiate_metas(&t);
    if let Err(msg) = validate_core_invariants(&t) {
        handle_diagnostic(
            diagnostics,
            expander,
            Diagnostic::error(format!("Instance term violates core invariants: {}", msg))
                .with_span(term.span),
        );
        return None;
    }

    Some(t)
}

fn format_kernel_error(err: &kernel::checker::TypeError) -> String {
    match err {
        kernel::checker::TypeError::DefEqFuelExhausted { context } => {
            defeq_fuel_diagnostic(Some(context))
        }
        kernel::checker::TypeError::DefEqFixUnfold => defeq_fix_diagnostic(),
        kernel::checker::TypeError::ReservedPrimitiveName(name) => format!(
            "Reserved primitive name '{}' can only be declared in the prelude as an axiom (index_* requires unsafe)",
            name
        ),
        kernel::checker::TypeError::ReservedPrimitiveSignature(name) => format!(
            "Reserved primitive '{}' must use the standard prelude signature",
            name
        ),
        kernel::checker::TypeError::ReservedCoreName(name) => format!(
            "Reserved core name '{}' can only be declared in the prelude",
            name
        ),
        kernel::checker::TypeError::DefinitionAlreadyExists(name) => {
            format!("Definition '{}' already exists", name)
        }
        kernel::checker::TypeError::InductiveAlreadyExists(name) => {
            format!("Inductive '{}' already exists", name)
        }
        kernel::checker::TypeError::ExplicitCopyInstanceRequiresUnsafe { ind } => format!(
            "Explicit Copy instance for inductive '{}' requires unsafe",
            ind
        ),
        kernel::checker::TypeError::ExplicitCopyInstanceInteriorMutable { ind } => format!(
            "Explicit Copy instance for interior-mutable inductive '{}' is not allowed",
            ind
        ),
        kernel::checker::TypeError::FunctionKindTooSmall { annotated, required } => format!(
            "Function kind mismatch: annotated {:?} but requires {:?}",
            annotated, required
        ),
        kernel::checker::TypeError::RefLifetimeLabelMismatch {
            expected_label,
            got_label,
            ..
        } => format!(
            "Ref lifetime label mismatch: expected {}, got {}",
            expected_label, got_label
        ),
        kernel::checker::TypeError::PartialReturnType { name, ty } => format!(
            "Partial definition '{}' must return Comp A, got {:?}",
            name, ty
        ),
        kernel::checker::TypeError::LargeElimination(name) => format!(
            "Large elimination from Prop inductive '{}' to Type is not allowed",
            name
        ),
        kernel::checker::TypeError::PropFieldInData { ind, ctor, field } => format!(
            "Inductive '{}' constructor '{}' field {} is in Prop",
            ind, ctor, field
        ),
        kernel::checker::TypeError::NestedInductive { ind, ctor, field } => format!(
            "Nested inductive occurrence of '{}' in constructor '{}' field {} is not supported yet",
            ind, ctor, field
        ),
        kernel::checker::TypeError::AxiomDependencyRequiresNoncomputable {
            name,
            kinds,
            axioms,
        } => {
            let mut message = format!(
                "Definition '{}' depends on {} axioms: {}. Mark it noncomputable or unsafe",
                name,
                kinds,
                axioms.join(", ")
            );
            if uses_interior_mutability_axioms(axioms) {
                message.push_str(
                    ". RefCell/Mutex/Atomic are not yet available in safe code; runtime checks are unimplemented",
                );
            }
            message
        }
        _ => format!("{:?}", err),
    }
}

fn format_elab_error(err: &ElabError) -> String {
    match err {
        ElabError::InferenceError(
            kernel::checker::TypeError::DefEqFuelExhausted { context },
            _,
        ) => {
            defeq_fuel_diagnostic(Some(context))
        }
        ElabError::InferenceError(kernel::checker::TypeError::DefEqFixUnfold, _) => {
            defeq_fix_diagnostic()
        }
        ElabError::InferenceError(kernel::checker::TypeError::LargeElimination(name), _) => format!(
            "Large elimination from Prop inductive '{}' to Type is not allowed (note: Prop classification does not unfold `opaque` aliases unless explicitly enabled)",
            name
        ),
        ElabError::InferenceError(
            kernel::checker::TypeError::PropFieldInData { ind, ctor, field },
            _,
        ) => format!(
            "Inductive '{}' constructor '{}' field {} is in Prop (note: Prop classification does not unfold `opaque` aliases unless explicitly enabled)",
            ind, ctor, field
        ),
        ElabError::InferenceError(
            kernel::checker::TypeError::NestedInductive { ind, ctor, field },
            _,
        ) => format!(
            "Nested inductive occurrence of '{}' in constructor '{}' field {} is not supported yet",
            ind, ctor, field
        ),
        _ => err.to_string(),
    }
}

fn totality_label(totality: Totality) -> &'static str {
    match totality {
        Totality::Total => "total",
        Totality::WellFounded => "well-founded",
        Totality::Partial => "partial",
        Totality::Axiom => "axiom",
        Totality::Unsafe => "unsafe",
    }
}

fn report_axiom_dependencies(
    env: &Env,
    def: &kernel::ast::Definition,
    expander: &mut Expander,
    diagnostics: &mut DiagnosticCollector,
) {
    let has_axioms = !def.axioms.is_empty();
    let has_primitives = !def.primitive_deps.is_empty();
    if !has_axioms && !has_primitives {
        return;
    }

    let suffix = if has_axioms {
        let classical = kernel::checker::classical_axiom_dependencies(env, def);
        let unsafe_axioms =
            kernel::checker::axiom_dependencies_with_tag(env, &def.axioms, AxiomTag::Unsafe);
        format_axiom_tag_suffix(&classical, &unsafe_axioms)
    } else {
        String::new()
    };

    let message = if def.totality == Totality::Axiom {
        match def.kind {
            DefinitionKind::Primitive => format!("Primitive '{}' declared", def.name),
            _ => format!("Axiom '{}' declared{}", def.name, suffix),
        }
    } else {
        let mut parts = Vec::new();
        if has_axioms {
            parts.push(format!("axioms: {}{}", def.axioms.join(", "), suffix));
        }
        if has_primitives {
            parts.push(format!("primitives: {}", def.primitive_deps.join(", ")));
        }
        format!("Definition '{}' depends on {}", def.name, parts.join("; "))
    };

    handle_diagnostic(diagnostics, expander, Diagnostic::warning(message));
}

fn uses_interior_mutability_axioms(axioms: &[String]) -> bool {
    axioms.iter().any(|ax| {
        matches!(
            ax.as_str(),
            "may_panic_on_borrow_violation" | "concurrency_primitive" | "atomic_primitive"
        )
    })
}

fn report_inductive_axiom_dependencies(
    env: &Env,
    decl: &kernel::ast::InductiveDecl,
    expander: &mut Expander,
    diagnostics: &mut DiagnosticCollector,
) {
    let has_axioms = !decl.axioms.is_empty();
    let has_primitives = !decl.primitive_deps.is_empty();
    if !has_axioms && !has_primitives {
        return;
    }

    let suffix = if has_axioms {
        let classical =
            kernel::checker::axiom_dependencies_with_tag(env, &decl.axioms, AxiomTag::Classical);
        let unsafe_axioms =
            kernel::checker::axiom_dependencies_with_tag(env, &decl.axioms, AxiomTag::Unsafe);
        format_axiom_tag_suffix(&classical, &unsafe_axioms)
    } else {
        String::new()
    };

    let mut parts = Vec::new();
    if has_axioms {
        parts.push(format!("axioms: {}{}", decl.axioms.join(", "), suffix));
    }
    if has_primitives {
        parts.push(format!("primitives: {}", decl.primitive_deps.join(", ")));
    }
    let message = format!("Inductive '{}' depends on {}", decl.name, parts.join("; "));
    handle_diagnostic(diagnostics, expander, Diagnostic::warning(message));
}

fn format_axiom_tag_suffix(classical: &[String], unsafe_axioms: &[String]) -> String {
    let mut parts = Vec::new();
    if !classical.is_empty() {
        parts.push(format!("classical: {}", classical.join(", ")));
    }
    if !unsafe_axioms.is_empty() {
        parts.push(format!("unsafe: {}", unsafe_axioms.join(", ")));
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!(" ({})", parts.join(", "))
    }
}

fn validate_core_invariants(t: &Rc<Term>) -> Result<(), String> {
    kernel::checker::validate_core_term(t).map_err(|e| e.to_string())
}

fn classical_choice_type(false_name: &str) -> Rc<Term> {
    let prop = Term::sort(KernelLevel::Zero);
    let false_ty = Term::ind(false_name.to_string());
    let p = Term::var(0);
    let not_p = Term::pi(p.clone(), false_ty.clone(), BinderInfo::Default);
    let not_not_p = Term::pi(not_p, false_ty, BinderInfo::Default);
    let body = Term::pi(not_not_p, Term::var(1), BinderInfo::Default);
    Term::pi(prop, body, BinderInfo::Default)
}

fn nbe_normalize(env: &Env, term: Rc<Term>) -> Rc<Term> {
    match kernel::nbe::eval(&term, &vec![], env, Transparency::All) {
        Ok(val) => match kernel::nbe::quote(val, 0, env, Transparency::All) {
            Ok(t) => t,
            Err(_) => term,
        },
        Err(_) => term,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defeq_fuel_diagnostic_mentions_opaque_and_env_var() {
        let message = format_kernel_error(&kernel::checker::TypeError::DefEqFuelExhausted {
            context: kernel::checker::DefEqFuelContext::Unknown,
        });
        assert!(message.contains("opaque"));
        assert!(message.contains("--defeq-fuel"));
        assert!(message.contains("LRL_DEFEQ_FUEL"));
        assert!(message.contains("source = default"));
    }

    #[test]
    fn defeq_fuel_elab_error_uses_actionable_message() {
        let span = Span {
            start: 0,
            end: 0,
            line: 0,
            col: 0,
        };
        let err = ElabError::InferenceError(
            kernel::checker::TypeError::DefEqFuelExhausted {
                context: kernel::checker::DefEqFuelContext::Unknown,
            },
            span,
        );
        let message = format_elab_error(&err);
        assert!(message.contains("Definitional equality fuel exhausted"));
        assert!(message.contains("--defeq-fuel"));
        assert!(message.contains("LRL_DEFEQ_FUEL"));
        assert!(message.contains("source = default"));
    }

    #[test]
    fn defeq_fix_diagnostic_mentions_fix_and_partial() {
        let message = format_kernel_error(&kernel::checker::TypeError::DefEqFixUnfold);
        assert!(message.contains("fix"));
        assert!(message.contains("partial"));
    }

    #[test]
    fn defeq_fix_elab_error_uses_actionable_message() {
        let span = Span {
            start: 0,
            end: 0,
            line: 0,
            col: 0,
        };
        let err = ElabError::InferenceError(kernel::checker::TypeError::DefEqFixUnfold, span);
        let message = format_elab_error(&err);
        assert!(message.contains("fix"));
        assert!(message.contains("partial"));
    }
}
