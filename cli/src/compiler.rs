use frontend::diagnostics::{Diagnostic, DiagnosticCollector, DiagnosticHandler, Level};
use frontend::macro_expander::Expander;
use frontend::surface::Span;
use kernel::ast::{marker_name, TypeMarker};
use kernel::checker::Env;
use mir::codegen::{codegen_body, codegen_constant, codegen_recursors, sanitize_name};
use mir::errors::{MirSpan, MirSpanMap, SourceSpan};
use mir::typed_codegen::{TypedBody, TypedProgram};
use mir::Literal;

use ariadne::{Color, Label, Report, ReportKind, Source};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

const CODE_DRIVER_LINT_PANIC_FREE: &str = "C0006";

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, clap::ValueEnum)]
pub enum BackendMode {
    Dynamic,
    Typed,
    #[default]
    Auto,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CompileOptions {
    pub trace_macros: bool,
    pub panic_free: bool,
    pub require_axiom_tags: bool,
    pub macro_boundary_warn: bool,
    pub allow_redefine: bool,
    pub allow_axioms: bool,
    pub backend: BackendMode,
}

pub const PRELUDE_API_PATH: &str = "stdlib/prelude_api.lrl";
pub const PRELUDE_STD_CORE_NAT_PATH: &str = "stdlib/std/core/nat.lrl";
pub const PRELUDE_STD_CORE_NAT_LITERALS_PATH: &str = "stdlib/std/core/nat_literals.lrl";
pub const PRELUDE_STD_CORE_INT_PATH: &str = "stdlib/std/core/int.lrl";
pub const PRELUDE_STD_CORE_FLOAT_PATH: &str = "stdlib/std/core/float.lrl";
pub const PRELUDE_STD_CORE_BOOL_PATH: &str = "stdlib/std/core/bool.lrl";
pub const PRELUDE_STD_DATA_LIST_PATH: &str = "stdlib/std/data/list.lrl";
pub const PRELUDE_STD_DATA_OPTION_PATH: &str = "stdlib/std/data/option.lrl";
pub const PRELUDE_STD_DATA_RESULT_PATH: &str = "stdlib/std/data/result.lrl";
pub const PRELUDE_STD_DATA_PAIR_PATH: &str = "stdlib/std/data/pair.lrl";
pub const PRELUDE_STD_CONTROL_COMP_PATH: &str = "stdlib/std/control/comp.lrl";
pub const PRELUDE_IMPL_DYNAMIC_PATH: &str = "stdlib/prelude_impl_dynamic.lrl";
pub const PRELUDE_IMPL_TYPED_PATH: &str = "stdlib/prelude_impl_typed.lrl";

const PRELUDE_DYNAMIC_STACK: &[&str] = &[
    PRELUDE_API_PATH,
    PRELUDE_STD_CORE_NAT_PATH,
    PRELUDE_STD_CORE_NAT_LITERALS_PATH,
    PRELUDE_STD_CORE_INT_PATH,
    PRELUDE_STD_CORE_FLOAT_PATH,
    PRELUDE_STD_CORE_BOOL_PATH,
    PRELUDE_STD_DATA_LIST_PATH,
    PRELUDE_STD_DATA_OPTION_PATH,
    PRELUDE_STD_DATA_RESULT_PATH,
    PRELUDE_STD_DATA_PAIR_PATH,
    PRELUDE_IMPL_DYNAMIC_PATH,
];

const PRELUDE_TYPED_STACK: &[&str] = &[
    PRELUDE_API_PATH,
    PRELUDE_STD_CORE_NAT_PATH,
    PRELUDE_STD_CORE_NAT_LITERALS_PATH,
    PRELUDE_STD_CORE_INT_PATH,
    PRELUDE_STD_CORE_FLOAT_PATH,
    PRELUDE_STD_CORE_BOOL_PATH,
    PRELUDE_STD_DATA_LIST_PATH,
    PRELUDE_STD_DATA_OPTION_PATH,
    PRELUDE_STD_DATA_RESULT_PATH,
    PRELUDE_STD_DATA_PAIR_PATH,
    PRELUDE_IMPL_TYPED_PATH,
];

pub fn prelude_stack_for_backend(backend: BackendMode) -> &'static [&'static str] {
    match backend {
        BackendMode::Typed | BackendMode::Auto => PRELUDE_TYPED_STACK,
        BackendMode::Dynamic => PRELUDE_DYNAMIC_STACK,
    }
}

struct LoweredDef {
    name: String,
    body: mir::Body,
    derived_bodies: Vec<mir::Body>,
}

struct AxiomStub {
    safe_name: String,
    original_name: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SelectedBackend {
    Dynamic,
    Typed,
}

#[derive(Debug)]
struct BackendSelection {
    code: String,
    warning: Option<String>,
    selected_backend: SelectedBackend,
    executable_axiom_stubs: Vec<String>,
}

fn escape_json_string(input: &str) -> String {
    input
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
}

fn move_compiled_binary(staged_binary: &Path, destination: &Path) -> io::Result<()> {
    if destination.exists() && destination.is_dir() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("destination '{}' is a directory", destination.display()),
        ));
    }

    // Try an atomic rename first.
    match fs::rename(staged_binary, destination) {
        Ok(()) => Ok(()),
        Err(rename_error) => {
            // If atomic rename is unavailable (for example across filesystems), copy+remove.
            fs::copy(staged_binary, destination).map_err(|copy_error| {
                io::Error::new(
                    copy_error.kind(),
                    format!(
                        "failed to move binary (rename error: {}; copy error: {})",
                        rename_error, copy_error
                    ),
                )
            })?;
            fs::remove_file(staged_binary)?;
            Ok(())
        }
    }
}

fn format_executable_axiom_warning(backend: SelectedBackend, axiom_stubs: &[AxiomStub]) -> String {
    let backend_label = match backend {
        SelectedBackend::Dynamic => "dynamic",
        SelectedBackend::Typed => "typed",
    };
    let mut names: Vec<&str> = axiom_stubs
        .iter()
        .map(|stub| stub.original_name.as_str())
        .collect();
    names.sort();
    format!(
        "WARNING: executable axioms enabled for {} backend; runtime panic stubs emitted for: {}. Runtime may panic if any listed axiom is executed.",
        backend_label,
        names.join(", ")
    )
}

fn append_typed_axiom_stubs(mut typed_code: String, axiom_stubs: &[AxiomStub]) -> String {
    if axiom_stubs.is_empty() {
        return typed_code;
    }
    typed_code.push('\n');
    for stub in axiom_stubs {
        typed_code.push_str(&format!(
            "fn {}<T>() -> T {{ panic!(\"Axiom accessed at runtime (enabled via --allow-axioms): {}\") }}\n",
            stub.safe_name,
            stub.original_name
        ));
    }
    typed_code
}

fn dump_mir_if_enabled(label: &str, body: &mir::Body) {
    if std::env::var("LRL_DUMP_MIR").ok().is_none() {
        return;
    }
    let safe = label.replace(['/', '\\', ' '], "_");
    let mut path = PathBuf::from("build");
    path.push(format!("mir_dump_{}.txt", safe));
    let text = mir::pretty::pretty_print_body(body);
    if let Err(err) = fs::write(&path, text) {
        eprintln!(
            "Warning: failed to write MIR dump {}: {}",
            path.display(),
            err
        );
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

fn span_for_mir_location(location: Option<MirSpan>, span_table: &MirSpanMap) -> Option<Span> {
    location
        .and_then(|loc| span_table.get(&loc).copied())
        .map(to_frontend_span)
}

fn write_diagnostic_fallback<W: Write>(
    writer: &mut W,
    filename: &str,
    diag: &Diagnostic,
    render_error: &io::Error,
) {
    let _ = writeln!(
        writer,
        "Warning: failed to render diagnostic for {}: {}",
        filename, render_error
    );
    let _ = writeln!(writer, "{:?}: {}", diag.level, diag.message_with_code());
    if let Some(span) = diag.span {
        let _ = writeln!(writer, "  --> {}:{}..{}", filename, span.start, span.end);
    }
    for (span, label) in &diag.labels {
        let _ = writeln!(writer, "  = note: {}..{}: {}", span.start, span.end, label);
    }
}

pub fn compile_file(path: &str, output_path: Option<String>, options: CompileOptions) {
    compile_with_mir(
        path,
        output_path,
        options,
        prelude_stack_for_backend(options.backend),
    );
}

pub fn compile_file_with_prelude(
    path: &str,
    output_path: Option<String>,
    options: CompileOptions,
    prelude_path: &str,
) {
    compile_with_mir(path, output_path, options, &[prelude_path]);
}

// Deprecated alias
pub fn compile_file_to_mir(path: &str, options: CompileOptions) {
    compile_with_mir(
        path,
        None,
        options,
        prelude_stack_for_backend(options.backend),
    );
}

// Deprecated alias
pub fn compile_file_to_mir_with_output(
    path: &str,
    output_path: Option<String>,
    options: CompileOptions,
) {
    compile_with_mir(
        path,
        output_path,
        options,
        prelude_stack_for_backend(options.backend),
    );
}

fn compile_with_mir(
    path: &str,
    output_path: Option<String>,
    compile_options: CompileOptions,
    prelude_paths: &[&str],
) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.trace_verbose = compile_options.trace_macros;
    let user_policy = if compile_options.macro_boundary_warn {
        frontend::macro_expander::MacroBoundaryPolicy::Warn
    } else {
        frontend::macro_expander::MacroBoundaryPolicy::Deny
    };
    expander.set_macro_boundary_policy(user_policy);
    let pipeline_options = crate::driver::PipelineOptions {
        panic_free: compile_options.panic_free,
        require_axiom_tags: compile_options.require_axiom_tags,
        allow_axioms: compile_options.allow_axioms,
        prelude_frozen: true,
        allow_redefine: compile_options.allow_redefine,
        ..Default::default()
    };
    let prelude_options = crate::driver::PipelineOptions {
        panic_free: compile_options.panic_free,
        require_axiom_tags: false,
        allow_axioms: true,
        prelude_frozen: false,
        allow_redefine: false,
        ..Default::default()
    };

    let mut main_def_name: Option<String> = None;
    let mut diagnostics = DiagnosticCollector::new();

    // Helper to print diagnostics
    let print_diagnostics = |diagnostics: &DiagnosticCollector, filename: &str, content: &str| {
        for diag in &diagnostics.diagnostics {
            let kind = match diag.level {
                Level::Error => ReportKind::Error,
                Level::Warning => ReportKind::Warning,
                Level::Info => ReportKind::Advice,
            };

            let mut builder =
                Report::build(kind, filename, diag.span.map(|s| s.start).unwrap_or(0))
                    .with_message(&diag.message_with_code());

            if let Some(span) = diag.span {
                let color = match diag.level {
                    Level::Error => Color::Red,
                    Level::Warning => Color::Yellow,
                    Level::Info => Color::Blue,
                };
                builder = builder.with_label(
                    Label::new((filename, span.start..span.end))
                        .with_message(&diag.message_with_code())
                        .with_color(color),
                );
            }

            for (span, label) in &diag.labels {
                builder = builder.with_label(
                    Label::new((filename, span.start..span.end))
                        .with_message(label)
                        .with_color(Color::Cyan),
                );
            }

            let report = builder.finish();
            if let Err(render_error) = report.print((filename, Source::from(content))) {
                let mut stderr = io::stderr().lock();
                write_diagnostic_fallback(&mut stderr, filename, diag, &render_error);
            }
        }
    };

    // Load Prelude stack (public API first, then backend-specific implementation layer).
    let mut prelude_modules = Vec::new();
    for prelude_path in prelude_paths {
        if !Path::new(prelude_path).exists() {
            continue;
        }
        let content = match fs::read_to_string(prelude_path) {
            Ok(content) => content,
            Err(err) => {
                println!("Error reading prelude {}: {:?}", prelude_path, err);
                return;
            }
        };
        let prelude_module = crate::driver::module_id_for_source(prelude_path);
        expander.set_macro_boundary_policy(frontend::macro_expander::MacroBoundaryPolicy::Deny);
        crate::set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
        if !prelude_modules.is_empty() {
            expander.set_default_imports(prelude_modules.clone());
        }
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        let _ = crate::driver::process_code(
            &content,
            prelude_path,
            &mut env,
            &mut expander,
            &prelude_options,
            &mut diagnostics,
        );
        expander.clear_macro_boundary_allowlist();
        env.set_allow_reserved_primitives(allow_reserved);
        expander.set_macro_boundary_policy(user_policy);
        if diagnostics.has_errors() {
            print_diagnostics(&diagnostics, prelude_path, &content);
            println!("Prelude compilation failed.");
            return;
        }
        prelude_modules.push(prelude_module);
    }
    if !prelude_modules.is_empty() {
        if let Err(err) = env.init_marker_registry() {
            println!("Failed to initialize marker registry: {}", err);
            return;
        }
        expander.set_default_imports(prelude_modules);
    }

    env.set_allow_redefinition(compile_options.allow_redefine);

    // Load Main File
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            println!("Error reading file: {} ({:?})", path, e);
            return;
        }
    };

    let result = match crate::driver::process_code(
        &content,
        path,
        &mut env,
        &mut expander,
        &pipeline_options,
        &mut diagnostics,
    ) {
        Ok(res) => res,
        Err(_) => {
            print_diagnostics(&diagnostics, path, &content);
            return;
        }
    };

    if diagnostics.has_errors() {
        print_diagnostics(&diagnostics, path, &content);
        println!("Compilation aborted due to errors.");
        return;
    }

    if !compile_options.allow_axioms {
        let mut blocked = Vec::new();
        for name in &result.deployed_definitions {
            if let Some(def) = env.definitions().get(name) {
                if def.value.is_some()
                    && !def.axioms.is_empty()
                    && !def.noncomputable
                    && def.totality != kernel::ast::Totality::Unsafe
                {
                    blocked.push((name.clone(), def.axioms.clone()));
                }
            }
        }
        if !blocked.is_empty() {
            for (name, axioms) in &blocked {
                diagnostics.handle(Diagnostic::error(format!(
                    "Definition '{}' depends on axioms ({}) and is not marked noncomputable; rerun with --allow-axioms or mark it noncomputable",
                    name,
                    axioms.join(", ")
                )));
            }
            print_diagnostics(&diagnostics, path, &content);
            println!("Compilation aborted due to axiom dependencies.");
            return;
        }
    }

    // Codegen Phase
    let mut names: Vec<_> = env.definitions().keys().cloned().collect();
    names.sort();
    let ids = mir::types::IdRegistry::from_env(&env);
    if ids.has_errors() {
        for err in ids.errors() {
            let mut diagnostic = Diagnostic::error(err.to_string());
            if let Some(span) = err.span() {
                diagnostic = diagnostic.with_span(to_frontend_span(span));
            }
            diagnostics.handle(diagnostic);
        }
        print_diagnostics(&diagnostics, path, &content);
        println!("Compilation aborted due to marker registry errors.");
        return;
    }

    let mut lowered_defs = Vec::new();
    let mut axiom_stubs = Vec::new();

    let is_builtin_nonexecutable_axiom = |name: &str| {
        name == marker_name(TypeMarker::InteriorMutable)
            || name == marker_name(TypeMarker::MayPanicOnBorrowViolation)
            || name == marker_name(TypeMarker::ConcurrencyPrimitive)
            || name == marker_name(TypeMarker::AtomicPrimitive)
            || name == marker_name(TypeMarker::Indexable)
            || name == "Shared"
            || name == "Mut"
            || name == "Ref"
            || name == "borrow_shared"
            || name == "borrow_mut"
            || name == "index_vec_dyn"
            || name == "index_slice"
            || name == "index_array"
            || name == "append"
            || name == "eval"
            || name == "Dyn"
            || name == "EvalCap"
    };

    for name in names {
        if let Some(def) = env.definitions().get(&name) {
            // Skip canonical constructor declarations, but keep ordinary definitions
            // whose normalized value happens to be a constructor.
            if !env.constructor_candidates(&name).is_empty() {
                continue;
            }

            if def.value.is_none() {
                if def.totality == kernel::ast::Totality::Axiom {
                    if is_builtin_nonexecutable_axiom(&name) {
                        continue;
                    }
                    axiom_stubs.push(AxiomStub {
                        safe_name: sanitize_name(&name),
                        original_name: name.clone(),
                    });
                    continue;
                }
                continue; // Should not happen for non-axiom definitions without value
            }

            // Lower to MIR
            let term_span_map = result.term_span_maps.get(&name).cloned().map(Rc::new);
            let mut ctx = match mir::lower::LoweringContext::new_with_metadata(
                vec![],
                def.ty.clone(),
                &env,
                &ids,
                term_span_map,
                Some(name.clone()),
                Some(Rc::new(def.capture_modes.clone())),
            ) {
                Ok(ctx) => ctx,
                Err(e) => {
                    let mut diagnostic =
                        Diagnostic::error(format!("Lowering error in {}: {}", name, e));
                    if let Some(span) = e.span() {
                        diagnostic = diagnostic.with_span(to_frontend_span(span));
                    }
                    diagnostics.handle(diagnostic);
                    continue;
                }
            };
            let dest = mir::Place::from(mir::Local(0));
            let target = mir::BasicBlock(1);
            ctx.body.basic_blocks.push(mir::BasicBlockData {
                statements: vec![],
                terminator: Some(mir::Terminator::Return),
            });

            if let Some(val) = &def.value {
                if let Err(e) = ctx.lower_term(val, dest, target) {
                    let mut diagnostic =
                        Diagnostic::error(format!("Lowering error in {}: {}", name, e));
                    if let Some(span) = e.span() {
                        diagnostic = diagnostic.with_span(to_frontend_span(span));
                    }
                    diagnostics.handle(diagnostic);
                    continue;
                }
            }

            mir::transform::storage::insert_exit_storage_deads(&mut ctx.body);

            // Safety Checks
            let mut typing = mir::analysis::typing::TypingChecker::new(&ctx.body);
            typing.check();
            for e in typing.errors() {
                diagnostics.handle(
                    Diagnostic::error(format!("MIR typing error in {}: {}", name, e))
                        .with_code(e.diagnostic_code()),
                );
            }

            let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
            ownership.analyze();
            let ownership_errors = ownership.check_structured();
            if !ownership_errors.is_empty() {
                dump_mir_if_enabled(&name, &ctx.body);
            }
            for e in &ownership_errors {
                let mut diagnostic =
                    Diagnostic::error(format!("Ownership error in {}: {}", name, e))
                        .with_code(e.diagnostic_code());
                if let Some(span) = span_for_mir_location(e.location(), &ctx.span_table) {
                    diagnostic = diagnostic.with_span(span);
                }
                diagnostics.handle(diagnostic);
            }

            let mut nll = mir::analysis::nll::NllChecker::new(&ctx.body);
            nll.check();
            let nll_result = nll.into_result();
            for e in &nll_result.errors {
                let mut diagnostic = Diagnostic::error(format!("Borrow error in {}: {}", name, e))
                    .with_code(e.diagnostic_code());
                if let Some(span) = span_for_mir_location(e.location(), &ctx.span_table) {
                    diagnostic = diagnostic.with_span(span);
                }
                diagnostics.handle(diagnostic);
            }
            let panic_free_runtime_checks =
                compile_options.panic_free && !nll_result.runtime_checks.is_empty();
            if panic_free_runtime_checks {
                diagnostics.handle(
                    Diagnostic::error(format!(
                        "Panic-free profile violation in {}: borrow checking inserted {} runtime check(s).",
                        name,
                        nll_result.runtime_checks.len()
                    ))
                    .with_code(CODE_DRIVER_LINT_PANIC_FREE),
                );
            }
            if nll_result.is_ok() && !panic_free_runtime_checks {
                nll_result.inject_runtime_checks(&mut ctx.body);
            }

            if compile_options.panic_free {
                let mut linter = mir::lints::PanicFreeLinter::new(&ctx.body);
                linter.check();
                for e in linter.errors {
                    diagnostics.handle(
                        Diagnostic::error(format!("Lint error in {}: {}", name, e))
                            .with_code(CODE_DRIVER_LINT_PANIC_FREE),
                    );
                }
            }

            let mut derived_bodies = ctx.derived_bodies.borrow_mut();
            let derived_span_tables = ctx.derived_span_tables.borrow();
            for (i, body) in derived_bodies.iter_mut().enumerate() {
                mir::transform::storage::insert_exit_storage_deads(body);
                let mut typing = mir::analysis::typing::TypingChecker::new(body);
                typing.check();
                for e in typing.errors() {
                    diagnostics.handle(
                        Diagnostic::error(format!(
                            "MIR typing error in {} closure {}: {}",
                            name, i, e
                        ))
                        .with_code(e.diagnostic_code()),
                    );
                }
                let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(body);
                ownership.analyze();
                let ownership_errors = ownership.check_structured();
                if !ownership_errors.is_empty() {
                    dump_mir_if_enabled(&format!("{}_closure_{}", name, i), body);
                }
                for e in &ownership_errors {
                    let mut diagnostic = Diagnostic::error(format!(
                        "Ownership error in {} closure {}: {}",
                        name, i, e
                    ))
                    .with_code(e.diagnostic_code());
                    if let Some(span_table) = derived_span_tables.get(i) {
                        if let Some(span) = span_for_mir_location(e.location(), span_table) {
                            diagnostic = diagnostic.with_span(span);
                        }
                    }
                    diagnostics.handle(diagnostic);
                }
                let mut nll = mir::analysis::nll::NllChecker::new(body);
                nll.check();
                let nll_result = nll.into_result();
                for e in &nll_result.errors {
                    let mut diagnostic =
                        Diagnostic::error(format!("Borrow error in {} closure {}: {}", name, i, e))
                            .with_code(e.diagnostic_code());
                    if let Some(span_table) = derived_span_tables.get(i) {
                        if let Some(span) = span_for_mir_location(e.location(), span_table) {
                            diagnostic = diagnostic.with_span(span);
                        }
                    }
                    diagnostics.handle(diagnostic);
                }
                let panic_free_runtime_checks =
                    compile_options.panic_free && !nll_result.runtime_checks.is_empty();
                if panic_free_runtime_checks {
                    diagnostics.handle(
                        Diagnostic::error(format!(
                            "Panic-free profile violation in {} closure {}: borrow checking inserted {} runtime check(s).",
                            name,
                            i,
                            nll_result.runtime_checks.len()
                        ))
                        .with_code(CODE_DRIVER_LINT_PANIC_FREE),
                    );
                }
                if nll_result.is_ok() && !panic_free_runtime_checks {
                    nll_result.inject_runtime_checks(body);
                }
                if compile_options.panic_free {
                    let mut linter = mir::lints::PanicFreeLinter::new(body);
                    linter.check();
                    for e in linter.errors {
                        diagnostics.handle(
                            Diagnostic::error(format!(
                                "Lint error in {} closure {}: {}",
                                name, i, e
                            ))
                            .with_code(CODE_DRIVER_LINT_PANIC_FREE),
                        );
                    }
                }
            }
            drop(derived_span_tables);
            drop(derived_bodies);

            if diagnostics.has_errors() {
                continue;
            }

            // Optimizations
            mir::transform::erasure::erase_proofs(&mut ctx.body);
            for body in ctx.derived_bodies.borrow_mut().iter_mut() {
                mir::transform::erasure::erase_proofs(body);
            }
            mir::transform::dce::eliminate_dead_code(&mut ctx.body);
            for body in ctx.derived_bodies.borrow_mut().iter_mut() {
                mir::transform::dce::eliminate_dead_code(body);
            }
            mir::transform::dce::simplify_cfg(&mut ctx.body);
            for body in ctx.derived_bodies.borrow_mut().iter_mut() {
                mir::transform::dce::simplify_cfg(body);
            }
            mir::transform::inline::optimize(&mut ctx.body);
            for body in ctx.derived_bodies.borrow_mut().iter_mut() {
                mir::transform::inline::optimize(body);
            }

            let derived_bodies = ctx.derived_bodies.borrow().clone();
            let safe_name = sanitize_name(&name);
            lowered_defs.push(LoweredDef {
                name: safe_name,
                body: ctx.body,
                derived_bodies,
            });
        }
    }

    // Determine Main
    if let Some(last_name) = result.deployed_definitions.last() {
        main_def_name = Some(sanitize_name(last_name));
    }

    if diagnostics.has_errors() {
        print_diagnostics(&diagnostics, path, &content);
        println!("Codegen aborted due to safety errors.");
        return;
    }

    let backend_selection = match select_backend_code(
        compile_options.backend,
        compile_options.allow_axioms,
        &env,
        &ids,
        &lowered_defs,
        &axiom_stubs,
        &main_def_name,
    ) {
        Ok(result) => result,
        Err(message) => {
            diagnostics.handle(Diagnostic::error(message));
            print_diagnostics(&diagnostics, path, &content);
            return;
        }
    };
    if let Some(warning) = backend_selection.warning.as_deref() {
        println!("{}", warning);
    }

    // Write output source to a unique file to avoid races across concurrent compiles.
    let build_dir = Path::new("build");
    if let Err(e) = fs::create_dir_all(build_dir) {
        println!("Error creating build directory: {:?}", e);
        return;
    }
    let unique_tag = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let source_file = build_dir.join(format!("output_{}_{}.rs", std::process::id(), unique_tag));
    let binary_file = output_path.unwrap_or_else(|| "output".to_string());
    let staged_binary_file =
        build_dir.join(format!("output_{}_{}.bin", std::process::id(), unique_tag));
    let incremental_dir = build_dir.join("incremental");
    if let Err(e) = fs::create_dir_all(&incremental_dir) {
        println!("Error creating incremental cache directory: {:?}", e);
        return;
    }

    if let Err(e) = fs::write(&source_file, backend_selection.code) {
        println!("Error writing output file: {:?}", e);
        return;
    }

    if !backend_selection.executable_axiom_stubs.is_empty() {
        let artifact_file = build_dir.join(format!(
            "output_{}_{}.artifacts.json",
            std::process::id(),
            unique_tag
        ));
        let backend_name = match backend_selection.selected_backend {
            SelectedBackend::Dynamic => "dynamic",
            SelectedBackend::Typed => "typed",
        };
        let axiom_list = backend_selection
            .executable_axiom_stubs
            .iter()
            .map(|name| format!("\"{}\"", escape_json_string(name)))
            .collect::<Vec<_>>()
            .join(", ");
        let metadata = format!(
            "{{\n  \"selected_backend\": \"{}\",\n  \"contains_executable_axioms\": true,\n  \"axiom_stubs\": [{}],\n  \"safety_note\": \"axioms are non-executable by default; --allow-axioms opted into panic stubs\"\n}}\n",
            backend_name, axiom_list
        );
        if let Err(err) = fs::write(&artifact_file, metadata) {
            println!(
                "Warning: failed to write axiom artifact metadata {}: {}",
                artifact_file.display(),
                err
            );
        } else {
            println!(
                "WARNING: executable axiom metadata written to {}",
                artifact_file.display()
            );
        }
    }

    println!("Compiling {} to {}...", source_file.display(), binary_file);
    let status = std::process::Command::new("rustc")
        .arg(&source_file)
        .arg("-o")
        .arg(&staged_binary_file)
        .arg("-C")
        .arg(format!("incremental={}", incremental_dir.display()))
        .status();

    match status {
        Ok(s) => {
            if s.success() {
                if let Err(e) =
                    move_compiled_binary(&staged_binary_file, &PathBuf::from(&binary_file))
                {
                    println!(
                        "Compilation succeeded, but failed to place binary '{}': {}",
                        binary_file, e
                    );
                    return;
                }
                println!("Compilation successful. Binary '{}' created.", binary_file);
            } else {
                println!("Compilation failed.");
            }
        }
        Err(e) => println!("Error running rustc: {:?}", e),
    }
}

fn select_backend_code(
    backend: BackendMode,
    allow_axioms: bool,
    env: &Env,
    ids: &mir::types::IdRegistry,
    lowered_defs: &[LoweredDef],
    axiom_stubs: &[AxiomStub],
    main_def_name: &Option<String>,
) -> Result<BackendSelection, String> {
    match backend {
        BackendMode::Dynamic => {
            if !axiom_stubs.is_empty() && !allow_axioms {
                let mut names: Vec<&str> = axiom_stubs
                    .iter()
                    .map(|stub| stub.original_name.as_str())
                    .collect();
                names.sort();
                return Err(
                    format!(
                        "Dynamic backend encountered axiom stubs ({}); rerun with --allow-axioms to opt in to executable panic stubs.",
                        names.join(", ")
                    ),
                );
            }
            let warning = if allow_axioms && !axiom_stubs.is_empty() {
                Some(format_executable_axiom_warning(
                    SelectedBackend::Dynamic,
                    axiom_stubs,
                ))
            } else {
                None
            };
            Ok(BackendSelection {
                code: build_dynamic_code(env, ids, lowered_defs, axiom_stubs, main_def_name),
                warning,
                selected_backend: SelectedBackend::Dynamic,
                executable_axiom_stubs: if allow_axioms {
                    axiom_stubs
                        .iter()
                        .map(|stub| stub.original_name.clone())
                        .collect()
                } else {
                    Vec::new()
                },
            })
        }
        BackendMode::Typed => {
            if !axiom_stubs.is_empty() {
                if !allow_axioms {
                    return Err(
                        "Typed backend does not support axiom stubs unless --allow-axioms is enabled; use --backend dynamic/auto or rerun with --allow-axioms"
                            .to_string(),
                    );
                }
            }
            let program = build_typed_program(lowered_defs, main_def_name.clone());
            let typed_code = mir::typed_codegen::codegen_program(env, ids, &program)
                .map_err(|err| format!("Typed backend unsupported: {}", err))?;
            let warning = if !axiom_stubs.is_empty() && allow_axioms {
                Some(format_executable_axiom_warning(
                    SelectedBackend::Typed,
                    axiom_stubs,
                ))
            } else {
                None
            };
            Ok(BackendSelection {
                code: append_typed_axiom_stubs(typed_code, axiom_stubs),
                warning,
                selected_backend: SelectedBackend::Typed,
                executable_axiom_stubs: if allow_axioms {
                    axiom_stubs
                        .iter()
                        .map(|stub| stub.original_name.clone())
                        .collect()
                } else {
                    Vec::new()
                },
            })
        }
        BackendMode::Auto => {
            if !axiom_stubs.is_empty() && !allow_axioms {
                return Err(
                    "Program requires axiom stubs, but executable axioms are disabled. Rerun with --allow-axioms (typed emits typed panic stubs; dynamic fallback emits Value panic stubs)."
                        .to_string(),
                );
            }
            if !axiom_stubs.is_empty() && allow_axioms {
                let program = build_typed_program(lowered_defs, main_def_name.clone());
                return match mir::typed_codegen::codegen_program(env, ids, &program) {
                    Ok(code) => Ok(BackendSelection {
                        code: append_typed_axiom_stubs(code, axiom_stubs),
                        warning: Some(format_executable_axiom_warning(
                            SelectedBackend::Typed,
                            axiom_stubs,
                        )),
                        selected_backend: SelectedBackend::Typed,
                        executable_axiom_stubs: axiom_stubs
                            .iter()
                            .map(|stub| stub.original_name.clone())
                            .collect(),
                    }),
                    Err(err) => Ok(BackendSelection {
                        code: build_dynamic_code(
                            env,
                            ids,
                            lowered_defs,
                            axiom_stubs,
                            main_def_name,
                        ),
                        warning: Some(format!(
                            "Warning: typed backend unsupported: {}; falling back to dynamic.",
                            err
                        )),
                        selected_backend: SelectedBackend::Dynamic,
                        executable_axiom_stubs: axiom_stubs
                            .iter()
                            .map(|stub| stub.original_name.clone())
                            .collect(),
                    }),
                };
            }
            let program = build_typed_program(lowered_defs, main_def_name.clone());
            match mir::typed_codegen::codegen_program(env, ids, &program) {
                Ok(code) => Ok(BackendSelection {
                    code,
                    warning: None,
                    selected_backend: SelectedBackend::Typed,
                    executable_axiom_stubs: Vec::new(),
                }),
                Err(err) => Ok(BackendSelection {
                    code: build_dynamic_code(env, ids, lowered_defs, axiom_stubs, main_def_name),
                    warning: Some(format!(
                        "Warning: typed backend unsupported: {}; falling back to dynamic.",
                        err
                    )),
                    selected_backend: SelectedBackend::Dynamic,
                    executable_axiom_stubs: Vec::new(),
                }),
            }
        }
    }
}

fn build_dynamic_code(
    env: &Env,
    ids: &mir::types::IdRegistry,
    lowered_defs: &[LoweredDef],
    axiom_stubs: &[AxiomStub],
    main_def_name: &Option<String>,
) -> String {
    let mut code = String::new();
    code.push_str("#![allow(dead_code, unused_variables, unused_parens, unreachable_patterns)]\n");
    code.push_str(&mir::codegen::codegen_prelude());
    code.push('\n');

    let mut ind_names: Vec<_> = env.inductives.keys().cloned().collect();
    ind_names.sort();
    for name in ind_names {
        if let Some(decl) = env.inductives.get(&name) {
            let ctors = &decl.ctors;
            for (i, ctor) in ctors.iter().enumerate() {
                let safe_ctor_name = sanitize_name(&ctor.name);
                let mut arity = 0;
                let mut t = &ctor.ty;
                while let kernel::ast::Term::Pi(_, b, _, _) = &**t {
                    arity += 1;
                    t = b;
                }

                let ctor_id = ids
                    .ctor_id(&name, i)
                    .unwrap_or_else(|| mir::types::CtorId::new(mir::types::AdtId::new(&name), i));
                let ctor_val_code = codegen_constant(&Literal::InductiveCtor(ctor_id, arity), 0);
                code.push_str(&format!(
                    "fn {}() -> Value {{ {} }}\n",
                    safe_ctor_name, ctor_val_code
                ));
            }
        }
    }

    for stub in axiom_stubs {
        code.push_str(&format!(
            "fn {}() -> Value {{ panic!(\"Axiom accessed at runtime (enabled via --allow-axioms): {}\") }}\n",
            stub.safe_name, stub.original_name
        ));
    }

    let mut closure_idx = 0usize;
    for def in lowered_defs {
        let closure_base = closure_idx;
        for (i, body) in def.derived_bodies.iter().enumerate() {
            let closure_name = format!("closure_{}", closure_base + i);
            code.push_str(&codegen_body(&closure_name, body, closure_base));
            code.push('\n');
        }

        code.push_str(&codegen_body(&def.name, &def.body, closure_base));
        code.push('\n');

        closure_idx += def.derived_bodies.len();
    }

    code.push_str(&codegen_recursors(&env.inductives, env));

    code.push_str("fn main() {\n");
    if let Some(name) = main_def_name {
        code.push_str(&format!("    let result = {}();\n", name));
        code.push_str("    println!(\"Result: {}\", runtime_result_to_string(&result));\n");
    }
    code.push_str("}\n");

    code
}

fn build_typed_program(lowered_defs: &[LoweredDef], main_def_name: Option<String>) -> TypedProgram {
    let mut defs = Vec::new();
    let mut closures = Vec::new();
    let mut closure_base = 0usize;

    for def in lowered_defs {
        defs.push(TypedBody {
            name: def.name.clone(),
            body: def.body.clone(),
            closure_base,
        });
        for (idx, body) in def.derived_bodies.iter().enumerate() {
            closures.push(TypedBody {
                name: format!("closure_{}", closure_base + idx),
                body: body.clone(),
                closure_base,
            });
        }
        closure_base += def.derived_bodies.len();
    }

    TypedProgram {
        defs,
        closures,
        main_name: main_def_name,
    }
}

/// Result of compiling a definition, for testing purposes
#[derive(Debug, Clone)]
pub struct DefCompileResult {
    pub name: String,
    pub lowering_errors: Vec<String>,
    pub typing_errors: Vec<String>,
    pub ownership_errors: Vec<String>,
    pub borrow_errors: Vec<mir::errors::BorrowError>,
}

/// Compile a string of LRL code and return compilation results for testing
pub fn compile_string_for_test(source: &str) -> Vec<DefCompileResult> {
    compile_string_with_prelude(source, None)
}

/// Compile with optional explicit prelude
pub fn compile_string_with_prelude(source: &str, prelude: Option<&str>) -> Vec<DefCompileResult> {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut results = Vec::new();
    expander.set_macro_boundary_policy(frontend::macro_expander::MacroBoundaryPolicy::Deny);

    // Load prelude
    let prelude_content = prelude.map(|p| p.to_string());
    let has_prelude = prelude_content.is_some();

    if let Some(content) = prelude_content.as_deref() {
        let prelude_module = crate::driver::module_id_for_source("prelude");
        let options = crate::driver::PipelineOptions {
            prelude_frozen: false,
            allow_redefine: false,
            ..Default::default()
        };
        let mut prelude_diagnostics = DiagnosticCollector::new();
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        expander.set_macro_boundary_policy(frontend::macro_expander::MacroBoundaryPolicy::Deny);
        crate::set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
        let _ = crate::driver::process_code(
            content,
            "prelude",
            &mut env,
            &mut expander,
            &options,
            &mut prelude_diagnostics,
        );
        expander.clear_macro_boundary_allowlist();
        env.set_allow_reserved_primitives(allow_reserved);
        expander.set_macro_boundary_policy(frontend::macro_expander::MacroBoundaryPolicy::Deny);
    }

    let mut diagnostics = DiagnosticCollector::new();
    let options = crate::driver::PipelineOptions {
        prelude_frozen: has_prelude,
        allow_redefine: false,
        ..Default::default()
    };
    let proc_result = crate::driver::process_code(
        source,
        "test",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    if let Ok(res) = proc_result {
        let ids = mir::types::IdRegistry::from_env(&env);
        if ids.has_errors() {
            results.push(DefCompileResult {
                name: "<id-registry>".to_string(),
                lowering_errors: ids.errors().iter().map(|e| e.to_string()).collect(),
                typing_errors: Vec::new(),
                ownership_errors: Vec::new(),
                borrow_errors: Vec::new(),
            });
            return results;
        }
        for name in res.deployed_definitions {
            let mut lowering_errors = Vec::new();
            let mut typing_errors = Vec::new();
            let mut ownership_errors = Vec::new();
            let mut borrow_errors = Vec::new();

            if let Some(def) = env.definitions().get(&name) {
                if !env.constructor_candidates(&name).is_empty() {
                    continue;
                }
                if let Some(val) = &def.value {
                    // Lower and Check
                    let mut ctx = match mir::lower::LoweringContext::new_with_metadata(
                        vec![],
                        def.ty.clone(),
                        &env,
                        &ids,
                        None,
                        Some(name.clone()),
                        Some(Rc::new(def.capture_modes.clone())),
                    ) {
                        Ok(ctx) => ctx,
                        Err(e) => {
                            lowering_errors.push(format!("Lowering error in {}: {}", name, e));
                            results.push(DefCompileResult {
                                name,
                                lowering_errors,
                                typing_errors,
                                ownership_errors,
                                borrow_errors,
                            });
                            continue;
                        }
                    };
                    let dest = mir::Place::from(mir::Local(0));
                    let target = mir::BasicBlock(1);
                    ctx.body.basic_blocks.push(mir::BasicBlockData {
                        statements: vec![],
                        terminator: Some(mir::Terminator::Return),
                    });
                    if let Err(e) = ctx.lower_term(val, dest, target) {
                        lowering_errors.push(format!("Lowering error in {}: {}", name, e));
                        results.push(DefCompileResult {
                            name,
                            lowering_errors,
                            typing_errors,
                            ownership_errors,
                            borrow_errors,
                        });
                        continue;
                    }

                    mir::transform::storage::insert_exit_storage_deads(&mut ctx.body);

                    let mut typing = mir::analysis::typing::TypingChecker::new(&ctx.body);
                    typing.check();
                    for e in typing.errors() {
                        typing_errors.push(e.to_string());
                    }

                    let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
                    ownership.analyze();
                    ownership_errors.extend(ownership.check());

                    let mut nll = mir::analysis::nll::NllChecker::new(&ctx.body);
                    nll.check();
                    let nll_result = nll.into_result();
                    borrow_errors.extend(nll_result.errors);
                }
            }

            results.push(DefCompileResult {
                name,
                lowering_errors,
                typing_errors,
                ownership_errors,
                borrow_errors,
            });
        }
    }

    results
}

#[cfg(test)]
mod tests {
    use super::*;
    use frontend::diagnostics::DiagnosticCollector;
    use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
    use kernel::ast::FunctionKind;
    use kernel::checker::Env;
    use std::io::{self, Write};

    const TEST_PRELUDE: &str = r#"(
inductive copy Nat (sort 1)
  (ctor zero Nat)
  (ctor succ (pi n Nat Nat)))

(inductive copy Bool (sort 1)
  (ctor true Bool)
  (ctor false Bool))

(def add (pi n Nat (pi m Nat Nat))
  (lam n Nat
    (lam m Nat
      (match n Nat
        (case (zero) m)
        (case (succ m' ih) (succ ih))))))
"#;

    fn local(name: &str, ty: mir::types::MirType) -> mir::LocalDecl {
        mir::LocalDecl::new(ty, Some(name.to_string()))
    }

    fn nat_const(value: u64) -> mir::Operand {
        mir::Operand::Constant(Box::new(mir::Constant {
            literal: mir::Literal::Nat(value),
            ty: mir::types::MirType::Nat,
        }))
    }

    fn build_body(
        arg_count: usize,
        local_decls: Vec<mir::LocalDecl>,
        statements: Vec<mir::Statement>,
        terminator: mir::Terminator,
    ) -> mir::Body {
        let mut body = mir::Body::new(arg_count);
        body.local_decls = local_decls;
        body.basic_blocks.push(mir::BasicBlockData {
            statements,
            terminator: Some(terminator),
        });
        body
    }

    fn auto_fallback_warning_for_body(body: mir::Body) -> String {
        let env = Env::new();
        let ids = mir::types::IdRegistry::from_env(&env);
        let lowered_defs = vec![LoweredDef {
            name: "entry".to_string(),
            body,
            derived_bodies: Vec::new(),
        }];

        let backend = select_backend_code(
            BackendMode::Auto,
            false,
            &env,
            &ids,
            &lowered_defs,
            &Vec::new(),
            &Some("entry".to_string()),
        )
        .expect("auto backend should succeed via dynamic fallback");

        assert!(
            backend.code.contains("enum Value"),
            "expected dynamic fallback code, got:\n{}",
            backend.code
        );
        backend
            .warning
            .expect("auto fallback warning should be present")
    }

    #[test]
    fn backend_mode_default_is_auto() {
        assert_eq!(BackendMode::default(), BackendMode::Auto);
    }

    #[test]
    fn backend_mode_uses_expected_preludes() {
        assert_eq!(
            prelude_stack_for_backend(BackendMode::Typed),
            &[
                PRELUDE_API_PATH,
                PRELUDE_STD_CORE_NAT_PATH,
                PRELUDE_STD_CORE_NAT_LITERALS_PATH,
                PRELUDE_STD_CORE_INT_PATH,
                PRELUDE_STD_CORE_FLOAT_PATH,
                PRELUDE_STD_CORE_BOOL_PATH,
                PRELUDE_STD_DATA_LIST_PATH,
                PRELUDE_STD_DATA_OPTION_PATH,
                PRELUDE_STD_DATA_RESULT_PATH,
                PRELUDE_STD_DATA_PAIR_PATH,
                PRELUDE_IMPL_TYPED_PATH,
            ]
        );
        assert_eq!(
            prelude_stack_for_backend(BackendMode::Auto),
            &[
                PRELUDE_API_PATH,
                PRELUDE_STD_CORE_NAT_PATH,
                PRELUDE_STD_CORE_NAT_LITERALS_PATH,
                PRELUDE_STD_CORE_INT_PATH,
                PRELUDE_STD_CORE_FLOAT_PATH,
                PRELUDE_STD_CORE_BOOL_PATH,
                PRELUDE_STD_DATA_LIST_PATH,
                PRELUDE_STD_DATA_OPTION_PATH,
                PRELUDE_STD_DATA_RESULT_PATH,
                PRELUDE_STD_DATA_PAIR_PATH,
                PRELUDE_IMPL_TYPED_PATH,
            ]
        );
        assert_eq!(
            prelude_stack_for_backend(BackendMode::Dynamic),
            &[
                PRELUDE_API_PATH,
                PRELUDE_STD_CORE_NAT_PATH,
                PRELUDE_STD_CORE_NAT_LITERALS_PATH,
                PRELUDE_STD_CORE_INT_PATH,
                PRELUDE_STD_CORE_FLOAT_PATH,
                PRELUDE_STD_CORE_BOOL_PATH,
                PRELUDE_STD_DATA_LIST_PATH,
                PRELUDE_STD_DATA_OPTION_PATH,
                PRELUDE_STD_DATA_RESULT_PATH,
                PRELUDE_STD_DATA_PAIR_PATH,
                PRELUDE_IMPL_DYNAMIC_PATH,
            ]
        );
    }

    #[test]
    fn auto_backend_rejects_axiom_stubs_without_allow_axioms() {
        let env = Env::new();
        let ids = mir::types::IdRegistry::from_env(&env);
        let lowered_defs = Vec::new();
        let axiom_stubs = vec![AxiomStub {
            safe_name: "axiom_stub".to_string(),
            original_name: "axiom_stub".to_string(),
        }];

        let err = select_backend_code(
            BackendMode::Auto,
            false,
            &env,
            &ids,
            &lowered_defs,
            &axiom_stubs,
            &None,
        )
        .expect_err("auto backend should reject executable axioms without --allow-axioms");

        assert!(
            err.contains("Program requires axiom stubs"),
            "expected explicit allow-axioms diagnostic, got: {}",
            err
        );
    }

    #[test]
    fn typed_backend_rejects_axiom_stubs() {
        let env = Env::new();
        let ids = mir::types::IdRegistry::from_env(&env);
        let lowered_defs = Vec::new();
        let axiom_stubs = vec![AxiomStub {
            safe_name: "axiom_stub".to_string(),
            original_name: "axiom_stub".to_string(),
        }];

        let err = select_backend_code(
            BackendMode::Typed,
            false,
            &env,
            &ids,
            &lowered_defs,
            &axiom_stubs,
            &None,
        )
        .expect_err("typed backend must reject axiom stubs");

        assert!(
            err.contains("Typed backend does not support axiom stubs"),
            "expected typed backend axiom stub diagnostic"
        );
    }

    #[test]
    fn dynamic_backend_rejects_axiom_stubs_without_allow_axioms() {
        let env = Env::new();
        let ids = mir::types::IdRegistry::from_env(&env);
        let lowered_defs = Vec::new();
        let axiom_stubs = vec![AxiomStub {
            safe_name: "axiom_stub".to_string(),
            original_name: "axiom_stub".to_string(),
        }];

        let err = select_backend_code(
            BackendMode::Dynamic,
            false,
            &env,
            &ids,
            &lowered_defs,
            &axiom_stubs,
            &None,
        )
        .expect_err("dynamic backend should reject stubs unless --allow-axioms");

        assert!(
            err.contains("Dynamic backend encountered axiom stubs"),
            "expected dynamic backend axiom stub diagnostic, got: {}",
            err
        );
    }

    #[test]
    fn typed_backend_emits_axiom_stubs_with_allow_axioms() {
        let env = Env::new();
        let ids = mir::types::IdRegistry::from_env(&env);
        let lowered_defs = Vec::new();
        let axiom_stubs = vec![AxiomStub {
            safe_name: "axiom_stub".to_string(),
            original_name: "axiom_stub".to_string(),
        }];

        let backend = select_backend_code(
            BackendMode::Typed,
            true,
            &env,
            &ids,
            &lowered_defs,
            &axiom_stubs,
            &None,
        )
        .expect("typed backend should emit allow-axioms stubs");

        assert!(
            backend.code.contains("fn axiom_stub<T>() -> T"),
            "expected typed axiom panic stub in generated code"
        );
        let warning = backend
            .warning
            .expect("expected loud warning for executable axioms");
        assert!(
            warning.contains("WARNING: executable axioms enabled"),
            "expected executable-axiom warning"
        );
        assert_eq!(backend.selected_backend, SelectedBackend::Typed);
        assert_eq!(
            backend.executable_axiom_stubs,
            vec!["axiom_stub".to_string()]
        );
    }

    #[test]
    fn auto_backend_prefers_typed_with_allow_axioms() {
        let env = Env::new();
        let ids = mir::types::IdRegistry::from_env(&env);
        let lowered_defs = Vec::new();
        let axiom_stubs = vec![AxiomStub {
            safe_name: "axiom_stub".to_string(),
            original_name: "axiom_stub".to_string(),
        }];

        let backend = select_backend_code(
            BackendMode::Auto,
            true,
            &env,
            &ids,
            &lowered_defs,
            &axiom_stubs,
            &None,
        )
        .expect("auto backend should use typed stubs when --allow-axioms is enabled");

        assert_eq!(backend.selected_backend, SelectedBackend::Typed);
        assert!(
            !backend.code.contains("enum Value"),
            "auto+allow-axioms should not force dynamic fallback when typed is available"
        );
        assert!(
            backend.code.contains("fn axiom_stub<T>() -> T"),
            "expected typed axiom panic stub in generated code"
        );
    }

    #[test]
    fn auto_backend_fallback_includes_typed_reason_code() {
        let env = Env::new();
        let ids = mir::types::IdRegistry::from_env(&env);
        let axiom_stubs = Vec::new();

        let body = build_body(
            0,
            vec![
                local("_0", mir::types::MirType::Unit),
                local("_1", mir::types::MirType::Nat),
            ],
            Vec::new(),
            mir::Terminator::Call {
                func: mir::CallOperand::Borrow(
                    mir::BorrowKind::Shared,
                    mir::Place::from(mir::Local(1)),
                ),
                args: vec![nat_const(0)],
                destination: mir::Place::from(mir::Local(0)),
                target: None,
            },
        );

        let backend = select_backend_code(
            BackendMode::Auto,
            false,
            &env,
            &ids,
            &[LoweredDef {
                name: "entry".to_string(),
                body,
                derived_bodies: Vec::new(),
            }],
            &axiom_stubs,
            &Some("entry".to_string()),
        )
        .expect("auto backend should fall back to dynamic when typed is unsupported");

        assert!(
            backend.code.contains("enum Value"),
            "auto fallback should emit dynamic backend runtime"
        );
        let warning = backend
            .warning
            .expect("expected explicit auto-fallback warning");
        assert!(
            warning.contains("[TB003]"),
            "expected typed reason code in fallback warning, got: {}",
            warning
        );
    }

    #[test]
    fn auto_backend_fallback_covers_typed_reason_codes_matrix() {
        let tb002 = build_body(
            0,
            vec![
                local("_0", mir::types::MirType::Unit),
                local(
                    "_1",
                    mir::types::MirType::Fn(
                        FunctionKind::Fn,
                        Vec::new(),
                        vec![mir::types::MirType::Nat, mir::types::MirType::Nat],
                        Box::new(mir::types::MirType::Nat),
                    ),
                ),
            ],
            Vec::new(),
            mir::Terminator::Return,
        );

        let tb003 = build_body(
            0,
            vec![
                local("_0", mir::types::MirType::Unit),
                local("_1", mir::types::MirType::Nat),
            ],
            Vec::new(),
            mir::Terminator::Call {
                func: mir::CallOperand::Borrow(
                    mir::BorrowKind::Shared,
                    mir::Place::from(mir::Local(1)),
                ),
                args: vec![nat_const(0)],
                destination: mir::Place::from(mir::Local(0)),
                target: None,
            },
        );

        let tb004 = build_body(
            0,
            vec![
                local("_0", mir::types::MirType::Unit),
                local("_1", mir::types::MirType::Nat),
            ],
            vec![mir::Statement::Assign(
                mir::Place {
                    local: mir::Local(1),
                    projection: vec![mir::PlaceElem::Downcast(1), mir::PlaceElem::Field(0)],
                },
                mir::Rvalue::Use(nat_const(1)),
            )],
            mir::Terminator::Return,
        );

        let tb005 = build_body(
            0,
            vec![
                local("_0", mir::types::MirType::Unit),
                local("_1", mir::types::MirType::Nat),
            ],
            vec![mir::Statement::Assign(
                mir::Place::from(mir::Local(0)),
                mir::Rvalue::Use(mir::Operand::Copy(mir::Place {
                    local: mir::Local(1),
                    projection: vec![mir::PlaceElem::Field(0)],
                })),
            )],
            mir::Terminator::Return,
        );

        let tb006 = build_body(
            2,
            vec![
                local("_0", mir::types::MirType::Unit),
                local("_1", mir::types::MirType::Unit),
                local("_2", mir::types::MirType::Unit),
            ],
            vec![mir::Statement::Assign(
                mir::Place::from(mir::Local(0)),
                mir::Rvalue::Use(mir::Operand::Copy(mir::Place {
                    local: mir::Local(1),
                    projection: vec![mir::PlaceElem::Deref],
                })),
            )],
            mir::Terminator::Return,
        );

        let tb007 = build_body(
            0,
            vec![local("_0", mir::types::MirType::Unit)],
            vec![mir::Statement::Assign(
                mir::Place::from(mir::Local(0)),
                mir::Rvalue::Use(mir::Operand::Constant(Box::new(mir::Constant {
                    literal: mir::Literal::Closure(0, Vec::new()),
                    ty: mir::types::MirType::Unit,
                }))),
            )],
            mir::Terminator::Return,
        );

        let tb008 = build_body(
            0,
            vec![local("_0", mir::types::MirType::Unit)],
            vec![mir::Statement::Assign(
                mir::Place::from(mir::Local(0)),
                mir::Rvalue::Use(mir::Operand::Constant(Box::new(mir::Constant {
                    literal: mir::Literal::Fix(0, Vec::new()),
                    ty: mir::types::MirType::Unit,
                }))),
            )],
            mir::Terminator::Return,
        );

        let tb001_legacy = build_body(
            0,
            vec![
                local("_0", mir::types::MirType::Unit),
                local(
                    "_1",
                    mir::types::MirType::Fn(
                        FunctionKind::FnMut,
                        Vec::new(),
                        vec![mir::types::MirType::Nat],
                        Box::new(mir::types::MirType::Nat),
                    ),
                ),
            ],
            Vec::new(),
            mir::Terminator::Return,
        );

        let poly_fn_ty = mir::types::MirType::Fn(
            FunctionKind::Fn,
            Vec::new(),
            vec![mir::types::MirType::Param(0)],
            Box::new(mir::types::MirType::Param(0)),
        );
        let tb009 = build_body(
            0,
            vec![local("_0", poly_fn_ty.clone())],
            vec![mir::Statement::Assign(
                mir::Place::from(mir::Local(0)),
                mir::Rvalue::Use(mir::Operand::Constant(Box::new(mir::Constant {
                    literal: mir::Literal::Closure(0, Vec::new()),
                    ty: poly_fn_ty,
                }))),
            )],
            mir::Terminator::Return,
        );

        let cases = vec![
            ("TB002", tb002),
            ("TB003", tb003),
            ("TB004", tb004),
            ("TB005", tb005),
            ("TB006", tb006),
            ("TB007", tb007),
            ("TB008", tb008),
        ];

        for (expected_code, body) in cases {
            let warning = auto_fallback_warning_for_body(body);
            assert!(
                warning.contains(expected_code),
                "expected warning to include {} but got: {}",
                expected_code,
                warning
            );
        }

        let env = Env::new();
        let ids = mir::types::IdRegistry::from_env(&env);
        let backend = select_backend_code(
            BackendMode::Auto,
            false,
            &env,
            &ids,
            &[LoweredDef {
                name: "entry".to_string(),
                body: tb009,
                derived_bodies: Vec::new(),
            }],
            &Vec::new(),
            &Some("entry".to_string()),
        )
        .expect("auto backend should support previously-polymorphic function-value case");
        assert!(
            backend.warning.is_none(),
            "did not expect fallback warning for TB009 scenario, got: {:?}",
            backend.warning
        );
        assert!(
            !backend.code.contains("enum Value"),
            "expected typed backend output for TB009 scenario"
        );

        let backend = select_backend_code(
            BackendMode::Auto,
            false,
            &env,
            &ids,
            &[LoweredDef {
                name: "entry".to_string(),
                body: tb001_legacy,
                derived_bodies: Vec::new(),
            }],
            &Vec::new(),
            &Some("entry".to_string()),
        )
        .expect("auto backend should support former TB001 fnmut scenario");
        assert!(
            backend.warning.is_none(),
            "did not expect fallback warning for former TB001 scenario, got: {:?}",
            backend.warning
        );
        assert!(
            !backend.code.contains("enum Value"),
            "expected typed backend output for former TB001 scenario"
        );
    }

    #[test]
    fn compiler_diagnostic_fallback_handles_closed_writer() {
        struct ClosedWriter;

        impl Write for ClosedWriter {
            fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
                Err(io::Error::new(io::ErrorKind::BrokenPipe, "writer closed"))
            }

            fn flush(&mut self) -> io::Result<()> {
                Err(io::Error::new(io::ErrorKind::BrokenPipe, "writer closed"))
            }
        }

        let diag = Diagnostic::error("synthetic diagnostic".to_string());
        let render_error = io::Error::new(io::ErrorKind::BrokenPipe, "stdout closed");
        let mut writer = ClosedWriter;
        write_diagnostic_fallback(&mut writer, "compile_test", &diag, &render_error);
    }

    #[test]
    fn test_basic_compilation() {
        let source = r#"(
def double (pi n Nat Nat)
  (lam n Nat (add n n)))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        assert!(
            !results.is_empty(),
            "Should have compiled at least one definition"
        );
        let double_result = results.iter().find(|r| r.name == "double");
        assert!(double_result.is_some(), "Should have compiled 'double'");
    }

    #[test]
    fn test_linear_type_definition() {
        let source = r#"(
inductive Token (sort 1)
  (ctor mk_token Token))

(def use_token (pi t Token Nat)
  (lam t Token zero))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let use_token = results.iter().find(|r| r.name == "use_token");
        assert!(use_token.is_some(), "Should have compiled 'use_token'");
    }

    #[test]
    fn test_copy_type_reuse() {
        let source = r#"(
def use_nat_twice (pi n Nat Nat)
  (lam n Nat (add n n)))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "use_nat_twice");
        assert!(result.is_some(), "Should have compiled 'use_nat_twice'");
    }

    #[test]
    fn test_ownership_analysis_runs() {
        let source = r#"(
def identity (pi n Nat Nat)
  (lam n Nat n))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        assert_eq!(results.len(), 1, "Should have exactly one definition");
    }

    #[test]
    fn test_match_compilation() {
        let source = r#"(
def is_zero (pi n Nat Bool)
  (lam n Nat
    (match n Bool
      (case (zero) true)
      (case (succ m ih) false))))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "is_zero");
        assert!(result.is_some(), "Should have compiled 'is_zero'");
    }

    #[test]
    fn test_nested_function_compilation() {
        let source = r#"(
def const_nat (pi a Nat (pi b Nat Nat))
  (lam a Nat (lam b Nat a)))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "const_nat");
        assert!(result.is_some(), "Should have compiled 'const_nat'");
    }

    #[test]
    fn test_fnonce_coercion_compiles() {
        let source = r#"
(def apply_once
  (pi f (pi #[once] x Nat Nat) (pi #[once] v Nat Nat))
  (lam f (pi #[once] x Nat Nat)
    (lam v Nat (f v))))

(def add_one (pi #[fn] x Nat Nat)
  (lam x Nat (succ x)))

(def test_coercion Nat (apply_once add_one zero))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        assert!(
            results.iter().any(|r| r.name == "test_coercion"),
            "Should have compiled 'test_coercion'"
        );
    }

    #[test]
    fn test_append_fnonce_compiles() {
        let source = r#"
(inductive List2 (pi T (sort 1) (sort 1))
  (ctor nil (pi {T (sort 1)} (List2 T)))
  (ctor cons (pi {T (sort 1)} (pi h T (pi t (List2 T) (List2 T))))))

(def append (pi {T (sort 1)} (pi l1 (List2 T) (pi #[once] l2 (List2 T) (List2 T))))
  (lam {T} (sort 1)
    (lam l1 (List2 T)
      (lam #[once] l2 (List2 T) l2)
    )
  )
)

(def test_append (pi l1 (List2 Nat) (pi #[once] l2 (List2 Nat) (List2 Nat)))
  (lam l1 (List2 Nat)
    (lam #[once] l2 (List2 Nat)
      (append l1 l2))))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        if results.iter().any(|r| r.name == "test_append") {
            return;
        }

        let mut env = Env::new();
        let mut expander = Expander::new();
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        let mut prelude_diagnostics = DiagnosticCollector::new();
        let prelude_options = crate::driver::PipelineOptions {
            prelude_frozen: false,
            allow_redefine: false,
            ..Default::default()
        };
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        let _ = crate::driver::process_code(
            TEST_PRELUDE,
            "prelude",
            &mut env,
            &mut expander,
            &prelude_options,
            &mut prelude_diagnostics,
        );
        env.set_allow_reserved_primitives(allow_reserved);

        let mut diagnostics = DiagnosticCollector::new();
        let options = crate::driver::PipelineOptions {
            prelude_frozen: true,
            allow_redefine: false,
            ..Default::default()
        };
        let _ = crate::driver::process_code(
            source,
            "test_append",
            &mut env,
            &mut expander,
            &options,
            &mut diagnostics,
        );
        let messages: Vec<String> = diagnostics
            .diagnostics
            .iter()
            .map(|diag| format!("{}: {}", diag.level, diag.message_with_code()))
            .collect();
        panic!(
            "Should have compiled 'test_append'. Diagnostics:\n{}",
            messages.join("\n")
        );
    }

    #[test]
    fn test_linear_type_must_be_used() {
        let source = r#"(
inductive Resource (sort 1)
  (ctor acquire Resource))

(def create_resource Resource acquire)"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "create_resource");
        assert!(result.is_some(), "Should have compiled 'create_resource'");
    }

    #[test]
    fn test_multiple_definitions() {
        let source = r#"(
def f1 Nat zero)
(def f2 Nat (succ zero))
(def f3 Nat (succ (succ zero)))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        assert_eq!(results.len(), 3, "Should have compiled 3 definitions");
        assert!(results.iter().any(|r| r.name == "f1"));
        assert!(results.iter().any(|r| r.name == "f2"));
        assert!(results.iter().any(|r| r.name == "f3"));
    }

    #[test]
    fn test_eval_allowed_in_unsafe_def() {
        let source = r#"
(axiom Dyn (sort 1))
(axiom EvalCap (sort 1))
(axiom unsafe eval (pi code Dyn (pi cap EvalCap Dyn)))
(axiom dyn_code Dyn)
(axiom dyn_cap EvalCap)

(unsafe uses_eval Dyn (eval dyn_code dyn_cap))
"#;
        let mut env = Env::new();
        let mut expander = Expander::new();
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        let mut diagnostics = DiagnosticCollector::new();
        let options = crate::driver::PipelineOptions::default();

        let result = crate::driver::process_code(
            source,
            "eval_allowed",
            &mut env,
            &mut expander,
            &options,
            &mut diagnostics,
        );

        assert!(result.is_ok(), "Expected eval in unsafe def to parse");
        assert!(
            !diagnostics.has_errors(),
            "Expected eval in unsafe def to typecheck"
        );
    }

    #[test]
    fn test_eval_rejected_in_total_def() {
        let source = r#"
(axiom Dyn (sort 1))
(axiom EvalCap (sort 1))
(axiom unsafe eval (pi code Dyn (pi cap EvalCap Dyn)))
(axiom dyn_code Dyn)
(axiom dyn_cap EvalCap)

(def bad Dyn (eval dyn_code dyn_cap))
"#;
        let mut env = Env::new();
        let mut expander = Expander::new();
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        let mut diagnostics = DiagnosticCollector::new();
        let options = crate::driver::PipelineOptions::default();

        let result = crate::driver::process_code(
            source,
            "eval_rejected",
            &mut env,
            &mut expander,
            &options,
            &mut diagnostics,
        );

        assert!(result.is_ok(), "Expected pipeline to complete");
        assert!(
            diagnostics.has_errors(),
            "Expected eval in total def to be rejected"
        );
    }

    #[test]
    fn test_recursive_function() {
        let source = r#"(
def double (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m ih) (succ (succ ih))))))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "double");
        assert!(result.is_some(), "Should have compiled 'double'");
    }

    #[test]
    fn test_bool_operations() {
        let source = r#"(
def my_not (pi b Bool Bool)
  (lam b Bool
    (match b Bool
      (case (true) false)
      (case (false) true))))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "my_not");
        assert!(result.is_some(), "Should have compiled 'my_not'");
    }

    #[test]
    fn test_complex_nested_match() {
        let source = r#"(
def nat_eq (pi a Nat (pi b Nat Bool))
  (lam a Nat
    (lam b Nat
      (match a Bool
        (case (zero)
          (match b Bool
            (case (zero) true)
            (case (succ m ih) false)))
        (case (succ n ih)
          (match b Bool
            (case (zero) false)
            (case (succ m ih2) ih)))))))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "nat_eq");
        assert!(result.is_some(), "Should have compiled 'nat_eq'");
    }

    #[test]
    fn test_prelude_macro_boundary_is_error() {
        let prelude = r#"
(defmacro def_marker (name) (axiom unsafe name Type))
(defmacro mk_eval (code cap) (eval code cap))
(def_marker interior_mutable)
(axiom Dyn (sort 1))
(axiom EvalCap (sort 1))
(axiom unsafe eval (pi code Dyn (pi cap EvalCap Dyn)))
(axiom dyn_code Dyn)
(axiom dyn_cap EvalCap)
(mk_eval dyn_code dyn_cap)
"#;
        let mut env = Env::new();
        let mut expander = Expander::new();
        let mut diagnostics = DiagnosticCollector::new();
        let options = crate::driver::PipelineOptions::default();
        let prelude_module = crate::driver::module_id_for_source("prelude");

        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        crate::set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        let _ = crate::driver::process_code(
            prelude,
            "prelude",
            &mut env,
            &mut expander,
            &options,
            &mut diagnostics,
        );
        env.set_allow_reserved_primitives(allow_reserved);
        expander.clear_macro_boundary_allowlist();

        assert!(
            diagnostics.has_errors(),
            "Expected macro boundary violations in prelude to be errors"
        );
        assert!(
            diagnostics
                .diagnostics
                .iter()
                .any(|d| d.message.contains("macro boundary violations are errors")),
            "Expected macro boundary error diagnostic"
        );
        assert!(
            diagnostics
                .diagnostics
                .iter()
                .any(|d| d.message.contains("axiom unsafe")),
            "Expected macro boundary error mentioning axiom unsafe"
        );
    }
}
