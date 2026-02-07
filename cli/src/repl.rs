use crate::compiler;
use crate::driver::{self, PipelineOptions};
use crate::expand::{expand_and_format, ExpandError, ExpandMode};
use frontend::diagnostics::{Diagnostic, DiagnosticCollector};
use frontend::macro_expander::Expander;
use kernel::checker::{classical_axiom_dependencies, Env};
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use std::fs;
use std::io::{self, BufRead, Write};
use std::path::Path;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum ReplLineAction {
    Continue,
    Exit,
}

#[derive(Clone, Copy)]
struct ReplOptions {
    require_axiom_tags: bool,
    allow_axioms: bool,
    allow_redefine: bool,
}

#[derive(Clone, Copy)]
pub struct RunFileOptions {
    pub verbose: bool,
    pub panic_free: bool,
    pub require_axiom_tags: bool,
    pub allow_axioms: bool,
    pub prelude_frozen: bool,
    pub allow_redefine: bool,
}

pub fn start(
    trace_macros: bool,
    panic_free: bool,
    macro_boundary_warn: bool,
    require_axiom_tags: bool,
    allow_redefine: bool,
    allow_axioms: bool,
) {
    let repl_options = ReplOptions {
        require_axiom_tags,
        allow_axioms,
        allow_redefine,
    };

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.trace_verbose = trace_macros;
    let user_policy = if macro_boundary_warn {
        frontend::macro_expander::MacroBoundaryPolicy::Warn
    } else {
        frontend::macro_expander::MacroBoundaryPolicy::Deny
    };
    expander.set_macro_boundary_policy(user_policy);
    let mut last_defined: Option<String> = None;

    let mut panic_free = panic_free;
    let mut prelude_modules = Vec::new();
    let mut loaded_any_prelude = false;
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    for prelude_path in compiler::prelude_stack_for_backend(compiler::BackendMode::Dynamic) {
        if !Path::new(prelude_path).exists() {
            continue;
        }
        loaded_any_prelude = true;
        println!("Loading prelude layer from {}...", prelude_path);
        let prelude_module = driver::module_id_for_source(prelude_path);
        expander.set_macro_boundary_policy(frontend::macro_expander::MacroBoundaryPolicy::Deny);
        crate::set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
        let _ = run_file(
            prelude_path,
            &mut env,
            &mut expander,
            RunFileOptions {
                verbose: false,
                panic_free,
                require_axiom_tags: false,
                allow_axioms: true,
                prelude_frozen: false,
                allow_redefine: false,
            },
        );
        expander.clear_macro_boundary_allowlist();
        prelude_modules.push(prelude_module);
    }
    env.set_allow_reserved_primitives(allow_reserved);
    expander.set_macro_boundary_policy(user_policy);
    if loaded_any_prelude {
        if let Err(err) = env.init_marker_registry() {
            println!("Failed to initialize marker registry: {}", err);
            return;
        }
        expander.set_default_imports(prelude_modules);
        expander.enter_module("repl");
    } else {
        println!(
            "Warning: prelude stack not found ({}, {})",
            compiler::PRELUDE_API_PATH,
            compiler::PRELUDE_IMPL_DYNAMIC_PATH
        );
    }

    env.set_allow_redefinition(allow_redefine);

    println!("LeanRustLisp REPL v0.1.0");
    println!("Type 'exit' or Ctrl-D to quit.");

    match DefaultEditor::new() {
        Ok(mut rl) => {
            if let Err(err) = rl.load_history("history.txt") {
                write_repl_warning(&format!(
                    "failed to load REPL history (continuing without history): {}",
                    err
                ));
            }

            let fallback_to_stdin = run_readline_loop(
                &mut rl,
                &mut env,
                &mut expander,
                &mut panic_free,
                repl_options,
                &mut last_defined,
            );

            if let Err(err) = rl.save_history("history.txt") {
                write_repl_warning(&format!(
                    "failed to save REPL history (continuing): {}",
                    err
                ));
            }

            if fallback_to_stdin {
                run_stdin_loop(
                    &mut env,
                    &mut expander,
                    &mut panic_free,
                    repl_options,
                    &mut last_defined,
                );
            }
        }
        Err(err) => {
            write_repl_warning(&format!(
                "failed to initialize line editor ({}); running in degraded mode without editing/history",
                err
            ));
            run_stdin_loop(
                &mut env,
                &mut expander,
                &mut panic_free,
                repl_options,
                &mut last_defined,
            );
        }
    }
}

fn run_readline_loop(
    rl: &mut DefaultEditor,
    env: &mut Env,
    expander: &mut Expander,
    panic_free: &mut bool,
    options: ReplOptions,
    last_defined: &mut Option<String>,
) -> bool {
    loop {
        match rl.readline("lrl> ") {
            Ok(line) => {
                let line = line.trim();
                if line.is_empty() {
                    continue;
                }
                if line == "exit" {
                    return false;
                }

                if let Err(err) = rl.add_history_entry(line) {
                    write_repl_warning(&format!(
                        "failed to append REPL history entry (continuing): {}",
                        err
                    ));
                }

                if matches!(
                    handle_repl_line(line, env, expander, panic_free, options, last_defined,),
                    ReplLineAction::Exit
                ) {
                    return false;
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                return false;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                return false;
            }
            Err(err) => {
                write_repl_warning(&format!(
                    "readline failed ({}); continuing in degraded stdin mode",
                    err
                ));
                return true;
            }
        }
    }
}

fn run_stdin_loop(
    env: &mut Env,
    expander: &mut Expander,
    panic_free: &mut bool,
    options: ReplOptions,
    last_defined: &mut Option<String>,
) {
    let stdin = io::stdin();
    let mut stdin_lock = stdin.lock();
    let mut input = String::new();
    loop {
        {
            let mut stdout = io::stdout().lock();
            let _ = write!(stdout, "lrl> ");
            let _ = stdout.flush();
        }

        input.clear();
        match stdin_lock.read_line(&mut input) {
            Ok(0) => {
                println!("CTRL-D");
                break;
            }
            Ok(_) => {
                let line = input.trim_end_matches(&['\r', '\n'][..]);
                if matches!(
                    handle_repl_line(line, env, expander, panic_free, options, last_defined,),
                    ReplLineAction::Exit
                ) {
                    break;
                }
            }
            Err(err) => {
                write_repl_warning(&format!(
                    "failed to read stdin in degraded mode; exiting REPL: {}",
                    err
                ));
                break;
            }
        }
    }
}

fn handle_repl_line(
    line: &str,
    env: &mut Env,
    expander: &mut Expander,
    panic_free: &mut bool,
    options: ReplOptions,
    last_defined: &mut Option<String>,
) -> ReplLineAction {
    let line = line.trim();
    if line == "exit" {
        return ReplLineAction::Exit;
    }
    if line.is_empty() {
        return ReplLineAction::Continue;
    }

    if line.starts_with(':') {
        let parts: Vec<&str> = line.split_whitespace().collect();
        match parts[0] {
            ":quit" | ":exit" => return ReplLineAction::Exit,
            ":help" => {
                println!("Available commands:");
                println!("  :quit, :exit    Exit the REPL");
                println!("  :help           Show this help message");
                println!("  :load <file>    Load a file");
                println!("  :type <expr>    Check the type of an expression");
                println!("  :eval <expr>    Evaluate an expression to WHNF");
                println!("  :expand <expr>       Show the macro-expanded syntax (alias for :expand-full)");
                println!("  :expand-1 <expr>     Show one step of macro expansion");
                println!("  :expand-full <expr>  Show the fully expanded syntax");
                println!("  :trace-expand <expr> Show expanded syntax with macro trace");
                println!("  :trace-macros [on|off]  Toggle macro trace during processing");
                println!(
                    "  :panic-free [on|off]    Toggle panic-free profile (interior mutability forbidden)"
                );
                println!("  :axioms <name...>  Show axiom dependencies (defaults to last defined)");
            }
            ":trace-macros" => {
                let setting = parts.get(1).map(|s| s.to_ascii_lowercase());
                match setting.as_deref() {
                    Some("on") => {
                        expander.trace_verbose = true;
                        println!("Macro tracing enabled.");
                    }
                    Some("off") => {
                        expander.trace_verbose = false;
                        println!("Macro tracing disabled.");
                    }
                    None => {
                        println!(
                            "Macro tracing is {}.",
                            if expander.trace_verbose { "on" } else { "off" }
                        );
                    }
                    _ => {
                        println!("Usage: :trace-macros [on|off]");
                    }
                }
            }
            ":axioms" => {
                let names: Vec<String> = if parts.len() >= 2 {
                    parts[1..].iter().map(|s| s.to_string()).collect()
                } else if let Some(name) = last_defined.clone() {
                    vec![name]
                } else {
                    println!("Usage: :axioms <name...>");
                    return ReplLineAction::Continue;
                };

                for (idx, name) in names.iter().enumerate() {
                    if idx > 0 {
                        println!();
                    }
                    match env.get_definition(name) {
                        Some(def) => {
                            let classical = classical_axiom_dependencies(&*env, def);
                            println!("{}:", name);
                            println!("Axioms: {:?}", def.axioms);
                            println!("Primitives: {:?}", def.primitive_deps);
                            println!("Classical: {:?}", classical);
                        }
                        None => println!("Unknown definition: {}", name),
                    }
                }
            }
            ":load" => {
                if parts.len() < 2 {
                    println!("Usage: :load <file>");
                } else {
                    let path = parts[1];
                    if let Some(name) = run_file(
                        path,
                        env,
                        expander,
                        RunFileOptions {
                            verbose: true,
                            panic_free: *panic_free,
                            require_axiom_tags: options.require_axiom_tags,
                            allow_axioms: options.allow_axioms,
                            prelude_frozen: true,
                            allow_redefine: options.allow_redefine,
                        },
                    ) {
                        *last_defined = Some(name);
                    }
                    expander.enter_module("repl");
                }
            }
            ":panic-free" => {
                let setting = parts.get(1).map(|s| s.to_ascii_lowercase());
                match setting.as_deref() {
                    Some("on") => {
                        *panic_free = true;
                        println!("Panic-free profile enabled.");
                    }
                    Some("off") => {
                        *panic_free = false;
                        println!("Panic-free profile disabled.");
                    }
                    None => {
                        println!(
                            "Panic-free profile is {}.",
                            if *panic_free { "on" } else { "off" }
                        );
                    }
                    _ => println!("Usage: :panic-free [on|off]"),
                }
            }
            ":type" => {
                if parts.len() < 2 {
                    println!("Usage: :type <expr>");
                } else {
                    let input_expr = line[parts[0].len()..].trim();
                    let options = PipelineOptions {
                        show_types: true,
                        show_eval: false,
                        verbose: false,
                        collect_artifacts: false,
                        panic_free: *panic_free,
                        require_axiom_tags: options.require_axiom_tags,
                        allow_axioms: options.allow_axioms,
                        prelude_frozen: true,
                        allow_redefine: options.allow_redefine,
                    };
                    let mut diagnostics = DiagnosticCollector::new();
                    let result = driver::process_code(
                        input_expr,
                        "repl",
                        env,
                        expander,
                        &options,
                        &mut diagnostics,
                    );
                    update_last_defined(&result, &diagnostics, env, last_defined);
                    print_diagnostics(&diagnostics, "repl", input_expr);
                }
            }
            ":eval" => {
                if parts.len() < 2 {
                    println!("Usage: :eval <expr>");
                } else {
                    let input_expr = line[parts[0].len()..].trim();
                    let options = PipelineOptions {
                        show_types: false,
                        show_eval: true,
                        verbose: false,
                        collect_artifacts: false,
                        panic_free: *panic_free,
                        require_axiom_tags: options.require_axiom_tags,
                        allow_axioms: options.allow_axioms,
                        prelude_frozen: true,
                        allow_redefine: options.allow_redefine,
                    };
                    let mut diagnostics = DiagnosticCollector::new();
                    let result = driver::process_code(
                        input_expr,
                        "repl",
                        env,
                        expander,
                        &options,
                        &mut diagnostics,
                    );
                    update_last_defined(&result, &diagnostics, env, last_defined);
                    print_diagnostics(&diagnostics, "repl", input_expr);
                }
            }
            ":expand" => {
                handle_expand_command(line, parts[0], ExpandMode::Full, expander);
            }
            ":expand-1" => {
                handle_expand_command(line, parts[0], ExpandMode::SingleStep, expander);
            }
            ":expand-full" => {
                handle_expand_command(line, parts[0], ExpandMode::Full, expander);
            }
            ":trace-expand" => {
                handle_expand_command(line, parts[0], ExpandMode::Trace, expander);
            }
            _ => println!("Unknown command. Type :help for help."),
        }
    } else {
        let options = PipelineOptions {
            show_types: true,
            show_eval: false,
            verbose: true,
            collect_artifacts: false,
            panic_free: *panic_free,
            require_axiom_tags: options.require_axiom_tags,
            allow_axioms: options.allow_axioms,
            prelude_frozen: true,
            allow_redefine: options.allow_redefine,
        };
        let mut diagnostics = DiagnosticCollector::new();
        let result = driver::process_code(line, "repl", env, expander, &options, &mut diagnostics);
        update_last_defined(&result, &diagnostics, env, last_defined);
        print_diagnostics(&diagnostics, "repl", line);
    }

    ReplLineAction::Continue
}

pub fn run_file(
    path: &str,
    env: &mut Env,
    expander: &mut Expander,
    options: RunFileOptions,
) -> Option<String> {
    match fs::read_to_string(path) {
        Ok(content) => {
            // For file execution, show_eval=true to see output of top-level expressions
            let options = PipelineOptions {
                show_types: options.verbose,
                show_eval: true,
                verbose: options.verbose,
                collect_artifacts: false,
                panic_free: options.panic_free,
                require_axiom_tags: options.require_axiom_tags,
                allow_axioms: options.allow_axioms,
                prelude_frozen: options.prelude_frozen,
                allow_redefine: options.allow_redefine,
            };
            let mut diagnostics = DiagnosticCollector::new();
            let result =
                driver::process_code(&content, path, env, expander, &options, &mut diagnostics);
            print_diagnostics(&diagnostics, path, &content);
            return extract_last_defined(&result, &diagnostics, env);
        }
        Err(e) => println!("Error reading file {}: {:?}", path, e),
    }
    None
}

fn handle_expand_command(line: &str, command: &str, mode: ExpandMode, expander: &mut Expander) {
    let input_expr = line[command.len()..].trim();
    if input_expr.is_empty() {
        println!("Usage: {} <expr>", command);
        return;
    }

    expander.enter_module("repl");

    match expand_and_format(input_expr, expander, mode) {
        Ok(output) => println!("{}", output),
        Err(err) => {
            println!("{}", err);
            if matches!(err, ExpandError::Expansion(_)) {
                print_macro_trace(expander);
            }
        }
    }
}

fn print_macro_trace(expander: &mut Expander) {
    if expander.expansion_trace.is_empty() {
        return;
    }
    println!("Macro Trace:");
    for (depth, (name, span)) in expander.expansion_trace.iter().enumerate() {
        let indent = "  ".repeat(depth);
        println!(
            "{}- {} @ {}:{} [{}..{}]",
            indent, name, span.line, span.col, span.start, span.end
        );
    }
    expander.expansion_trace.clear();
}

fn write_repl_warning(message: &str) {
    let mut stderr = io::stderr().lock();
    let _ = writeln!(stderr, "Warning: {}", message);
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

fn print_diagnostics(diagnostics: &DiagnosticCollector, filename: &str, content: &str) {
    use ariadne::{Color, Label, Report, ReportKind, Source};
    use frontend::diagnostics::Level;

    for diag in &diagnostics.diagnostics {
        let kind = match diag.level {
            Level::Error => ReportKind::Error,
            Level::Warning => ReportKind::Warning,
            Level::Info => ReportKind::Advice,
        };

        let mut builder = Report::build(kind, filename, diag.span.map(|s| s.start).unwrap_or(0))
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
}

fn update_last_defined(
    result: &Result<driver::ProcessingResult, driver::DriverError>,
    diagnostics: &DiagnosticCollector,
    env: &Env,
    last_defined: &mut Option<String>,
) {
    if diagnostics.has_errors() {
        return;
    }
    if let Some(name) = extract_last_defined(result, diagnostics, env) {
        *last_defined = Some(name);
    }
}

fn extract_last_defined(
    result: &Result<driver::ProcessingResult, driver::DriverError>,
    diagnostics: &DiagnosticCollector,
    env: &Env,
) -> Option<String> {
    if diagnostics.has_errors() {
        return None;
    }
    if let Ok(processed) = result {
        let mut last = None;
        for name in &processed.deployed_definitions {
            if env.get_definition(name).is_some() {
                last = Some(name.clone());
            }
        }
        return last;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::PipelineOptions;
    use frontend::diagnostics::DiagnosticCollector;
    use frontend::macro_expander::Expander;
    use std::io::{self, Write};

    fn run_repl_snippet(
        source: &str,
    ) -> (
        Result<driver::ProcessingResult, driver::DriverError>,
        DiagnosticCollector,
        Env,
    ) {
        let mut env = Env::new();
        env.set_allow_reserved_primitives(true);
        let mut expander = Expander::new();
        let mut diagnostics = DiagnosticCollector::new();
        let options = PipelineOptions::default();
        let result = driver::process_code(
            source,
            "repl_test",
            &mut env,
            &mut expander,
            &options,
            &mut diagnostics,
        );
        (result, diagnostics, env)
    }

    #[test]
    fn repl_last_defined_prefers_defs_over_inductives() {
        let source = r#"
            (inductive Nat Type
              (zero Nat)
              (succ (pi n Nat Nat)))

            (def one Nat (succ zero))
        "#;
        let (result, diagnostics, env) = run_repl_snippet(source);
        let last = extract_last_defined(&result, &diagnostics, &env);
        assert_eq!(last.as_deref(), Some("one"));
    }

    #[test]
    fn repl_last_defined_none_on_error() {
        let source = r#"
            (inductive Nat Type
              (zero Nat)
              (succ (pi n Nat Nat)))

            (def bad Nat (lam x Nat x))
        "#;
        let (result, diagnostics, env) = run_repl_snippet(source);
        assert!(
            diagnostics.has_errors(),
            "Expected diagnostics for ill-typed definition"
        );
        let last = extract_last_defined(&result, &diagnostics, &env);
        assert!(last.is_none());
    }

    #[test]
    fn repl_last_defined_on_axiom() {
        let source = r#"(axiom classical_choice (sort 0))"#;
        let (result, diagnostics, env) = run_repl_snippet(source);
        let last = extract_last_defined(&result, &diagnostics, &env);
        assert_eq!(last.as_deref(), Some("classical_choice"));
    }

    #[test]
    fn repl_diagnostic_fallback_handles_closed_writer() {
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
        write_diagnostic_fallback(&mut writer, "repl", &diag, &render_error);
    }
}
