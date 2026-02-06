use crate::driver::{self, PipelineOptions};
use crate::expand::{expand_and_format, ExpandError, ExpandMode};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::Expander;
use kernel::checker::{classical_axiom_dependencies, Env};
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use std::fs;
use std::path::Path;

pub fn start(
    trace_macros: bool,
    panic_free: bool,
    macro_boundary_warn: bool,
    require_axiom_tags: bool,
    allow_redefine: bool,
    allow_axioms: bool,
) {
    let mut rl = DefaultEditor::new().expect("Failed to init readline");
    if rl.load_history("history.txt").is_err() {
        // No history yet
    }

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
    let allow_axioms = allow_axioms;
    let prelude_path = "stdlib/prelude.lrl";
    if Path::new(prelude_path).exists() {
        println!("Loading prelude from {}...", prelude_path);
        let prelude_module = driver::module_id_for_source(prelude_path);
        expander.set_macro_boundary_policy(frontend::macro_expander::MacroBoundaryPolicy::Deny);
        crate::set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        let _ = run_file(
            prelude_path,
            &mut env,
            &mut expander,
            false,
            panic_free,
            false,
            true,
            false,
            false,
        );
        env.set_allow_reserved_primitives(allow_reserved);
        expander.clear_macro_boundary_allowlist();
        expander.set_macro_boundary_policy(user_policy);
        if let Err(err) = env.init_marker_registry() {
            println!("Failed to initialize marker registry: {}", err);
            return;
        }
        expander.set_default_imports(vec![prelude_module]);
        expander.enter_module("repl");
    } else {
        println!("Warning: Prelude not found at {}", prelude_path);
    }

    env.set_allow_redefinition(allow_redefine);

    println!("LeanRustLisp REPL v0.1.0");
    println!("Type 'exit' or Ctrl-D to quit.");

    loop {
        let readline = rl.readline("lrl> ");
        match readline {
            Ok(line) => {
                let line = line.trim();
                if line == "exit" {
                    break;
                }
                if line.is_empty() {
                    continue;
                }

                rl.add_history_entry(line).unwrap();

                if line.starts_with(':') {
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    match parts[0] {
                        ":quit" | ":exit" => break,
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
                            println!(
                                "  :trace-expand <expr> Show expanded syntax with macro trace"
                            );
                            println!(
                                "  :trace-macros [on|off]  Toggle macro trace during processing"
                            );
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
                                continue;
                            };

                            for (idx, name) in names.iter().enumerate() {
                                if idx > 0 {
                                    println!();
                                }
                                match env.get_definition(name) {
                                    Some(def) => {
                                        let classical = classical_axiom_dependencies(&env, def);
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
                                    &mut env,
                                    &mut expander,
                                    true,
                                    panic_free,
                                    require_axiom_tags,
                                    allow_axioms,
                                    true,
                                    allow_redefine,
                                ) {
                                    last_defined = Some(name);
                                }
                                expander.enter_module("repl");
                            }
                        }
                        ":panic-free" => {
                            let setting = parts.get(1).map(|s| s.to_ascii_lowercase());
                            match setting.as_deref() {
                                Some("on") => {
                                    panic_free = true;
                                    println!("Panic-free profile enabled.");
                                }
                                Some("off") => {
                                    panic_free = false;
                                    println!("Panic-free profile disabled.");
                                }
                                None => {
                                    println!(
                                        "Panic-free profile is {}.",
                                        if panic_free { "on" } else { "off" }
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
                                    panic_free,
                                    require_axiom_tags,
                                    allow_axioms,
                                    prelude_frozen: true,
                                    allow_redefine,
                                };
                                let mut diagnostics = DiagnosticCollector::new();
                                let result = driver::process_code(
                                    input_expr,
                                    "repl",
                                    &mut env,
                                    &mut expander,
                                    &options,
                                    &mut diagnostics,
                                );
                                update_last_defined(&result, &diagnostics, &env, &mut last_defined);
                                // Diagnostics are printed by driver? No, driver returns/collects them.
                                // Driver logic needs to print them or return them.
                                // My driver implementation collected them but processed valid ones.
                                // Let's check driver implementation.
                                // Ah, driver *handles* diagnostics but doesn't print them to stdout unless I make it do so?
                                // Actually, I passed DiagnosticCollector. I need to print them here.
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
                                    panic_free,
                                    require_axiom_tags,
                                    allow_axioms,
                                    prelude_frozen: true,
                                    allow_redefine,
                                };
                                let mut diagnostics = DiagnosticCollector::new();
                                let result = driver::process_code(
                                    input_expr,
                                    "repl",
                                    &mut env,
                                    &mut expander,
                                    &options,
                                    &mut diagnostics,
                                );
                                update_last_defined(&result, &diagnostics, &env, &mut last_defined);
                                print_diagnostics(&diagnostics, "repl", input_expr);
                            }
                        }
                        ":expand" => {
                            handle_expand_command(line, parts[0], ExpandMode::Full, &mut expander);
                        }
                        ":expand-1" => {
                            handle_expand_command(
                                line,
                                parts[0],
                                ExpandMode::SingleStep,
                                &mut expander,
                            );
                        }
                        ":expand-full" => {
                            handle_expand_command(line, parts[0], ExpandMode::Full, &mut expander);
                        }
                        ":trace-expand" => {
                            handle_expand_command(line, parts[0], ExpandMode::Trace, &mut expander);
                        }
                        _ => println!("Unknown command. Type :help for help."),
                    }
                } else {
                    let options = PipelineOptions {
                        show_types: true,
                        show_eval: false,
                        verbose: true,
                        collect_artifacts: false,
                        panic_free,
                        require_axiom_tags,
                        allow_axioms,
                        prelude_frozen: true,
                        allow_redefine,
                    };
                    let mut diagnostics = DiagnosticCollector::new();
                    let result = driver::process_code(
                        line,
                        "repl",
                        &mut env,
                        &mut expander,
                        &options,
                        &mut diagnostics,
                    );
                    update_last_defined(&result, &diagnostics, &env, &mut last_defined);
                    print_diagnostics(&diagnostics, "repl", line);
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}

pub fn run_file(
    path: &str,
    env: &mut Env,
    expander: &mut Expander,
    verbose: bool,
    panic_free: bool,
    require_axiom_tags: bool,
    allow_axioms: bool,
    prelude_frozen: bool,
    allow_redefine: bool,
) -> Option<String> {
    match fs::read_to_string(path) {
        Ok(content) => {
            // For file execution, show_eval=true to see output of top-level expressions
            let options = PipelineOptions {
                show_types: verbose,
                show_eval: true,
                verbose,
                collect_artifacts: false,
                panic_free,
                require_axiom_tags,
                allow_axioms,
                prelude_frozen,
                allow_redefine,
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

        builder
            .finish()
            .print((filename, Source::from(content)))
            .unwrap();
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
}
