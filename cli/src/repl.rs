use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use frontend::macro_expander::Expander;
use frontend::diagnostics::DiagnosticCollector;
use kernel::checker::{Env, classical_axiom_dependencies};
use std::fs;
use std::path::Path;
use crate::driver::{self, PipelineOptions};

pub fn start() {
    let mut rl = DefaultEditor::new().expect("Failed to init readline");
    if rl.load_history("history.txt").is_err() {
        // No history yet
    }

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut last_defined: Option<String> = None;
    
    let prelude_path = "stdlib/prelude.lrl";
    if Path::new(prelude_path).exists() {
        println!("Loading prelude from {}...", prelude_path);
        let _ = run_file(prelude_path, &mut env, &mut expander, false);
    } else {
        println!("Warning: Prelude not found at {}", prelude_path);
    }

    println!("LeanRustLisp REPL v0.1.0");
    println!("Type 'exit' or Ctrl-D to quit.");

    loop {
        let readline = rl.readline("lrl> ");
        match readline {
            Ok(line) => {
                let line = line.trim();
                if line == "exit" { break; }
                if line.is_empty() { continue; }
                
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
                            println!("  :expand <expr>  Show the macro-expanded syntax");
                            println!("  :axioms <name...>  Show axiom dependencies (defaults to last defined)");
                        },
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
                                        println!("Classical: {:?}", classical);
                                    }
                                    None => println!("Unknown definition: {}", name),
                                }
                            }
                        },
                        ":load" => {
                            if parts.len() < 2 {
                                println!("Usage: :load <file>");
                            } else {
                                let path = parts[1];
                                if let Some(name) = run_file(path, &mut env, &mut expander, true) {
                                    last_defined = Some(name);
                                }
                            }
                        },
                        ":type" => {
                            if parts.len() < 2 {
                                println!("Usage: :type <expr>");
                            } else {
                                let input_expr = line[parts[0].len()..].trim();
                                let options = PipelineOptions { show_types: true, show_eval: false, verbose: false, collect_artifacts: false };
                                let mut diagnostics = DiagnosticCollector::new();
                                let result = driver::process_code(input_expr, "repl", &mut env, &mut expander, &options, &mut diagnostics);
                                update_last_defined(&result, &diagnostics, &env, &mut last_defined);
                                // Diagnostics are printed by driver? No, driver returns/collects them.
                                // Driver logic needs to print them or return them.
                                // My driver implementation collected them but processed valid ones.
                                // Let's check driver implementation.
                                // Ah, driver *handles* diagnostics but doesn't print them to stdout unless I make it do so?
                                // Actually, I passed DiagnosticCollector. I need to print them here.
                                print_diagnostics(&diagnostics, "repl", input_expr);
                            }
                        },
                        ":eval" => {
                            if parts.len() < 2 {
                                println!("Usage: :eval <expr>");
                            } else {
                                let input_expr = line[parts[0].len()..].trim();
                                let options = PipelineOptions { show_types: false, show_eval: true, verbose: false, collect_artifacts: false };
                                let mut diagnostics = DiagnosticCollector::new();
                                let result = driver::process_code(input_expr, "repl", &mut env, &mut expander, &options, &mut diagnostics);
                                update_last_defined(&result, &diagnostics, &env, &mut last_defined);
                                print_diagnostics(&diagnostics, "repl", input_expr);
                            }
                        },
                        ":expand" => {
                            if parts.len() < 2 {
                                println!("Usage: :expand <expr>");
                            } else {
                                let input_expr = line[parts[0].len()..].trim();
                                let mut parser = frontend::parser::Parser::new(input_expr);
                                match parser.parse() {
                                    Ok(exprs) => {
                                        for expr in exprs {
                                            match expander.expand_syntax(expr) {
                                                Ok(expanded) => {
                                                    println!("{}", expanded.pretty_print());
                                                },
                                                Err(e) => {
                                                    println!("Expansion Error: {:?}", e);
                                                    if !expander.expansion_trace.is_empty() {
                                                        println!("Macro Trace:");
                                                        for (name, span) in &expander.expansion_trace {
                                                            println!("  In macro '{}' at {:?}", name, span);
                                                        }
                                                        // Clear trace for next command
                                                        expander.expansion_trace.clear();
                                                    }
                                                }
                                            }
                                        }
                                    },
                                    Err(e) => println!("Parse Error: {:?}", e),
                                }
                            }
                        },
                        _ => println!("Unknown command. Type :help for help."),
                    }
                } else {
                     let options = PipelineOptions { show_types: true, show_eval: false, verbose: true, collect_artifacts: false };
                     let mut diagnostics = DiagnosticCollector::new();
                     let result = driver::process_code(line, "repl", &mut env, &mut expander, &options, &mut diagnostics);
                     update_last_defined(&result, &diagnostics, &env, &mut last_defined);
                     print_diagnostics(&diagnostics, "repl", line);
                }
            },
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break
            },
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break
            },
            Err(err) => {
                println!("Error: {:?}", err);
                break
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}

pub fn run_file(path: &str, env: &mut Env, expander: &mut Expander, verbose: bool) -> Option<String> {
    match fs::read_to_string(path) {
        Ok(content) => {
             // For file execution, show_eval=true to see output of top-level expressions
             let options = PipelineOptions { show_types: verbose, show_eval: true, verbose, collect_artifacts: false };
             let mut diagnostics = DiagnosticCollector::new();
             let result = driver::process_code(&content, path, env, expander, &options, &mut diagnostics);
             print_diagnostics(&diagnostics, path, &content);
             return extract_last_defined(&result, &diagnostics, env);
        },
        Err(e) => println!("Error reading file {}: {:?}", path, e),
    }
    None
}

fn print_diagnostics(diagnostics: &DiagnosticCollector, filename: &str, content: &str) {
    use ariadne::{Report, ReportKind, Label, Source, Color};
    use frontend::diagnostics::Level;

    for diag in &diagnostics.diagnostics {
        let kind = match diag.level {
            Level::Error => ReportKind::Error,
            Level::Warning => ReportKind::Warning,
            Level::Info => ReportKind::Advice,
        };
        
        let mut builder = Report::build(kind, filename, diag.span.map(|s| s.start).unwrap_or(0))
            .with_message(&diag.message);
            
        if let Some(span) = diag.span {
             let color = match diag.level {
                Level::Error => Color::Red,
                Level::Warning => Color::Yellow,
                Level::Info => Color::Blue,
            };
            builder = builder.with_label(Label::new((filename, span.start..span.end))
                .with_message(&diag.message)
                .with_color(color));
        }
        
        builder.finish().print((filename, Source::from(content))).unwrap();
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
