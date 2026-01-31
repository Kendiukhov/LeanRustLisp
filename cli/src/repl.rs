use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use frontend::elaborator::{Elaborator, ElabError};
use frontend::declaration_parser::DeclarationParser;
use frontend::surface::Declaration;
use kernel::checker::{Env, whnf};
use std::rc::Rc;
use std::fs;
use std::path::Path;

pub fn start() {
    let mut rl = DefaultEditor::new().expect("Failed to init readline");
    if rl.load_history("history.txt").is_err() {
        // No history yet
    }

    let mut env = Env::new();
    let mut expander = Expander::new();
    
    let prelude_path = "stdlib/prelude.lrl";
    if Path::new(prelude_path).exists() {
        println!("Loading prelude from {}...", prelude_path);
        run_file(prelude_path, &mut env, &mut expander, false);
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
                            println!("  :expand <expr>  Expand macros in an expression");
                        },
                        ":load" => {
                            if parts.len() < 2 {
                                println!("Usage: :load <file>");
                            } else {
                                let path = parts[1];
                                run_file(path, &mut env, &mut expander, true);
                            }
                        },
                        ":type" => {
                            if parts.len() < 2 {
                                println!("Usage: :type <expr>");
                            } else {
                                let input_expr = line[parts[0].len()..].trim();
                                process_line(input_expr, &mut env, &mut expander, true, false);
                            }
                        },
                        ":eval" => {
                            if parts.len() < 2 {
                                println!("Usage: :eval <expr>");
                            } else {
                                let input_expr = line[parts[0].len()..].trim();
                                process_line(input_expr, &mut env, &mut expander, false, true);
                            }
                        },
                        ":expand" => {
                            if parts.len() < 2 {
                                println!("Usage: :expand <expr>");
                            } else {
                                let input_expr = line[parts[0].len()..].trim();
                                let mut parser = Parser::new(input_expr);
                                let syntax_nodes = match parser.parse() {
                                    Ok(nodes) => nodes,
                                    Err(e) => {
                                        println!("Parse Error: {:?}", e);
                                        continue;
                                    }
                                };
                                for syntax in syntax_nodes {
                                    if let Some(expanded_syntax) = expander.expand_all_macros(syntax).unwrap() {
                                        println!("{}", expanded_syntax.pretty_print());
                                    }
                                }
                            }
                        },
                        _ => println!("Unknown command. Type :help for help."),
                    }
                } else {
                    process_line(line, &mut env, &mut expander, true, false);
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

pub fn run_file(path: &str, env: &mut Env, expander: &mut Expander, verbose: bool) {
    match fs::read_to_string(path) {
        Ok(content) => {
            process_line(&content, env, expander, verbose, false);
        },
        Err(e) => println!("Error reading file {}: {:?}", path, e),
    }
}

fn process_line(input: &str, env: &mut Env, expander: &mut Expander, show_type: bool, do_eval: bool) {
    let mut parser = Parser::new(input);
    let syntax_nodes = match parser.parse() {
        Ok(nodes) => nodes,
        Err(e) => {
            println!("Parse Error: {:?}", e);
            return;
        }
    };

    let mut decl_parser = DeclarationParser::new(expander);
    let decls = match decl_parser.parse(syntax_nodes) {
        Ok(decls) => decls,
        Err(e) => {
            println!("Declaration Parse Error: {:?}", e);
            return;
        }
    };

    for decl in decls {
        match decl {
            Declaration::Def { name, ty, val, is_partial } => {
                let mut elab = Elaborator::new(env);
                let ty_core = match elab.infer(ty) {
                    Ok((t, s)) => {
                        if !matches!(*s, kernel::ast::Term::Sort(_)) {
                            println!("Type of a definition must be a Sort, but got {:?}", s);
                            continue;
                        }
                        t
                    },
                    Err(e) => { println!("Elaboration Error (Type): {:?}", e); continue; }
                };

                let val_core = match elab.check(val, &ty_core) {
                    Ok(t) => {
                         if let Err(e) = elab.solve_constraints() {
                             println!("Elaboration Error (Constraints): {:?}", e);
                             continue;
                         }
                         t
                    },
                    Err(e) => { println!("Elaboration Error (Value): {:?}", e); continue; }
                };
                
                let def = if is_partial {
                    kernel::ast::Definition::partial(name.clone(), ty_core, val_core)
                } else {
                    kernel::ast::Definition::total(name.clone(), ty_core, val_core)
                };
                match env.add_definition(def) {
                    Ok(_) => {
                        if show_type { println!("Defined {} ({})", name, if is_partial { "partial" } else { "total" }); }
                    }
                    Err(e) => {
                        println!("Definition Error in {}: {:?}", name, e);
                    }
                }
            }
            Declaration::Axiom { name, ty } => {
                let mut elab = Elaborator::new(env);
                let (ty_core, ty_ty) = match elab.infer(ty) {
                    Ok((t, s)) => (t, s),
                    Err(e) => { println!("Elaboration Error (Type): {:?}", e); continue; }
                };
                if !matches!(*ty_ty, kernel::ast::Term::Sort(_)) {
                    println!("Error: axiom type must be a type, got {:?}", ty_ty);
                    continue;
                }
                env.add_axiom(name.clone(), ty_core);
                if show_type { println!("Axiom {} declared", name); }
            }
            Declaration::Inductive { name, ty, ctors } => {
                // Elaborate the type
                let mut elab = Elaborator::new(env);
                let (ty_core, ty_ty) = match elab.infer(ty) {
                    Ok((t, s)) => (t, s),
                    Err(e) => { println!("Elaboration Error (Inductive Type): {:?}", e); continue; }
                };
                if !matches!(*ty_ty, kernel::ast::Term::Sort(_)) {
                    println!("Error: inductive type must be a type, got {:?}", ty_ty);
                    continue;
                }

                // Count parameters (pi binders in the type)
                let num_params = {
                    let mut n = 0;
                    let mut t = &ty_core;
                    while let kernel::ast::Term::Pi(_, b, _) = &**t {
                        n += 1;
                        t = b;
                    }
                    n
                };

                // Pre-register the inductive to allow self-references in constructors
                let placeholder = kernel::ast::InductiveDecl {
                    name: name.clone(),
                    univ_params: vec![],
                    num_params,
                    ty: ty_core.clone(),
                    ctors: vec![],
                    is_copy: false,
                };
                if let Err(e) = env.add_inductive(placeholder) {
                    println!("Error adding placeholder inductive: {:?}", e);
                    continue;
                }

                // Elaborate constructors
                let mut kernel_ctors = Vec::new();
                let mut failed = false;
                for (cname, cty) in ctors {
                    let mut elab_c = Elaborator::new(env);
                    let (cty_core, _) = match elab_c.infer(cty) {
                        Ok((t, s)) => (t, s),
                        Err(e) => {
                            println!("Elaboration Error (Constructor {}): {:?}", cname, e);
                            failed = true;
                            break;
                        }
                    };
                    kernel_ctors.push(kernel::ast::Constructor { name: cname, ty: cty_core });
                }
                if failed { continue; }

                // Create the full inductive declaration
                let decl = kernel::ast::InductiveDecl {
                    name: name.clone(),
                    univ_params: vec![],
                    num_params,
                    ty: ty_core,
                    ctors: kernel_ctors,
                    is_copy: false,
                };

                // Re-register with full constructors (replacing placeholder)
                env.inductives.insert(name.clone(), decl.clone());

                // Verify soundness
                if let Err(e) = kernel::checker::check_inductive_soundness(env, &decl) {
                    println!("Inductive soundness check failed for {}: {:?}", name, e);
                    env.inductives.remove(&name);
                    continue;
                }

                if show_type { println!("Defined inductive {}", name); }
            }
            Declaration::DefMacro { name, args, body } => {
                let macro_def = frontend::macro_expander::MacroDef { args, body };
                expander.macros.insert(name.clone(), macro_def);
                if show_type { println!("Defined macro {}", name); }
            }
            Declaration::Expr(term) => {
                let mut elab = Elaborator::new(env);
                let (core_term, ty) = match elab.infer(term) {
                    Ok((term, ty)) => (term, ty),
                    Err(e) => {
                        match e {
                            ElabError::OccursCheck(id, t) => {
                                println!("Occurs Check Failed: {} in {:?}", id, t);
                            }
                            ElabError::UnificationError(t1, t2) => {
                                println!("Unification Error: {:?} vs {:?}", t1, t2);
                            }
                            ElabError::SolutionContainsFreeVariables(t) => {
                                println!("Solution Contains Free Variables: {:?}", t);
                            }
                            _ => {
                                println!("Elaboration Error: {:?}", e);
                            }
                        }
                        continue;
                    }
                };

                if show_type {
                    let ty_norm = whnf(env, ty, kernel::Transparency::All);
                    println!(": {:?}", ty_norm);
                }
                
                if do_eval {
                    let val_norm = strong_normalize(env, core_term);
                    println!("= {}", pretty_print(env, &val_norm));
                }
            }
        }
    }
}

fn strong_normalize(env: &Env, term: Rc<kernel::ast::Term>) -> Rc<kernel::ast::Term> {
    use kernel::ast::Term;
    let whnf = kernel::checker::whnf(env, term, kernel::Transparency::All);
    match &*whnf {
        Term::App(f, a) => {
            Rc::new(Term::App(
                strong_normalize(env, f.clone()),
                strong_normalize(env, a.clone())
            ))
        }
        Term::Lam(ty, body, info) => {
            Rc::new(Term::Lam(
                strong_normalize(env, ty.clone()),
                strong_normalize(env, body.clone()),
                *info
            ))
        }
        Term::Pi(ty, body, info) => {
            Rc::new(Term::Pi(
                strong_normalize(env, ty.clone()),
                strong_normalize(env, body.clone()),
                *info
            ))
        }
        Term::LetE(_ty, v, b) => { 
             strong_normalize(env, b.subst(0, v)) 
        }
        _ => whnf,
    }
}

fn pretty_print(env: &Env, term: &kernel::ast::Term) -> String {
    use kernel::ast::Term;
    match term {
        Term::Var(i) => format!("#{}", i),
        Term::Sort(l) => format!("Sort({:?})", l),
        Term::Const(n, _) => n.clone(),
        Term::App(f, a) => {
            let mut args = vec![a];
            let mut curr = f;
            while let Term::App(sub_f, sub_a) = &**curr {
                args.push(sub_a);
                curr = sub_f;
            }
            args.reverse();
            
            let head = pretty_print(env, &**curr);
            let ar_str: Vec<String> = args.iter().map(|arg| pretty_print(env, &***arg)).collect();
            format!("({} {})", head, ar_str.join(" "))
        }
        Term::Lam(_, body, _) => format!("(lam {})", pretty_print(env, &**body)),
        Term::Pi(_, body, _) => format!("(pi {})", pretty_print(env, &**body)),
        Term::LetE(_, val, body) => format!("(let {} {})", pretty_print(env, &**val), pretty_print(env, &**body)),
        Term::Ind(n, _) => n.clone(),
        Term::Ctor(ind_name, idx, _) => {
            if let Some(decl) = env.get_inductive(ind_name) {
                if let Some(ctor) = decl.ctors.get(*idx) {
                    return ctor.name.clone();
                }
            }
            format!("{}.{}", ind_name, idx)
        }
        Term::Rec(n, _) => format!("Rec({})", n),
        Term::Meta(id) => format!("?{}", id),
    }
}