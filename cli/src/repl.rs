use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use frontend::elaborator::Elaborator;
use frontend::surface::SyntaxKind;
use kernel::checker::{Env, Context, infer, whnf, check};
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
    
    // Load local prelude if available
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
                        _ => println!("Unknown command. Type :help for help."),
                    }
                } else {
                    // Default behavior: Check type
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
    // 1. Parse
    let mut parser = Parser::new(input);
    let syntax_nodes = match parser.parse() {
        Ok(nodes) => nodes,
        Err(e) => {
            println!("Parse Error: {:?}", e);
            return;
        }
    };

    for syntax in syntax_nodes {
        // Special Form: (def name type value) or (inductive ...)
        if let SyntaxKind::List(ref items) = syntax.kind {
            if items.len() >= 3 {
                if let SyntaxKind::Symbol(ref s) = items[0].kind {
                    if s == "def" {
                         if items.len() != 4 { println!("Error: def expects 3 args"); continue; }
                        let name_node = &items[1];
                        let type_node = &items[2];
                        let val_node = &items[3];

                        let name = if let SyntaxKind::Symbol(ref n) = name_node.kind {
                            n.clone()
                        } else {
                            println!("Error: def name must be a symbol");
                            continue;
                        };

                        // Process Type
                        let ty_expanded = match expander.expand(type_node.clone()) {
                            Ok(t) => t,
                            Err(e) => { println!("Expansion Error (Type): {:?}", e); continue; }
                        };
                        let mut elab = Elaborator::new(env);
                        let ty_core = match elab.elaborate(ty_expanded) {
                            Ok(t) => t,
                            Err(e) => { println!("Elaboration Error (Type): {:?}", e); continue; }
                        };

                        // Process Value
                        let val_expanded = match expander.expand(val_node.clone()) {
                            Ok(t) => t,
                            Err(e) => { println!("Expansion Error (Value): {:?}", e); continue; }
                        };
                        let mut elab2 = Elaborator::new(env);
                        let val_core = match elab2.elaborate(val_expanded) {
                            Ok(t) => t,
                            Err(e) => { println!("Elaboration Error (Value): {:?}", e); continue; }
                        };

                        // Check Type
                        let ctx = Context::new();
                        match check(env, &ctx, val_core.clone(), ty_core.clone()) {
                            Ok(_) => {
                                env.add_def(name.clone(), ty_core, val_core);
                                if show_type { println!("Defined {}", name); }
                            },
                            Err(e) => {
                                println!("Type Error in def {}: {:?}", name, e);
                            }
                        }
                        continue;
                    } else if s == "inductive" {
                        // (inductive Name Type (ctor Name Type) ...)
                        if items.len() < 3 { println!("Error: inductive missing args"); continue; }
                        
                        let name = if let SyntaxKind::Symbol(n) = &items[1].kind { n.clone() } else { println!("Error: inductive name symbol"); continue; };
                        
                        // Type
                        let ty_exp = match expander.expand(items[2].clone()) { Ok(t)=>t, Err(e)=>{println!("Exp Err: {:?}",e);continue;} };
                        let mut elab = Elaborator::new(env);
                        let ty_core = match elab.elaborate(ty_exp) { Ok(t)=>t, Err(e)=>{println!("Elab Err: {:?}",e);continue;} };
                        
                        // Pre-register inductive to support recursion in constructors
                        let placeholder = kernel::ast::InductiveDecl {
                            name: name.clone(),
                            univ_params: vec![],
                            ty: ty_core.clone(),
                            ctors: vec![],
                        };
                        env.add_inductive(placeholder);
                        
                        // Constructors
                        let mut ctors = Vec::new();
                        let mut failed = false;
                        for ctor_spec in items.iter().skip(3) {
                            // Only process valid ctor lists
                            if let SyntaxKind::List(citems) = &ctor_spec.kind {
                                if citems.len() != 3 { println!("Error: ctor spec len"); failed=true; break; }
                                if let SyntaxKind::Symbol(k) = &citems[0].kind {
                                    if k != "ctor" { println!("Error: expected ctor keyword"); failed=true; break; }
                                }
                                let cname = if let SyntaxKind::Symbol(n)=&citems[1].kind { n.clone() } else { println!("Error ctor name"); failed=true; break; };
                                
                                let cty_exp = match expander.expand(citems[2].clone()) { Ok(t)=>t, Err(e)=>{println!("Exp Err: {:?}",e); failed=true; break;} };
                                let mut elab_c = Elaborator::new(env); 
                                let cty_core = match elab_c.elaborate(cty_exp) { Ok(t)=>t, Err(e)=>{println!("Elab Err: {:?}",e); failed=true; break;} };
                                
                                ctors.push(kernel::ast::Constructor { name: cname, ty: cty_core });
                            } else { println!("Error: ctor spec not list"); failed=true; break; }
                        }
                        if failed { continue; }
                        
                        let decl = kernel::ast::InductiveDecl {
                            name: name.clone(),
                            univ_params: vec![],
                            ty: ty_core,
                            ctors: ctors,
                        };
                        env.add_inductive(decl);
                        if show_type { println!("Defined inductive {}", name); }
                        continue;
                    }
                }
            }
        }

        // 2. Expand (Normal term)
        let expanded = match expander.expand(syntax) {
            Ok(term) => term,
            Err(e) => {
                println!("Expansion Error: {:?}", e);
                continue;
            }
        };

        // 3. Elaborate
        let mut elaborator = Elaborator::new(env);
        let core_term = match elaborator.elaborate(expanded) {
            Ok(term) => term,
            Err(e) => {
                println!("Elaboration Error: {:?}", e);
                continue;
            }
        };

        // 4. Type Check / Infer
        let ctx = Context::new();
        match infer(env, &ctx, core_term.clone()) {
            Ok(ty) => {
                if show_type {
                    let ty_norm = whnf(env, ty);
                    println!(": {:?}", ty_norm);
                }
                
                if do_eval {
                    let val_norm = strong_normalize(env, core_term);
                    println!("= {}", pretty_print(env, &val_norm));
                }
            },
            Err(e) => {
                println!("Type Error: {:?}", e);
            }
        }
    }
}

fn strong_normalize(env: &Env, term: Rc<kernel::ast::Term>) -> Rc<kernel::ast::Term> {
    use kernel::ast::Term;
    let whnf = kernel::checker::whnf(env, term);
    match &*whnf {
        Term::App(f, a) => {
            Rc::new(Term::App(
                strong_normalize(env, f.clone()),
                strong_normalize(env, a.clone())
            ))
        }
        Term::Lam(ty, body) => {
            // We don't go under binders for now to avoid dealing with variable capture/renaming
            // unless we strictly need to. But for values (closed terms), we usually want to.
            // For simple math, we shouldn't have free vars in body if it's a value.
            // But we have De Bruijn indices.
            // If we normalize body, we must be careful?
            // `whnf` doesn't reduce under lambda.
            // But for `Nat`, we don't have lambdas in values (except inside closures).
            // Let's recurse.
            Rc::new(Term::Lam(
                strong_normalize(env, ty.clone()),
                strong_normalize(env, body.clone())
            ))
        }
        Term::Pi(ty, body) => {
            Rc::new(Term::Pi(
                strong_normalize(env, ty.clone()),
                strong_normalize(env, body.clone())
            ))
        }
        Term::LetE(ty, v, b) => { // Should be removed by whnf
             strong_normalize(env, b.subst(0, v)) 
        }
        _ => whnf,
    }
}

fn pretty_print(env: &Env, term: &kernel::ast::Term) -> String {
    use kernel::ast::Term;
    match term {
        Term::Var(i) => format!("#{}", i),
        Term::Sort(l) => format!("Sort({:?})", l), // Simplify level printing if possible
        Term::Const(n, _) => n.clone(),
        Term::App(f, a) => {
            // Flatten app spine
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
        Term::Lam(_, body) => format!("(lam {})", pretty_print(env, &**body)),
        Term::Pi(_, body) => format!("(pi {})", pretty_print(env, &**body)), // infer name?
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
    }
}
