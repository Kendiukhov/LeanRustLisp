use kernel::checker::{Env, Context, check};
use kernel::ast::{Term, InductiveDecl};
use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use frontend::elaborator::{Elaborator, ElabError};
use frontend::surface::SyntaxKind;
use codegen::Codegen;
use std::fs;
use std::path::Path;
use std::rc::Rc;
use ariadne::{Report, ReportKind, Label, Source, Color};

pub fn compile_file(path: &str, output_path: Option<String>) {
    let mut env = Env::new();
    let mut expander = Expander::new();

    let prelude_path = "stdlib/prelude.lrl";
    let mut defs: Vec<(String, Term)> = Vec::new();
    let mut main_term: Option<Term> = None;

    // Helper to process content
    let mut process = |filename: &str, content: &str| {
        let mut parser = Parser::new(content);
        let syntax_nodes = match parser.parse() {
            Ok(n) => n,
            Err(e) => { 
                println!("Parse Error in {}: {:?}", filename, e); 
                return; 
            }
        };

        // Error reporter helper
        let report_elab_err = |e: ElabError| {
            let (msg, span) = match &e {
                ElabError::UnboundVariable(n, s) => (format!("Unbound variable: {}", n), *s),
                ElabError::UnknownInductive(n, s) => (format!("Unknown inductive type: {}", n), *s),
                ElabError::NotImplemented(s) => ("Elaboration not implemented".to_string(), *s),
            };
            
            Report::build(ReportKind::Error, filename, span.start)
                .with_message(msg.clone())
                .with_label(Label::new((filename, span.start..span.end))
                    .with_message(msg)
                    .with_color(Color::Red))
                .finish()
                .print((filename, Source::from(content)))
                .unwrap();
        };

        for syntax in syntax_nodes {
             if let SyntaxKind::List(ref items) = syntax.kind {
                if !items.is_empty() {
                    // DEBUG
                    if let SyntaxKind::Symbol(ref s) = items[0].kind {
                         println!("Processing: {}", s);
                    } else {
                         println!("Processing unknown list: {:?}", items[0]);
                    }
                }

                if items.len() >= 3 {
                    if let SyntaxKind::Symbol(ref s) = items[0].kind {
                        if s == "def" {
                            if items.len() < 4 {
                                println!("Def len err: {}", items.len());
                                continue;
                            }
                            let name_ref = if let SyntaxKind::Symbol(n) = &items[1].kind { n } else { continue };
                            
                            println!("Processing def: {} with type: {:?}", name_ref, items[2]);

                            let name = name_ref.clone();
                            let ty_node = &items[2];
                            let val_node = &items[3];
                             
                             let ty_exp = match expander.expand(ty_node.clone()) { 
                                 Ok(t)=>t, 
                                 Err(e)=>{ println!("Def Ty Expansion Error {}: {:?}", name, e); continue; } 
                             };
                             let mut elab = Elaborator::new(&mut env);
                             let ty_core = match elab.elaborate(ty_exp) { 
                                 Ok(t)=>t, 
                                 Err(e)=>{ report_elab_err(e); continue; } 
                             };
                             
                             let val_exp = match expander.expand(val_node.clone()) { 
                                 Ok(t)=>t, 
                                 Err(e)=>{ println!("Def Val Expansion Error {}: {:?}", name, e); continue; } 
                             };
                             let mut elab2 = Elaborator::new(&mut env);
                             let val_core = match elab2.elaborate(val_exp) { 
                                 Ok(t)=>t, 
                                 Err(e)=>{ report_elab_err(e); continue; } 
                             };
                             
                             // Check
                             let ctx = Context::new();
                             println!("Check Def {}: ty_core={:?} val_core={:?}", name, ty_core, val_core);
                             match check(&mut env, &ctx, val_core.clone(), ty_core.clone()) {
                                 Ok(_) => {
                                     env.add_def(name.clone(), ty_core, val_core.clone());
                                     defs.push((name, (*val_core).clone()));
                                 },
                                 Err(e) => {
                                      println!("Def Check Error {}: {:?}", name, e);
                                 }
                             }
                             continue;
                        } else if s == "inductive" {
                              if items.len() < 3 { continue; }
                              let name = if let SyntaxKind::Symbol(n) = &items[1].kind { n.clone() } else { continue; };
                              
                              let ty_exp = match expander.expand(items[2].clone()) { Ok(t)=>t, Err(e)=>{ println!("Ind Ty Exp Err: {:?}", e); continue; } };
                              let mut elab = Elaborator::new(&mut env);
                              let ty_core = match elab.elaborate(ty_exp) { Ok(t)=>t, Err(e)=>{ report_elab_err(e); continue; } };

                              // Pre-register
                              env.add_inductive(InductiveDecl { name: name.clone(), univ_params: vec![], ty: ty_core.clone(), ctors: vec![] });

                              let mut ctors = Vec::new();
                              for ctor_spec in items.iter().skip(3) {
                                  if let SyntaxKind::List(citems) = &ctor_spec.kind {
                                      if citems.len() == 3 {
                                          let cname = if let SyntaxKind::Symbol(n)=&citems[1].kind { n.clone() } else { continue; };
                                          let cty_exp = match expander.expand(citems[2].clone()) { Ok(t)=>t, Err(e)=>{ println!("Ctor Exp Err: {:?}", e); continue; } };
                                          let mut elab_c = Elaborator::new(&mut env);
                                          let cty_core = match elab_c.elaborate(cty_exp) { Ok(t)=>t, Err(e)=>{ report_elab_err(e); continue; } };
                                          ctors.push(kernel::ast::Constructor { name: cname, ty: cty_core });
                                      }
                                  }
                              }
                              let decl = InductiveDecl { name: name.clone(), univ_params: vec![], ty: ty_core, ctors: ctors.clone() };
                              env.add_inductive(decl);

                              // Register constructors
                              for (i, ctor) in ctors.iter().enumerate() {
                                  let val = Rc::new(kernel::ast::Term::Ctor(name.clone(), i, vec![]));
                                  env.add_def(ctor.name.clone(), ctor.ty.clone(), val.clone());
                                  defs.push((ctor.name.clone(), (*val).clone()));
                              }
                              continue;
                        } else if s == "defmacro" {
                             expander.expand(syntax.clone()).ok();
                             continue;
                        }
                    }
                }
             }

             // Main term
             let expanded = match expander.expand(syntax) { Ok(t)=>t, Err(e)=>{ println!("Expansion Error: {:?}", e); continue;} };
             let mut elab = Elaborator::new(&mut env);
             let core = match elab.elaborate(expanded) { Ok(t)=>t, Err(e)=>{ report_elab_err(e); continue;} };
             
             main_term = Some((*core).clone());
        }
    };

    // 1. Process Prelude
    if Path::new(prelude_path).exists() {
         if let Ok(content) = fs::read_to_string(prelude_path) {
             process(prelude_path, &content);
         }
    }
    
    // 2. Process User File
    if let Ok(content) = fs::read_to_string(path) {
        process(path, &content);
    } else {
        println!("Error reading file: {}", path);
        return;
    }

    // 3. Generate Code
    let code = match Codegen::generate_program(defs, main_term, env.inductives.clone()) {
        Ok(code) => code,
        Err(e) => { println!("Codegen Error: {:?}", e); return; }
    };

    // 4. Write to output.rs and Compile
    let build_dir = "build";
    fs::create_dir_all(build_dir).ok();
    let source_file = format!("{}/output.rs", build_dir);
    let binary_file = output_path.unwrap_or_else(|| "output".to_string());

    if let Err(e) = fs::write(&source_file, &code) {
        println!("Error writing output file: {:?}", e);
        return;
    }

    println!("Compiling {} to {}...", source_file, binary_file);
    let status = std::process::Command::new("rustc")
        .arg("output.rs")
        .arg("-o")
        .arg(&binary_file) // Output to build/binary_file
        .arg("-C")
        .arg("incremental=incremental")
        .current_dir(build_dir)
        .status();

    match status {
        Ok(s) => {
            if s.success() {
                // Move binary from build/binary_file to root
                let _ = fs::rename(format!("{}/{}", build_dir, binary_file), &binary_file);
                println!("Compilation successful. Binary '{}' created.", binary_file);
            } else {
                println!("Compilation failed.");
            }
        }
        Err(e) => println!("Error running rustc: {:?}", e),
    }
}
