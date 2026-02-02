use kernel::checker::{Env, Context};
use kernel::ast::{Term, BinderInfo, InductiveDecl, Constructor, Transparency, Totality, Definition};
use frontend::parser::Parser;
use frontend::macro_expander::{Expander, MacroDef};
use frontend::elaborator::{Elaborator, ElabError};
use frontend::declaration_parser::DeclarationParser;
use frontend::surface::{Declaration, Span};
use frontend::diagnostics::{Diagnostic, Level, DiagnosticCollector, DiagnosticHandler};
use std::rc::Rc;
use std::fs;
use mir;

#[derive(Debug)]
pub enum DriverError {
    ParseValidations(Vec<String>),
    ElaborationErrors(Vec<String>),
    IoError(std::io::Error),
    Other(String),
}

/// Compilation/Interpretation Options
pub struct PipelineOptions {
    pub show_types: bool,
    pub show_eval: bool,
    pub verbose: bool,
    pub collect_artifacts: bool,
}

impl Default for PipelineOptions {
    fn default() -> Self {
        PipelineOptions {
            show_types: false,
            show_eval: false,
            verbose: false,
            collect_artifacts: false,
        }
    }
}

#[derive(Debug)]
pub enum Artifact {
    ElaboratedDef { name: String, ty: String, val: String },
    MirBody { name: String, body: String },
    BorrowCheck { name: String, errors: Vec<String> },
    AxiomDependencies { name: String, axioms: Vec<String>, classical: Vec<String> },
}

/// The result of processing a chunk of code.
/// Contains the list of successfully elaborated definitions (for backend use).
pub struct ProcessingResult {
    pub deployed_definitions: Vec<String>, // Names of definitions added
    pub evaluated_terms: Vec<(Rc<Term>, Rc<Term>)>, // (Type, Value) of evaluated expressions
    pub artifacts: Vec<Artifact>,
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
    println!("DEBUG: process_code called for {}", filename);
    
    let mut parser = Parser::new(source);
    let syntax_nodes = match parser.parse() {
        Ok(nodes) => nodes,
        Err(e) => {
            diagnostics.handle(Diagnostic::error(format!("Parse error: {:?}", e)));
            return Err(DriverError::ParseValidations(vec![format!("{:?}", e)]));
        }
    };

    let mut decl_parser = DeclarationParser::new(expander);
    let parse_result = decl_parser.parse(syntax_nodes);
    drop(decl_parser); // Release borrow of expander

    let decls = match parse_result {
        Ok(decls) => decls,
        Err(e) => {
             if !expander.expansion_trace.is_empty() {
                 println!("Macro Expansion Trace:");
                 for (name, span) in &expander.expansion_trace {
                     println!("  In macro '{}' at line {}:{}", name, span.line, span.col);
                 }
                 expander.expansion_trace.clear();
             }
             diagnostics.handle(Diagnostic::error(format!("Declaration parsing error: {:?}", e)));
             return Err(DriverError::ParseValidations(vec![format!("{:?}", e)]));
        }
    };

    let mut processed = ProcessingResult {
        deployed_definitions: Vec::new(),
        evaluated_terms: Vec::new(),
        artifacts: Vec::new(),
    };

    for decl in decls {
        // println!("Processing decl"); // Too verbose?
        match decl {
            Declaration::Def { ref name, .. } => println!("DEBUG: Processing Def {}", name),
            Declaration::Expr(_) => println!("DEBUG: Processing Expr"),
            _ => {}
        }
        
        match decl {
            Declaration::Def { name, ty, val, totality, transparency } => {
                let mut elab = Elaborator::new(env);
                
                // Infer Type
                let ty_core = match elab.infer(ty) {
                    Ok((t, s)) => {
                        // Ensure it's a type (Sort)
                        if !matches!(*s, Term::Sort(_)) {
                            diagnostics.handle(Diagnostic::error(format!("Type of definition '{}' must be a Sort", name)));
                            continue;
                        }
                        let t = elab.instantiate_metas(&t);
                        if let Err(msg) = validate_core_invariants(&t) {
                            diagnostics.handle(Diagnostic::error(format!(
                                "Type of definition '{}' violates core invariants: {}",
                                name, msg
                            )));
                            continue;
                        }
                        t
                    },
                    Err(e) => {
                        diagnostics.handle(Diagnostic::error(format!("Elaboration error (Type) in '{}': {}", name, e)));
                        continue;
                    }
                };

                // Check Value
                let val_core = match elab.check(val, &ty_core) {
                    Ok(t) => {
                         if let Err(e) = elab.solve_constraints() {
                             diagnostics.handle(Diagnostic::error(format!("Unsolved constraints in '{}': {:?}", name, e)));
                             continue;
                         }
                         let t = elab.instantiate_metas(&t);
                         if let Err(msg) = validate_core_invariants(&t) {
                             println!("DEBUG: Definition '{}' violates core invariants: {}", name, msg);
                             diagnostics.handle(Diagnostic::error(format!(
                                 "Definition '{}' violates core invariants: {}",
                                 name, msg
                             )));
                             continue;
                         }
                         t
                    },
                    Err(e) => {
                        diagnostics.handle(Diagnostic::error(format!("Elaboration error (Value) in '{}': {}", name, e)));
                        continue;
                    }
                };

                // Kernel re-check to enforce the trusted kernel boundary.
                let ctx = Context::new();
                let ty_ty = match kernel::checker::infer(env, &ctx, ty_core.clone()) {
                    Ok(t) => t,
                    Err(e) => {
                        diagnostics.handle(Diagnostic::error(format!(
                            "Kernel re-check failed for type of '{}': {:?}",
                            name, e
                        )));
                        continue;
                    }
                };
                let ty_ty_norm = match kernel::checker::whnf(env, ty_ty, kernel::Transparency::Reducible) {
                    Ok(norm) => norm,
                    Err(e) => {
                        diagnostics.handle(Diagnostic::error(format!(
                            "Kernel re-check failed for type of '{}': {:?}",
                            name, e
                        )));
                        continue;
                    }
                };
                if !matches!(&*ty_ty_norm, Term::Sort(_)) {
                    diagnostics.handle(Diagnostic::error(format!(
                        "Kernel re-check failed for type of '{}': expected a Sort, got {:?}",
                        name, ty_ty_norm
                    )));
                    continue;
                }
                if let Err(e) = kernel::checker::check(env, &ctx, val_core.clone(), ty_core.clone()) {
                    diagnostics.handle(Diagnostic::error(format!(
                        "Kernel re-check failed for '{}': {:?}",
                        name, e
                    )));
                    continue;
                }

                // Add to Env
                let mut def = match totality {
                    Totality::Partial => {
                        kernel::ast::Definition::partial(name.clone(), ty_core.clone(), val_core.clone())
                    }
                    Totality::Unsafe => {
                        kernel::ast::Definition::unsafe_def(name.clone(), ty_core.clone(), val_core.clone())
                    }
                    Totality::Total | Totality::WellFounded => {
                        kernel::ast::Definition::total(name.clone(), ty_core.clone(), val_core.clone())
                    }
                    Totality::Axiom => {
                        kernel::ast::Definition::total(name.clone(), ty_core.clone(), val_core.clone())
                    }
                };
                def.transparency = transparency;
                
                if options.collect_artifacts {
                    processed.artifacts.push(Artifact::ElaboratedDef {
                        name: name.clone(),
                        ty: format!("{:?}", ty_core),
                        val: format!("{:?}", val_core),
                    });
                }
                
                match env.add_definition(def) {
                    Ok(_) => {
                        processed.deployed_definitions.push(name.clone());
                        if options.verbose || options.show_types {
                            println!("Defined {} ({})", name, totality_label(totality));
                        }

                        if let Some(def) = env.get_definition(&name) {
                            report_axiom_dependencies(env, def, diagnostics);
                            if options.collect_artifacts && !def.axioms.is_empty() {
                                let classical = kernel::checker::classical_axiom_dependencies(env, def);
                                processed.artifacts.push(Artifact::AxiomDependencies {
                                    name: name.clone(),
                                    axioms: def.axioms.clone(),
                                    classical,
                                });
                            }
                        }

                        // MIR Validation Pipeline (Unified)
                        // Even in REPL/Driver mode, we check safety constraints.
                        if let Some(d) = env.definitions().get(&name) {
                             if let Some(val) = &d.value {
                                 let mut ctx = mir::lower::LoweringContext::new(vec![], d.ty.clone(), &env);
                                 let dest = mir::Place::from(mir::Local(0));
                                 let target = mir::BasicBlock(1);
                                 ctx.body.basic_blocks.push(mir::BasicBlockData {
                                     statements: vec![],
                                     terminator: Some(mir::Terminator::Return)
                                 });
                                 if let Err(e) = ctx.lower_term(val, dest, target) {
                                     diagnostics.handle(Diagnostic::error(format!("Lowering error in {}: {}", name, e)));
                                     continue;
                                 }
                                 
                                 if options.collect_artifacts {
                                     processed.artifacts.push(Artifact::MirBody {
                                         name: name.clone(),
                                         body: format!("{:?}", ctx.body),
                                     });
                                 }

                                 // Check Ownership
                                 let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
                                 ownership.analyze();
                                 let ownership_errors = ownership.check();
                                 for e in &ownership_errors {
                                     diagnostics.handle(Diagnostic::error(format!("Ownership error in {}: {}", name, e)));
                                 }
                                 
                                 // Check Borrows
                                 // Check NLL
                                 let mut nll = mir::analysis::nll::NllChecker::new(&ctx.body);
                                 nll.check();
                                 let nll_result = nll.into_result();
                                 for e in &nll_result.errors {
                                     diagnostics.handle(Diagnostic::error(format!("Borrow error in {}: {}", name, e)));
                                 }
                                 if nll_result.is_ok() {
                                     nll_result.inject_runtime_checks(&mut ctx.body);
                                 }

                                 // Check Lints (Panic Free)
                                 let mut linter = mir::lints::PanicFreeLinter::new(&ctx.body);
                                 linter.check();
                                 for e in &linter.errors {
                                     diagnostics.handle(Diagnostic::error(format!("Lint error in {}: {}", name, e)));
                                 }

                                 if options.collect_artifacts {
                                     let mut errors = Vec::new();
                                     errors.extend(ownership_errors);
                                     errors.extend(nll_result.errors.iter().map(|e| e.to_string()));
                                     
                                     processed.artifacts.push(Artifact::BorrowCheck {
                                         name: name.clone(),
                                         errors,
                                     });
                                 }
                             }
                        }
                    }
                    Err(e) => diagnostics.handle(Diagnostic::error(format!("Environment error defining '{}': {:?}", name, e))),
                }
            }

            Declaration::Axiom { name, ty, tags } => {
                let mut elab = Elaborator::new(env);
                let ty_core = match elab.infer(ty) {
                    Ok((t, s)) => {
                        if !matches!(*s, Term::Sort(_)) {
                             diagnostics.handle(Diagnostic::error(format!("Axiom '{}' type must be a Sort", name)));
                             continue;
                        }
                        elab.instantiate_metas(&t)
                    },
                    Err(e) => {
                        diagnostics.handle(Diagnostic::error(format!("Elaboration error (Axiom Type) in '{}': {}", name, e)));
                        continue;
                    }
                };
                
                if let Err(e) = env.add_definition(Definition::axiom_with_tags(name.clone(), ty_core, tags.clone())) {
                    diagnostics.handle(Diagnostic::error(format!(
                        "Kernel error declaring axiom '{}': {:?}",
                        name, e
                    )));
                    continue;
                }
                if options.verbose || options.show_types { println!("Axiom {} declared", name); }
                if let Some(def) = env.get_definition(&name) {
                    report_axiom_dependencies(env, def, diagnostics);
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

            Declaration::Inductive { name, ty, ctors, is_copy } => {
                let mut elab = Elaborator::new(env);
                let (ty_core, _) = match elab.infer(ty) {
                    Ok((t, s)) => (elab.instantiate_metas(&t), s),
                    Err(e) => {
                        diagnostics.handle(Diagnostic::error(format!("Elaboration error (Inductive Type) '{}': {}", name, e)));
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
                    is_copy
                };
                if let Err(e) = env.add_inductive(placeholder) {
                     diagnostics.handle(Diagnostic::error(format!("Error adding placeholder '{}': {:?}", name, e)));
                     continue;
                }

                // Constructors
                let mut kernel_ctors = Vec::new();
                for (cname, cty) in ctors {
                     let mut elab_c = Elaborator::new(env);
                     let (cty_core, _) = match elab_c.infer(cty) {
                         Ok((t, _)) => (elab_c.instantiate_metas(&t), ()),
                         Err(e) => {
                             diagnostics.handle(Diagnostic::error(format!("Elaboration error (Constructor '{}'): {}", cname, e)));
                             continue;
                         }
                     };
                     kernel_ctors.push(Constructor { name: cname, ty: cty_core });
                }

                // Final Register
                let decl = InductiveDecl {
                    name: name.clone(),
                    univ_params: vec![],
                    num_params: 0,
                    ty: ty_core,
                    ctors: kernel_ctors.clone(),
                    is_copy
                };

                if let Err(e) = env.add_inductive(decl) {
                     diagnostics.handle(Diagnostic::error(format!("Error registering inductive '{}': {:?}", name, e)));
                     continue;
                }
                
                // Register constructors as definitions (for backend visibility)
                for (i, ctor) in kernel_ctors.iter().enumerate() {
                    let val = Rc::new(Term::Ctor(name.clone(), i, vec![]));
                    let def = Definition::total(ctor.name.clone(), ctor.ty.clone(), val.clone());
                    if let Err(e) = env.add_definition(def) {
                        diagnostics.handle(Diagnostic::error(format!(
                            "Error registering constructor '{}': {:?}",
                            ctor.name, e
                        )));
                    }
                }

                if options.verbose || options.show_types { println!("Defined inductive {}", name); }
                processed.deployed_definitions.push(name);
            }

            Declaration::DefMacro { name, args, body } => {
                let macro_def = MacroDef { args, body };
                expander.macros.insert(name.clone(), macro_def);
                if options.verbose { println!("Defined macro {}", name); }
            }

            Declaration::Expr(term) => {
                let mut elab = Elaborator::new(env);
                match elab.infer(term) {
                    Ok((core_term, ty)) => {
                        let mut valid = true;
                        if let Err(e) = elab.solve_constraints() {
                             diagnostics.handle(Diagnostic::error(format!("Unsolved constraints in expression: {:?}", e)));
                             valid = false;
                        }
                        
                        let core_term = elab.instantiate_metas(&core_term);
                        if valid {
                             if let Err(msg) = validate_core_invariants(&core_term) {
                                 println!("DEBUG: Expr violates core invariants: {} {:?}", msg, core_term);
                                 diagnostics.handle(Diagnostic::error(format!(
                                     "Expression violates core invariants: {}",
                                     msg
                                 )));
                                 valid = false;
                             } else {
                                 println!("DEBUG: Valid Term: {:?}", core_term);
                             }
                        }

                        let ty = elab.instantiate_metas(&ty);
                        if let Err(msg) = validate_core_invariants(&ty) {
                            diagnostics.handle(Diagnostic::error(format!(
                                "Expression type violates core invariants: {}",
                                msg
                            )));
                            valid = false;
                        }

                        if !valid {
                            continue;
                        }

                        // WHNF type if needed
                        let ty_norm = match kernel::checker::whnf(env, ty.clone(), kernel::Transparency::All) {
                            Ok(norm) => norm,
                            Err(e) => {
                                diagnostics.handle(Diagnostic::error(format!(
                                    "Failed to normalize type for display: {:?}",
                                    e
                                )));
                                continue;
                            }
                        };
                        processed.evaluated_terms.push((ty_norm.clone(), core_term.clone()));
                        
                        if options.show_types {
                            println!(": {:?}", ty_norm);
                        }
                     if options.show_eval {
                         println!("DEBUG: About to normalize");
                         let val_norm = nbe_normalize(env, core_term);
                         //let val_norm = nbe_eval(env, core_term); // Use eval for now? No, normalize for readable output
                         
                         println!("DEBUG: Normalized");
                         println!("DEBUG: Normalized: {:?}", val_norm);
                         if true {
                             println!("Eval: {:?}", val_norm);
                         }
                     }
                    },
                    Err(e) => {
                        diagnostics.handle(Diagnostic::error(format!("Elaboration error (Expression): {}", e)));
                    }
                }
            }
        }
    }

    Ok(processed)
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

fn report_axiom_dependencies(env: &Env, def: &kernel::ast::Definition, diagnostics: &mut DiagnosticCollector) {
    if def.axioms.is_empty() {
        return;
    }

    let classical = kernel::checker::classical_axiom_dependencies(env, def);
    let message = if def.totality == Totality::Axiom {
        if classical.is_empty() {
            format!("Axiom '{}' declared", def.name)
        } else {
            format!("Axiom '{}' declared (classical: {})", def.name, classical.join(", "))
        }
    } else if classical.is_empty() {
        format!(
            "Definition '{}' depends on axioms: {}",
            def.name,
            def.axioms.join(", ")
        )
    } else {
        format!(
            "Definition '{}' depends on axioms: {} (classical: {})",
            def.name,
            def.axioms.join(", "),
            classical.join(", ")
        )
    };

    diagnostics.handle(Diagnostic::warning(message));
}

fn validate_core_invariants(t: &Rc<Term>) -> Result<(), String> {
    kernel::checker::validate_core_term(t).map_err(|e| e.to_string())
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
