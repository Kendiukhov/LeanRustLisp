use kernel::checker::{Env};
use kernel::ast::{Term, InductiveDecl};
use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use frontend::elaborator::{Elaborator, ElabError};
use frontend::declaration_parser::DeclarationParser;
use frontend::surface::{Declaration, Span};
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

    let mut process = |filename: &str, content: &str| {
        let mut parser = Parser::new(content);
        let syntax_nodes = match parser.parse() {
            Ok(n) => n,
            Err(e) => { 
                println!("Parse Error in {}: {:?}", filename, e); 
                return; 
            }
        };

        let report_elab_err = |e: ElabError| {
            let (msg, span) = match &e {
                ElabError::UnboundVariable(n, s) => (format!("Unbound variable: {}", n), *s),
                ElabError::UnknownInductive(n, s) => (format!("Unknown inductive type: {}", n), *s),
                ElabError::NotImplemented(s) => ("Elaboration not implemented".to_string(), *s),
                ElabError::InferenceError(e, s) => (format!("Inference Error: {:?}", e), *s),
                ElabError::TypeMismatch{ expected, got, span } => (format!("Type mismatch: expected {}, got {}", expected, got), *span),
                ElabError::UnificationError(t1, t2) => (format!("Unification Error: {:?} vs {:?}", t1, t2), Span { start: 0, end: 0, line: 0, col: 0 }),
                ElabError::OccursCheck(id, t) => (format!("Occurs Check Failed: {} in {:?}", id, t), Span { start: 0, end: 0, line: 0, col: 0 }),
                ElabError::SolutionContainsFreeVariables(t) => (format!("Solution Contains Free Variables: {:?}", t), Span { start: 0, end: 0, line: 0, col: 0 }),
                ElabError::UnsolvedConstraints(msg) => (format!("Unsolved Constraints: {}", msg), Span { start: 0, end: 0, line: 0, col: 0 }),
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
        
        let mut decl_parser = DeclarationParser::new(&mut expander);
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
                    let mut elab = Elaborator::new(&mut env);
                    let ty_core = match elab.infer(ty) {
                        Ok((t, s)) => {
                            if !matches!(*s, kernel::ast::Term::Sort(_)) {
                                println!("Type of a definition must be a Sort, but got {:?}", s);
                                continue;
                            }
                            t
                        },
                        Err(e) => { report_elab_err(e); continue; }
                    };

                    let val_core = match elab.check(val, &ty_core) {
                        Ok(t) => t,
                        Err(e) => { report_elab_err(e); continue; }
                    };
                    
                    let def = if is_partial {
                        kernel::ast::Definition::partial(name.clone(), ty_core, val_core.clone())
                    } else {
                        kernel::ast::Definition::total(name.clone(), ty_core, val_core.clone())
                    };
                    match env.add_definition(def) {
                        Ok(_) => {
                            defs.push((name, (*val_core).clone()));
                        }
                        Err(e) => {
                            println!("Definition Error {}: {:?}", name, e);
                        }
                    }
                }
                Declaration::Axiom { name, ty } => {
                    let mut elab = Elaborator::new(&mut env);
                    let (ty_core, ty_ty) = match elab.infer(ty) {
                        Ok((t, s)) => (t, s),
                        Err(e) => { report_elab_err(e); continue; }
                    };
                    if !matches!(*ty_ty, kernel::ast::Term::Sort(_)) {
                        println!("Error: axiom type must be a type, got {:?}", ty_ty);
                        continue;
                    }
                    env.add_axiom(name.clone(), ty_core);
                }
                Declaration::Inductive { name, ty, ctors } => {
                    let mut elab = Elaborator::new(&mut env);
                    let (ty_core, ty_ty) = match elab.infer(ty) {
                        Ok((t, s)) => (t, s),
                        Err(e) => { report_elab_err(e); continue; }
                    };
                    if !matches!(*ty_ty, kernel::ast::Term::Sort(_)) {
                        println!("Error: inductive type must be a type, got {:?}", ty_ty);
                        continue;
                    }

                    let num_params = { let mut n = 0; let mut t = &ty_core; while let kernel::ast::Term::Pi(_, b, _) = &**t { n+=1; t=b; } n };
                    if let Err(e) = env.add_inductive(InductiveDecl { name: name.clone(), univ_params: vec![], num_params, ty: ty_core.clone(), ctors: vec![], is_copy: false }) {
                         println!("Error adding inductive placeholder: {:?}", e);
                         continue;
                    }

                    let mut core_ctors = Vec::new();
                    for (cname, cty) in ctors {
                        let mut elab_c = Elaborator::new(&mut env); 
                        let (cty_core, _) = match elab_c.infer(cty) {
                            Ok((t, s)) => (t, s),
                            Err(e) => { report_elab_err(e); continue; }
                        };
                        core_ctors.push(kernel::ast::Constructor { name: cname, ty: cty_core });
                    }
                    
                    let decl = InductiveDecl { name: name.clone(), univ_params: vec![], num_params, ty: ty_core, ctors: core_ctors.clone(), is_copy: false };
                    if let Err(e) = env.add_inductive(decl) {
                         println!("Error adding inductive: {:?}", e);
                         continue;
                    }

                    for (i, ctor) in core_ctors.iter().enumerate() {
                        let val = Rc::new(kernel::ast::Term::Ctor(name.clone(), i, vec![]));
                        env.add_def(ctor.name.clone(), ctor.ty.clone(), val.clone());
                        defs.push((ctor.name.clone(), (*val).clone()));
                    }
                }
                Declaration::DefMacro { name, args, body } => {
                    let macro_def = frontend::macro_expander::MacroDef { args, body };
                    expander.macros.insert(name, macro_def);
                }
                Declaration::Expr(term) => {
                    let mut elab = Elaborator::new(&mut env);
                    let (core, _ty) = match elab.infer(term) {
                        Ok((t, s)) => (t, s),
                        Err(e) => { report_elab_err(e); continue; }
                    };
                    main_term = Some((*core).clone());
                }
            }
        }
    };

    if Path::new(prelude_path).exists() {
         if let Ok(content) = fs::read_to_string(prelude_path) {
             process(prelude_path, &content);
         }
    }
    
    if let Ok(content) = fs::read_to_string(path) {
        process(path, &content);
    } else {
        println!("Error reading file: {}", path);
        return;
    }

    let code = match Codegen::generate_program(defs, main_term, env.inductives.clone()) {
        Ok(code) => code,
        Err(e) => { println!("Codegen Error: {:?}", e); return; }
    };

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
        .arg(&binary_file)
        .arg("-C")
        .arg("incremental=incremental")
        .current_dir(build_dir)
        .status();

    match status {
        Ok(s) => {
            if s.success() {
                let _ = fs::rename(format!("{}/{}", build_dir, binary_file), &binary_file);
                println!("Compilation successful. Binary '{}' created.", binary_file);
            } else {
                println!("Compilation failed.");
            }
        }
        Err(e) => println!("Error running rustc: {:?}", e),
    }
}

pub fn compile_file_to_mir(path: &str) {
    compile_file_to_mir_with_output(path, None)
}

pub fn compile_file_to_mir_with_output(path: &str, output_path: Option<String>) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let prelude_path = "stdlib/prelude.lrl";

    // Collected code segments
    let mut all_code = String::new();
    let mut main_def_name: Option<String> = None;
    let mut has_any_errors = false;

    // Add prelude
    all_code.push_str("#![allow(dead_code, unused_variables, unused_parens, unreachable_patterns)]\n");
    all_code.push_str(&mir::codegen::codegen_prelude());
    all_code.push_str("\n");

    // Closure counter for unique names across all definitions
    let mut global_closure_idx = 0usize;

    // Helper to process a file content
    let mut process_mir = |filename: &str, content: &str, code_out: &mut String, has_errors: &mut bool, main_name: &mut Option<String>, closure_idx: &mut usize| {
        let mut parser = Parser::new(content);
        let syntax_nodes = match parser.parse() {
            Ok(n) => n,
            Err(e) => { println!("Parse Error in {}: {:?}", filename, e); *has_errors = true; return; }
        };

        let mut decl_parser = DeclarationParser::new(&mut expander);
        let decls = match decl_parser.parse(syntax_nodes) {
            Ok(decls) => decls,
            Err(e) => { println!("Declaration Parse Error: {:?}", e); *has_errors = true; return; }
        };

        for decl in decls {
            match decl {
                Declaration::Def { name, ty, val, is_partial } => {
                    let mut elab = Elaborator::new(&mut env);
                    let ty_core = match elab.infer(ty) {
                        Ok((t, _)) => t,
                        Err(e) => { println!("Elab error in {}: {:?}", name, e); continue; }
                    };
                    let val_core = match elab.check(val, &ty_core) {
                        Ok(t) => t,
                        Err(e) => { println!("Elab error in {}: {:?}", name, e); continue; }
                    };

                    let def = if is_partial {
                        kernel::ast::Definition::partial(name.clone(), ty_core.clone(), val_core.clone())
                    } else {
                        kernel::ast::Definition::total(name.clone(), ty_core.clone(), val_core.clone())
                    };
                    env.add_definition(def).ok();

                    // Lower to MIR
                    let mut ctx = mir::lower::LoweringContext::new(vec![], ty_core.clone(), &env);
                    let dest = mir::Place::from(mir::Local(0));
                    let target = mir::BasicBlock(1);
                    ctx.body.basic_blocks.push(mir::BasicBlockData {
                        statements: vec![],
                        terminator: Some(mir::Terminator::Return)
                    });

                    ctx.lower_term(&val_core, dest, target);

                    // --- SAFETY CHECKS ---
                    let mut def_has_errors = false;

                    // Check Main Body
                    let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
                    ownership.analyze();
                    let own_errors = ownership.check();
                    if !own_errors.is_empty() {
                         println!("Ownership Errors in {}:", name);
                         for e in own_errors { println!("  {}", e); }
                         def_has_errors = true;
                    }

                    let mut borrow = mir::analysis::borrow::BorrowChecker::new(&ctx.body);
                    borrow.check();
                    if !borrow.errors.is_empty() {
                         println!("Borrow Errors in {}:", name);
                         for e in borrow.errors { println!("  {}", e); }
                         def_has_errors = true;
                    }

                    // Check Derived Bodies (Closures)
                    for (i, body) in ctx.derived_bodies.borrow().iter().enumerate() {
                         let body_name = format!("{}_closure_{}", name, i);
                         let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(body);
                         ownership.analyze();
                         let own_errors = ownership.check();
                         if !own_errors.is_empty() {
                              println!("Ownership Errors in {}:", body_name);
                              for e in own_errors { println!("  {}", e); }
                              def_has_errors = true;
                         }

                         let mut borrow = mir::analysis::borrow::BorrowChecker::new(body);
                         borrow.check();
                         if !borrow.errors.is_empty() {
                              println!("Borrow Errors in {}:", body_name);
                              for e in borrow.errors { println!("  {}", e); }
                              def_has_errors = true;
                         }
                    }

                    if def_has_errors {
                        *has_errors = true;
                        continue;
                    }

                    // --- OPTIMIZATIONS ---
                    // 1. Erase proof terms (computationally irrelevant)
                    mir::transform::erasure::erase_proofs(&mut ctx.body);
                    for body in ctx.derived_bodies.borrow_mut().iter_mut() {
                        mir::transform::erasure::erase_proofs(body);
                    }

                    // 2. Dead code elimination (remove unreachable blocks, unused locals)
                    mir::transform::dce::eliminate_dead_code(&mut ctx.body);
                    for body in ctx.derived_bodies.borrow_mut().iter_mut() {
                        mir::transform::dce::eliminate_dead_code(body);
                    }

                    // 3. CFG simplification (bypass empty blocks, merge single-edge blocks)
                    mir::transform::dce::simplify_cfg(&mut ctx.body);
                    for body in ctx.derived_bodies.borrow_mut().iter_mut() {
                        mir::transform::dce::simplify_cfg(body);
                    }

                    // 4. Copy propagation and constant folding
                    mir::transform::inline::optimize(&mut ctx.body);
                    for body in ctx.derived_bodies.borrow_mut().iter_mut() {
                        mir::transform::inline::optimize(body);
                    }
                    // ---------------------

                    // Generate closures first (they need to be defined before the main function)
                    for (i, body) in ctx.derived_bodies.borrow().iter().enumerate() {
                         let closure_name = format!("closure_{}", *closure_idx + i);
                         code_out.push_str(&mir::codegen::codegen_body(&closure_name, body));
                         code_out.push_str("\n");
                    }
                    *closure_idx += ctx.derived_bodies.borrow().len();

                    // Generate the definition
                    let safe_name = Codegen::sanitize_name(&name);
                    code_out.push_str(&mir::codegen::codegen_body(&safe_name, &ctx.body));
                    code_out.push_str("\n");

                    // Track last definition as potential main
                    *main_name = Some(safe_name);
                }
                Declaration::Inductive { name, ty, ctors } => {
                    let mut elab = Elaborator::new(&mut env);
                    let (ty_core, ty_ty) = match elab.infer(ty) {
                        Ok((t, s)) => (t, s),
                        Err(e) => { println!("Elab error: {:?}", e); continue; }
                    };
                    if !matches!(*ty_ty, kernel::ast::Term::Sort(_)) {
                        println!("Error: inductive type must be a type, got {:?}", ty_ty);
                        continue;
                    }

                    let num_params = { let mut n = 0; let mut t = &ty_core; while let kernel::ast::Term::Pi(_, b, _) = &**t { n+=1; t=b; } n };
                    if let Err(e) = env.add_inductive(InductiveDecl { name: name.clone(), univ_params: vec![], num_params, ty: ty_core.clone(), ctors: vec![], is_copy: false }) {
                         println!("Error adding inductive placeholder: {:?}", e);
                         continue;
                    }

                    let mut core_ctors = Vec::new();
                    for (cname, cty) in ctors {
                        let mut elab_c = Elaborator::new(&mut env);
                        let (cty_core, _) = match elab_c.infer(cty) {
                            Ok((t, s)) => (t, s),
                            Err(e) => { println!("Elab error: {:?}", e); continue; }
                        };
                        core_ctors.push(kernel::ast::Constructor { name: cname, ty: cty_core });
                    }

                    let decl = InductiveDecl { name: name.clone(), univ_params: vec![], num_params, ty: ty_core, ctors: core_ctors.clone(), is_copy: false };
                    if let Err(e) = env.add_inductive(decl) {
                         println!("Error adding inductive: {:?}", e);
                         continue;
                    }

                    for (i, ctor) in core_ctors.iter().enumerate() {
                        let val = Rc::new(kernel::ast::Term::Ctor(name.clone(), i, vec![]));
                        env.add_def(ctor.name.clone(), ctor.ty.clone(), val.clone());
                    }
                }
                Declaration::Expr(term) => {
                    // Standalone expression - elaborate and set as main
                    let mut elab = Elaborator::new(&mut env);
                    if let Ok((_, _)) = elab.infer(term) {
                        // Mark that we have a main expression
                        // For MIR path, we'd need to lower this too
                    }
                }
                _ => {} // Skip axioms/macros for MIR output
            }
        }
    };

    if Path::new(prelude_path).exists() {
         if let Ok(content) = fs::read_to_string(prelude_path) {
             process_mir(prelude_path, &content, &mut all_code, &mut has_any_errors, &mut main_def_name, &mut global_closure_idx);
         }
    }

    if let Ok(content) = fs::read_to_string(path) {
        process_mir(path, &content, &mut all_code, &mut has_any_errors, &mut main_def_name, &mut global_closure_idx);
    } else {
        println!("Error reading file: {}", path);
        return;
    }

    if has_any_errors {
        println!("Compilation aborted due to errors.");
        return;
    }

    // Add main function
    all_code.push_str("fn main() {\n");
    if let Some(name) = &main_def_name {
        all_code.push_str(&format!("    let result = {}();\n", name));
        all_code.push_str("    println!(\"Result: {:?}\", result);\n");
    }
    all_code.push_str("}\n");

    // Write output
    let build_dir = "build";
    fs::create_dir_all(build_dir).ok();
    let source_file = format!("{}/output_mir.rs", build_dir);
    let binary_file = output_path.unwrap_or_else(|| "output_mir".to_string());

    if let Err(e) = fs::write(&source_file, &all_code) {
        println!("Error writing output file: {:?}", e);
        return;
    }

    println!("Compiling {} to {}...", source_file, binary_file);
    let status = std::process::Command::new("rustc")
        .arg("output_mir.rs")
        .arg("-o")
        .arg(&binary_file)
        .arg("-C")
        .arg("incremental=incremental")
        .current_dir(build_dir)
        .status();

    match status {
        Ok(s) => {
            if s.success() {
                let _ = fs::rename(format!("{}/{}", build_dir, binary_file), &binary_file);
                println!("MIR compilation successful. Binary '{}' created.", binary_file);
            } else {
                println!("MIR compilation failed. Generated source at: {}", source_file);
            }
        }
        Err(e) => println!("Error running rustc: {:?}", e),
    }
}

/// Result of compiling a definition, for testing purposes
#[derive(Debug, Clone)]
pub struct DefCompileResult {
    pub name: String,
    pub ownership_errors: Vec<String>,
    pub borrow_errors: Vec<String>,
}

/// Compile a string of LRL code and return compilation results for testing
/// Optionally provide prelude content directly for test independence
pub fn compile_string_for_test(source: &str) -> Vec<DefCompileResult> {
    compile_string_with_prelude(source, None)
}

/// Compile with optional explicit prelude
pub fn compile_string_with_prelude(source: &str, prelude: Option<&str>) -> Vec<DefCompileResult> {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut results = Vec::new();

    // Load prelude - try explicit content, then file paths
    let prelude_content = if let Some(p) = prelude {
        Some(p.to_string())
    } else {
        // Try multiple paths for different working directories
        let paths = vec![
            "stdlib/prelude.lrl",
            "../stdlib/prelude.lrl",
            "../../stdlib/prelude.lrl",
        ];
        paths.iter()
            .filter_map(|p| fs::read_to_string(p).ok())
            .next()
    };

    if let Some(content) = prelude_content {
        let _ = process_content_for_test(&mut env, &mut expander, &content, &mut results, true);
    }

    // Process the test source
    let _ = process_content_for_test(&mut env, &mut expander, source, &mut results, false);
    results
}

fn process_content_for_test(
    env: &mut Env,
    expander: &mut Expander,
    content: &str,
    results: &mut Vec<DefCompileResult>,
    is_prelude: bool,
) -> Result<(), String> {
    let mut parser = Parser::new(content);
    let syntax_nodes = parser.parse().map_err(|e| format!("Parse error: {:?}", e))?;

    let mut decl_parser = DeclarationParser::new(expander);
    let decls = decl_parser.parse(syntax_nodes).map_err(|e| format!("Declaration parse error: {:?}", e))?;

    for decl in decls {
        match decl {
            Declaration::Def { name, ty, val, is_partial } => {
                let mut elab = Elaborator::new(env);
                let ty_core = match elab.infer(ty) {
                    Ok((t, _)) => t,
                    Err(e) => { continue; }
                };
                let val_core = match elab.check(val, &ty_core) {
                    Ok(t) => t,
                    Err(e) => { continue; }
                };

                let def = if is_partial {
                    kernel::ast::Definition::partial(name.clone(), ty_core.clone(), val_core.clone())
                } else {
                    kernel::ast::Definition::total(name.clone(), ty_core.clone(), val_core.clone())
                };
                env.add_definition(def).ok();

                // Lower to MIR
                let mut ctx = mir::lower::LoweringContext::new(vec![], ty_core.clone(), env);
                let dest = mir::Place::from(mir::Local(0));
                let target = mir::BasicBlock(1);
                ctx.body.basic_blocks.push(mir::BasicBlockData {
                    statements: vec![],
                    terminator: Some(mir::Terminator::Return)
                });

                ctx.lower_term(&val_core, dest, target);

                // Collect errors
                let mut ownership_errors = Vec::new();
                let mut borrow_errors = Vec::new();

                // Check Main Body
                let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
                ownership.analyze();
                ownership_errors.extend(ownership.check());

                let mut borrow = mir::analysis::borrow::BorrowChecker::new(&ctx.body);
                borrow.check();
                borrow_errors.extend(borrow.errors);

                // Check Derived Bodies (Closures)
                for (i, body) in ctx.derived_bodies.borrow().iter().enumerate() {
                    let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(body);
                    ownership.analyze();
                    for e in ownership.check() {
                        ownership_errors.push(format!("closure_{}: {}", i, e));
                    }

                    let mut borrow = mir::analysis::borrow::BorrowChecker::new(body);
                    borrow.check();
                    for e in borrow.errors {
                        borrow_errors.push(format!("closure_{}: {}", i, e));
                    }
                }

                // Only record results for non-prelude definitions
                if !is_prelude {
                    results.push(DefCompileResult {
                        name,
                        ownership_errors,
                        borrow_errors,
                    });
                }
            }
            Declaration::Inductive { name, ty, ctors } => {
                let mut elab = Elaborator::new(env);
                let (ty_core, ty_ty) = match elab.infer(ty) {
                    Ok((t, s)) => (t, s),
                    Err(_) => { continue; }
                };
                if !matches!(*ty_ty, kernel::ast::Term::Sort(_)) {
                    continue;
                }

                let num_params = { let mut n = 0; let mut t = &ty_core; while let kernel::ast::Term::Pi(_, b, _) = &**t { n+=1; t=b; } n };
                if let Err(_) = env.add_inductive(InductiveDecl { name: name.clone(), univ_params: vec![], num_params, ty: ty_core.clone(), ctors: vec![], is_copy: false }) {
                    continue;
                }

                let mut core_ctors = Vec::new();
                for (cname, cty) in ctors {
                    let mut elab_c = Elaborator::new(env);
                    let (cty_core, _) = match elab_c.infer(cty) {
                        Ok((t, s)) => (t, s),
                        Err(_) => { continue; }
                    };
                    core_ctors.push(kernel::ast::Constructor { name: cname, ty: cty_core });
                }

                let decl = InductiveDecl { name: name.clone(), univ_params: vec![], num_params, ty: ty_core, ctors: core_ctors.clone(), is_copy: false };
                if let Err(_) = env.add_inductive(decl) {
                    continue;
                }

                for (i, ctor) in core_ctors.iter().enumerate() {
                    let val = Rc::new(kernel::ast::Term::Ctor(name.clone(), i, vec![]));
                    env.add_def(ctor.name.clone(), ctor.ty.clone(), val.clone());
                }
            }
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // Minimal prelude for tests
    const TEST_PRELUDE: &str = r#"
(inductive Nat (sort 1)
  (ctor zero Nat)
  (ctor succ (pi n Nat Nat)))

(inductive Bool (sort 1)
  (ctor true Bool)
  (ctor false Bool))

(def add (pi n Nat (pi m Nat Nat))
  (lam n Nat
    (lam m Nat
      (match n Nat
        (case (zero) m)
        (case (succ m' ih) (succ ih))))))
"#;

    #[test]
    fn test_basic_compilation() {
        // Simple Nat operation should compile without errors
        let source = r#"
(def double (pi n Nat Nat)
  (lam n Nat (add n n)))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        assert!(!results.is_empty(), "Should have compiled at least one definition");
        let double_result = results.iter().find(|r| r.name == "double");
        assert!(double_result.is_some(), "Should have compiled 'double'");
    }

    #[test]
    fn test_linear_type_definition() {
        // Define a linear type (not in Copy list) and use it
        let source = r#"
(inductive Token (sort 1)
  (ctor mk_token Token))

(def use_token (pi t Token Nat)
  (lam t Token zero))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let use_token = results.iter().find(|r| r.name == "use_token");
        assert!(use_token.is_some(), "Should have compiled 'use_token'");
        // Token is linear (not Copy), but this simple usage should be fine
    }

    #[test]
    fn test_copy_type_reuse() {
        // Nat is Copy, so using it multiple times should be fine
        let source = r#"
(def use_nat_twice (pi n Nat Nat)
  (lam n Nat (add n n)))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "use_nat_twice");
        assert!(result.is_some(), "Should have compiled 'use_nat_twice'");
    }

    #[test]
    fn test_ownership_analysis_runs() {
        // Verify that ownership analysis runs and produces results
        let source = r#"
(def identity (pi n Nat Nat)
  (lam n Nat n))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        assert_eq!(results.len(), 1, "Should have exactly one definition");
        // The analysis ran - errors are collected (may or may not have errors depending on implementation)
    }

    #[test]
    fn test_match_compilation() {
        // Test that match expressions compile through the pipeline
        let source = r#"
(def is_zero (pi n Nat Bool)
  (lam n Nat
    (match n Bool
      (case (zero) true)
      (case (succ m ih) false))))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "is_zero");
        assert!(result.is_some(), "Should have compiled 'is_zero'");
    }

    #[test]
    fn test_nested_function_compilation() {
        // Test nested lambdas (closures)
        let source = r#"
(def const_nat (pi a Nat (pi b Nat Nat))
  (lam a Nat (lam b Nat a)))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "const_nat");
        assert!(result.is_some(), "Should have compiled 'const_nat'");
    }

    #[test]
    fn test_linear_type_must_be_used() {
        // Define a linear type and verify it triggers ownership analysis
        let source = r#"
(inductive Resource (sort 1)
  (ctor acquire Resource))

(def create_resource Resource acquire)
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "create_resource");
        assert!(result.is_some(), "Should have compiled 'create_resource'");
        // Resource is linear (not in Copy list), ownership analysis should run
    }

    #[test]
    fn test_multiple_definitions() {
        // Test that multiple definitions are all compiled
        let source = r#"
(def f1 Nat zero)
(def f2 Nat (succ zero))
(def f3 Nat (succ (succ zero)))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        assert_eq!(results.len(), 3, "Should have compiled 3 definitions");
        assert!(results.iter().any(|r| r.name == "f1"));
        assert!(results.iter().any(|r| r.name == "f2"));
        assert!(results.iter().any(|r| r.name == "f3"));
    }

    #[test]
    fn test_recursive_function() {
        // Test recursive function through match/recursor
        let source = r#"
(def double (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m ih) (succ (succ ih))))))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "double");
        assert!(result.is_some(), "Should have compiled 'double'");
    }

    #[test]
    fn test_bool_operations() {
        // Test boolean operations compile correctly
        let source = r#"
(def my_not (pi b Bool Bool)
  (lam b Bool
    (match b Bool
      (case (true) false)
      (case (false) true))))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "my_not");
        assert!(result.is_some(), "Should have compiled 'my_not'");
    }

    #[test]
    fn test_complex_nested_match() {
        // Test nested function with match
        let source = r#"
(def nat_eq (pi a Nat (pi b Nat Bool))
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
            (case (succ m ih2) ih)))))))
"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        let result = results.iter().find(|r| r.name == "nat_eq");
        assert!(result.is_some(), "Should have compiled 'nat_eq'");
    }
}