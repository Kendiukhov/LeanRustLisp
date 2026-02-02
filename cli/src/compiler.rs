use kernel::checker::Env;
use kernel::ast::{Term, InductiveDecl, Transparency};
use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use frontend::elaborator::{Elaborator, ElabError};
use frontend::declaration_parser::DeclarationParser;
use frontend::surface::{Declaration, Span};
use frontend::diagnostics::{Diagnostic, Level, DiagnosticCollector, DiagnosticHandler};
use mir::codegen::{codegen_recursors, sanitize_name, codegen_constant};
use mir::Literal;

use std::fs;
use std::path::Path;
use std::rc::Rc;
use ariadne::{Report, ReportKind, Label, Source, Color};

pub fn compile_file(path: &str, output_path: Option<String>) {
    compile_with_mir(path, output_path);
}

// Deprecated alias
pub fn compile_file_to_mir(path: &str) {
    compile_with_mir(path, None);
}

// Deprecated alias
pub fn compile_file_to_mir_with_output(path: &str, output_path: Option<String>) {
    compile_with_mir(path, output_path);
}

fn compile_with_mir(path: &str, output_path: Option<String>) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let prelude_path = "stdlib/prelude.lrl";

    let mut all_code = String::new();
    let mut main_def_name: Option<String> = None;
    let mut diagnostics = DiagnosticCollector::new();

    // Add prelude
    all_code.push_str("#![allow(dead_code, unused_variables, unused_parens, unreachable_patterns)]\n");
    all_code.push_str(&mir::codegen::codegen_prelude());
    all_code.push_str("\n");

    let mut closure_idx = 0usize;

    // Helper to print diagnostics
    let print_diagnostics = |diagnostics: &DiagnosticCollector, filename: &str, content: &str| {
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
    };

    // Load Prelude
    if Path::new(prelude_path).exists() {
         if let Ok(content) = fs::read_to_string(prelude_path) {
             let options = crate::driver::PipelineOptions::default();
             let _ = crate::driver::process_code(&content, prelude_path, &mut env, &mut expander, &options, &mut diagnostics);
             if diagnostics.has_errors() {
                 print_diagnostics(&diagnostics, prelude_path, &content);
                 println!("Prelude compilation failed.");
                 return;
             }
         }
    }
    
    // Load Main File
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            println!("Error reading file: {} ({:?})", path, e);
            return;
        }
    };

    let options = crate::driver::PipelineOptions::default();
    let result = match crate::driver::process_code(&content, path, &mut env, &mut expander, &options, &mut diagnostics) {
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

    // Codegen Phase
    let mut names: Vec<_> = env.definitions().keys().cloned().collect();
    names.sort(); 
    
    // Inductives
    let mut ind_names: Vec<_> = env.inductives.keys().cloned().collect();
    ind_names.sort();
    
    for name in ind_names {
        if let Some(decl) = env.inductives.get(&name) {
             let ctors = &decl.ctors;
             for (i, ctor) in ctors.iter().enumerate() {
                  let safe_ctor_name = sanitize_name(&ctor.name);
                   let mut arity = 0;
                    let mut t = &ctor.ty;
                    while let kernel::ast::Term::Pi(_, b, _) = &**t { arity += 1; t = b; }
                    
                    let ctor_val_code = codegen_constant(&Literal::InductiveCtor(name.clone(), i, arity));
                    all_code.push_str(&format!("fn {}() -> Value {{ {} }}\n", safe_ctor_name, ctor_val_code));
             }
        }
    }

    // Definitions
    for name in names {
        if let Some(def) = env.definitions().get(&name) {
            // Skip if it's a constructor (Term::Ctor)
            if let Some(val) = &def.value {
                 if let kernel::ast::Term::Ctor(_, _, _) = &**val {
                    continue;
                 }
            } else if def.totality == kernel::ast::Totality::Axiom {
                 let safe_name = sanitize_name(&name);
                 all_code.push_str(&format!("fn {}() -> Value {{ panic!(\"Axiom accessed: {}\") }}\n", safe_name, name));
                 continue;
            } else {
                continue; // Should not happen for definitions without value unless axiom
            }

            // Lower to MIR
             let mut ctx = mir::lower::LoweringContext::new(vec![], def.ty.clone(), &env);
             let dest = mir::Place::from(mir::Local(0));
             let target = mir::BasicBlock(1);
             ctx.body.basic_blocks.push(mir::BasicBlockData {
                 statements: vec![],
                 terminator: Some(mir::Terminator::Return)
             });

             if let Some(val) = &def.value {
                 if let Err(e) = ctx.lower_term(val, dest, target) {
                     diagnostics.handle(Diagnostic::error(format!("Lowering error in {}: {}", name, e)));
                     continue;
                 }
             }

            // Safety Checks
            let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
            ownership.analyze();
            for e in ownership.check() {
                diagnostics.handle(Diagnostic::error(format!("Ownership error in {}: {}", name, e)));
            }

            let mut nll = mir::analysis::nll::NllChecker::new(&ctx.body);
            nll.check();
            let nll_result = nll.into_result();
            for e in &nll_result.errors {
                diagnostics.handle(Diagnostic::error(format!("Borrow error: {}", e)));
            }
            if nll_result.is_ok() {
                nll_result.inject_runtime_checks(&mut ctx.body);
            }

            let mut linter = mir::lints::PanicFreeLinter::new(&ctx.body);
            linter.check();
            for e in linter.errors {
                diagnostics.handle(Diagnostic::error(format!("Lint error in {}: {}", name, e)));
            }
            
             for (i, body) in ctx.derived_bodies.borrow_mut().iter_mut().enumerate() {
                 let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(body);
                 ownership.analyze();
                 for e in ownership.check() {
                     diagnostics.handle(Diagnostic::error(format!("Ownership error in {} closure {}: {}", name, i, e)));
                 }
                 let mut nll = mir::analysis::nll::NllChecker::new(body);
                 nll.check();
                 let nll_result = nll.into_result();
                 for e in &nll_result.errors {
                     diagnostics.handle(Diagnostic::error(format!("Borrow error in {} closure {}: {}", name, i, e)));
                 }
                 if nll_result.is_ok() {
                     nll_result.inject_runtime_checks(body);
                 }
                 let mut linter = mir::lints::PanicFreeLinter::new(body);
                 linter.check();
                 for e in linter.errors {
                     diagnostics.handle(Diagnostic::error(format!("Lint error in {} closure {}: {}", name, i, e)));
                 }
            }

            if diagnostics.has_errors() {
                 continue;
            }
            
            // Optimizations
            mir::transform::erasure::erase_proofs(&mut ctx.body);
            for body in ctx.derived_bodies.borrow_mut().iter_mut() { mir::transform::erasure::erase_proofs(body); }
            mir::transform::dce::eliminate_dead_code(&mut ctx.body);
            for body in ctx.derived_bodies.borrow_mut().iter_mut() { mir::transform::dce::eliminate_dead_code(body); }
            mir::transform::dce::simplify_cfg(&mut ctx.body);
            for body in ctx.derived_bodies.borrow_mut().iter_mut() { mir::transform::dce::simplify_cfg(body); }
            mir::transform::inline::optimize(&mut ctx.body);
            for body in ctx.derived_bodies.borrow_mut().iter_mut() { mir::transform::inline::optimize(body); }

            // CodeGen
            for (i, body) in ctx.derived_bodies.borrow().iter().enumerate() {
                 let closure_name = format!("closure_{}", closure_idx + i);
                 all_code.push_str(&mir::codegen::codegen_body(&closure_name, body));
                 all_code.push_str("\n");
            }
            closure_idx += ctx.derived_bodies.borrow().len();

            let safe_name = sanitize_name(&name);
            all_code.push_str(&mir::codegen::codegen_body(&safe_name, &ctx.body));
            all_code.push_str("\n");
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

    all_code.push_str(&codegen_recursors(&env.inductives, &env));

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
    let source_file = format!("{}/output.rs", build_dir);
    let binary_file = output_path.unwrap_or_else(|| "output".to_string());

    if let Err(e) = fs::write(&source_file, &all_code) {
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

/// Result of compiling a definition, for testing purposes
#[derive(Debug, Clone)]
pub struct DefCompileResult {
    pub name: String,
    pub ownership_errors: Vec<String>,
    pub borrow_errors: Vec<String>,
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
    let mut diagnostics = DiagnosticCollector::new();

    // Load prelude
    let prelude_content = if let Some(p) = prelude {
        Some(p.to_string())
    } else {
        None 
    };

    if let Some(content) = prelude_content {
        let options = crate::driver::PipelineOptions::default();
        let _ = crate::driver::process_code(&content, "prelude", &mut env, &mut expander, &options, &mut diagnostics);
    }

    let options = crate::driver::PipelineOptions::default();
    let proc_result = crate::driver::process_code(source, "test", &mut env, &mut expander, &options, &mut diagnostics);
    
    if let Ok(res) = proc_result {
        for name in res.deployed_definitions {
            let mut ownership_errors = Vec::new();
            let mut borrow_errors = Vec::new();
            
            if let Some(def) = env.definitions().get(&name) {
                 if let Some(val) = &def.value {
                     if let kernel::ast::Term::Ctor(_, _, _) = &**val {
                         continue;
                     }
                     // Lower and Check
                     let mut ctx = mir::lower::LoweringContext::new(vec![], def.ty.clone(), &env);
                     let dest = mir::Place::from(mir::Local(0));
                     let target = mir::BasicBlock(1);
                     ctx.body.basic_blocks.push(mir::BasicBlockData {
                         statements: vec![],
                         terminator: Some(mir::Terminator::Return)
                     });
                     if let Err(e) = ctx.lower_term(val, dest, target) {
                         borrow_errors.push(format!("Lowering error in {}: {}", name, e));
                         results.push(DefCompileResult {
                             name,
                             ownership_errors,
                             borrow_errors,
                         });
                         continue;
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

    #[test]
    fn test_basic_compilation() {
        let source = r#"(
def double (pi n Nat Nat)
  (lam n Nat (add n n)))"#;
        let results = compile_string_with_prelude(source, Some(TEST_PRELUDE));
        assert!(!results.is_empty(), "Should have compiled at least one definition");
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
}
