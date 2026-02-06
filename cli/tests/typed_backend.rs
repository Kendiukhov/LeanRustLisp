use cli::driver::{module_id_for_source, process_code, PipelineOptions};
use cli::set_prelude_macro_boundary_allowlist;
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::ast::Term;
use kernel::checker::Env;
use mir::codegen::{
    codegen_body, codegen_constant, codegen_prelude, codegen_recursors, sanitize_name,
};
use mir::typed_codegen::{codegen_program, TypedBody, TypedProgram};
use mir::types::{AdtId, CtorId, IdRegistry};
use mir::Literal;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Clone)]
struct LoweredDef {
    name: String,
    body: mir::Body,
    derived_bodies: Vec<mir::Body>,
}

fn lower_program(
    source: &str,
    load_prelude: bool,
    check_closure_bodies: bool,
) -> (Env, IdRegistry, Vec<LoweredDef>, Option<String>) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    env.set_allow_reserved_primitives(true);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    if load_prelude {
        let prelude_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../stdlib/prelude.lrl");
        let prelude = fs::read_to_string(&prelude_path)
            .unwrap_or_else(|e| panic!("failed to read prelude {:?}: {}", prelude_path, e));
        let prelude_module = module_id_for_source("stdlib/prelude.lrl");
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
        let mut prelude_diagnostics = DiagnosticCollector::new();
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        process_code(
            &prelude,
            "prelude",
            &mut env,
            &mut expander,
            &PipelineOptions::default(),
            &mut prelude_diagnostics,
        )
        .expect("prelude processing failed");
        expander.clear_macro_boundary_allowlist();
        env.set_allow_reserved_primitives(allow_reserved);
        if let Err(err) = env.init_marker_registry() {
            panic!("Failed to initialize marker registry: {}", err);
        }
        expander.set_default_imports(vec![prelude_module]);
        assert!(
            !prelude_diagnostics.has_errors(),
            "prelude diagnostics contained errors"
        );
    }

    let result = process_code(
        source,
        "typed_backend_test",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    )
    .expect("process_code failed");

    assert!(
        !diagnostics.has_errors(),
        "diagnostics contained errors: {:?}",
        diagnostics.diagnostics
    );

    let ids = IdRegistry::from_env(&env);
    let mut names: Vec<_> = env.definitions().keys().cloned().collect();
    names.sort();

    let mut lowered_defs = Vec::new();
    for name in names {
        let def = env.definitions().get(&name).expect("missing def");
        if let Some(val) = &def.value {
            if matches!(&**val, Term::Ctor(_, _, _)) {
                continue;
            }
        } else {
            continue;
        }

        let mut ctx = mir::lower::LoweringContext::new_with_metadata(
            vec![],
            def.ty.clone(),
            &env,
            &ids,
            None,
            Some(name.clone()),
            Some(Rc::new(def.capture_modes.clone())),
        );
        let dest = mir::Place::from(mir::Local(0));
        let target = mir::BasicBlock(1);
        ctx.body.basic_blocks.push(mir::BasicBlockData {
            statements: vec![],
            terminator: Some(mir::Terminator::Return),
        });

        if let Some(val) = &def.value {
            ctx.lower_term(val, dest, target)
                .unwrap_or_else(|e| panic!("lowering error in {}: {}", name, e));
        }

        mir::transform::storage::insert_exit_storage_deads(&mut ctx.body);

        let mut typing = mir::analysis::typing::TypingChecker::new(&ctx.body);
        typing.check();
        assert!(
            typing.errors().is_empty(),
            "typing errors in {}: {:?}",
            name,
            typing.errors()
        );

        let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
        ownership.analyze();
        let ownership_errors = ownership.check();
        assert!(
            ownership_errors.is_empty(),
            "ownership errors in {}: {:?}",
            name,
            ownership_errors
        );

        let mut nll = mir::analysis::nll::NllChecker::new(&ctx.body);
        nll.check();
        let nll_result = nll.into_result();
        assert!(
            nll_result.errors.is_empty(),
            "borrow errors in {}: {:?}",
            name,
            nll_result.errors
        );
        if nll_result.is_ok() {
            nll_result.inject_runtime_checks(&mut ctx.body);
        }

        if check_closure_bodies {
            for (i, body) in ctx.derived_bodies.borrow_mut().iter_mut().enumerate() {
                mir::transform::storage::insert_exit_storage_deads(body);

                let mut typing = mir::analysis::typing::TypingChecker::new(body);
                typing.check();
                assert!(
                    typing.errors().is_empty(),
                    "typing errors in {} closure {}: {:?}",
                    name,
                    i,
                    typing.errors()
                );

                let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(body);
                ownership.analyze();
                let ownership_errors = ownership.check();
                assert!(
                    ownership_errors.is_empty(),
                    "ownership errors in {} closure {}: {:?}",
                    name,
                    i,
                    ownership_errors
                );

                let mut nll = mir::analysis::nll::NllChecker::new(body);
                nll.check();
                let nll_result = nll.into_result();
                assert!(
                    nll_result.errors.is_empty(),
                    "borrow errors in {} closure {}: {:?}",
                    name,
                    i,
                    nll_result.errors
                );
                if nll_result.is_ok() {
                    nll_result.inject_runtime_checks(body);
                }
            }
        }

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

        let safe_name = sanitize_name(&name);
        lowered_defs.push(LoweredDef {
            name: safe_name,
            body: ctx.body,
            derived_bodies: ctx.derived_bodies.borrow().clone(),
        });
    }

    let main_name = result
        .deployed_definitions
        .last()
        .map(|name| sanitize_name(name));

    (env, ids, lowered_defs, main_name)
}

fn build_typed_program(defs: &[LoweredDef], main_name: Option<String>) -> TypedProgram {
    let mut typed_defs = Vec::new();
    let mut typed_closures = Vec::new();
    let mut closure_base = 0usize;

    for def in defs {
        typed_defs.push(TypedBody {
            name: def.name.clone(),
            body: def.body.clone(),
            closure_base,
        });
        for (idx, body) in def.derived_bodies.iter().enumerate() {
            typed_closures.push(TypedBody {
                name: format!("closure_{}", closure_base + idx),
                body: body.clone(),
                closure_base,
            });
        }
        closure_base += def.derived_bodies.len();
    }

    TypedProgram {
        defs: typed_defs,
        closures: typed_closures,
        main_name,
    }
}

fn build_dynamic_code(
    env: &Env,
    ids: &IdRegistry,
    defs: &[LoweredDef],
    main_name: Option<String>,
) -> String {
    let mut code = String::new();
    code.push_str("#![allow(dead_code, unused_variables, unused_parens, unreachable_patterns)]\n");
    code.push_str(&codegen_prelude());
    code.push('\n');

    let mut ind_names: Vec<_> = env.inductives.keys().cloned().collect();
    ind_names.sort();
    for name in ind_names {
        if let Some(decl) = env.inductives.get(&name) {
            for (i, ctor) in decl.ctors.iter().enumerate() {
                let safe_ctor_name = sanitize_name(&ctor.name);
                let mut arity = 0;
                let mut ty = &ctor.ty;
                while let Term::Pi(_, body, _, _) = &**ty {
                    arity += 1;
                    ty = body;
                }
                let ctor_id = ids
                    .ctor_id(&name, i)
                    .unwrap_or_else(|| CtorId::new(AdtId::new(&name), i));
                let ctor_val_code = codegen_constant(&Literal::InductiveCtor(ctor_id, arity), 0);
                code.push_str(&format!(
                    "fn {}() -> Value {{ {} }}\n",
                    safe_ctor_name, ctor_val_code
                ));
            }
        }
    }

    let mut closure_idx = 0usize;
    for def in defs {
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
    if let Some(name) = main_name {
        code.push_str(&format!("    let result = {}();\n", name));
        code.push_str("    println!(\"Result: {:?}\", result);\n");
    }
    code.push_str("}\n");

    code
}

fn extract_result_value(output: &str) -> Option<&str> {
    output
        .lines()
        .find_map(|line| line.strip_prefix("Result: "))
        .map(str::trim)
}

fn extract_nat_result(output: &str) -> Option<u64> {
    let value = extract_result_value(output)?;
    if let Some(rest) = value.strip_prefix("Nat(").and_then(|s| s.strip_suffix(')')) {
        rest.parse().ok()
    } else {
        value.parse().ok()
    }
}

fn extract_bool_result(output: &str) -> Option<bool> {
    let value = extract_result_value(output)?;
    if let Some(rest) = value
        .strip_prefix("Bool(")
        .and_then(|s| s.strip_suffix(')'))
    {
        rest.parse().ok()
    } else {
        value.parse().ok()
    }
}

fn compile_and_run(code: &str) -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time went backwards")
        .as_nanos();
    let temp_dir = std::env::temp_dir().join(format!(
        "lrl_typed_backend_{}_{}",
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&temp_dir).expect("failed to create temp dir");
    let src_path = temp_dir.join("main.rs");
    let bin_path = temp_dir.join("main_bin");

    fs::write(&src_path, code).expect("failed to write rust source");
    let status = Command::new("rustc")
        .arg(&src_path)
        .arg("-O")
        .arg("-o")
        .arg(&bin_path)
        .status()
        .expect("failed to invoke rustc");
    assert!(status.success(), "rustc failed for {:?}", src_path);

    let output = Command::new(&bin_path)
        .output()
        .expect("failed to run compiled binary");
    assert!(
        output.status.success(),
        "compiled binary failed: {:?}",
        output
    );

    String::from_utf8_lossy(&output.stdout).to_string()
}

#[test]
fn typed_backend_generates_code_for_simple_program() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive copy Color (sort 1)
          (ctor red Color)
          (ctor rgb (pi r Nat (pi g Nat (pi b Nat Color)))))

        (def id_color (pi c Color Color)
          (lam c Color c))

        (def main Color
          (id_color (rgb (succ zero) zero (succ zero))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, true);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");

    assert!(code.contains("enum Color"), "expected Color enum in output");
    assert!(
        !code.contains("Value::"),
        "typed backend should not emit Value runtime"
    );
    assert!(
        !code.contains("Expected Func"),
        "typed backend should not emit tag-check panics"
    );
}

#[test]
fn typed_backend_codegen_is_deterministic() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive copy Color (sort 1)
          (ctor red Color)
          (ctor rgb (pi r Nat (pi g Nat (pi b Nat Color)))))

        (def id_color (pi c Color Color)
          (lam c Color c))

        (def main Color
          (id_color (rgb (succ zero) zero (succ zero))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, true);
    let program = build_typed_program(&defs, main_name);
    let code1 = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let code2 = codegen_program(&env, &ids, &program).expect("typed codegen failed");

    assert_eq!(code1, code2, "typed backend output is nondeterministic");
}

#[test]
fn typed_backend_rejects_parametric_adts() {
    let source = r#"
        (inductive Box (pi (T (sort 1)) (sort 1))
          (ctor mk_box (pi (T (sort 1)) (pi (x T) (Box T)))))

        (def id_box (pi (T (sort 1)) (pi (b (Box T)) (Box T)))
          (lam T (sort 1) (lam b (Box T) b)))

        (def main (pi (T (sort 1)) (pi (b (Box T)) (Box T)))
          id_box)
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, true);
    let program = build_typed_program(&defs, main_name);
    let err = codegen_program(&env, &ids, &program).expect_err("expected error");
    assert!(
        err.message.contains("parametric ADT"),
        "expected parametric ADT error, got: {}",
        err.message
    );
}

#[test]
fn typed_backend_executes_match_on_nat() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def add (pi n Nat (pi m Nat Nat))
          (lam n Nat
            (lam m Nat
              (match n Nat
                (case (zero) m)
                (case (succ m' ih) (succ ih))))))

        (def entry Nat
          (add (succ zero) (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: 2"),
        "expected output to contain Result: 2, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_match_on_user_inductive() {
    let source = r#"
        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive copy Color (sort 1)
          (ctor red Color)
          (ctor rgb (pi r Bool (pi g Bool (pi b Bool Color)))))

        (def is_red (pi c Color Bool)
          (lam c Color
            (match c Bool
              (case (red) true)
              (case (rgb r g b) false))))

        (def entry Bool
          (is_red red))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: true"),
        "expected output to contain Result: true, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_print_nat() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def print_nat (pi n Nat Nat)
          (lam n Nat n))

        (def entry Nat
          (print_nat (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    let lines: Vec<_> = output.lines().collect();
    assert!(
        lines.iter().any(|line| *line == "1"),
        "expected print output to include a standalone '1', got {:?}",
        lines
    );
    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_nested_projections() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def add (pi n Nat (pi m Nat Nat))
          (lam n Nat
            (lam m Nat
              (match n Nat
                (case (zero) m)
                (case (succ m' ih) (succ ih))))))

        (inductive copy Pair (sort 1)
          (ctor pair (pi a Nat (pi b Nat Pair))))

        (inductive copy Tree (sort 1)
          (ctor leaf (pi p Pair Tree))
          (ctor node (pi left Tree (pi right Tree Tree))))

        (def sum_pair (pi p Pair Nat)
          (lam p Pair
            (match p Nat
              (case (pair a b) (add a b)))))

        (def leaf_sum (pi t Tree Nat)
          (lam t Tree
            (match t Nat
              (case (leaf p) (sum_pair p))
              (case (node l r) zero))))

        (def entry Nat
          (leaf_sum (leaf (pair (succ zero) (succ (succ zero))))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: 3"),
        "expected output to contain Result: 3, got {}",
        output
    );
}

#[test]
fn typed_backend_matches_dynamic_output_for_stage1_program() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def entry Nat
          (succ (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name.clone());
    let typed_code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);

    let typed_output = compile_and_run(&typed_code);
    let dynamic_output = compile_and_run(&dynamic_code);

    let typed_value = extract_nat_result(&typed_output);
    let dynamic_value = extract_nat_result(&dynamic_output);
    assert!(
        typed_value.is_some() && dynamic_value.is_some(),
        "expected nat outputs, got typed: {:?}, dynamic: {:?}",
        typed_output,
        dynamic_output
    );
    assert_eq!(
        typed_value, dynamic_value,
        "typed and dynamic outputs differ: typed {:?}, dynamic {:?}",
        typed_output, dynamic_output
    );
}

#[test]
fn typed_backend_auto_falls_back_to_dynamic_on_parametric_adt() {
    let source = r#"
        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive Box (pi (T (sort 1)) (sort 1))
          (ctor mk_box (pi (T (sort 1)) (pi (x T) (Box T)))))

        (def id_box (pi (T (sort 1)) (pi (b (Box T)) (Box T)))
          (lam T (sort 1) (lam b (Box T) b)))

        (def entry Bool
          true)
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name.clone());
    let err = codegen_program(&env, &ids, &program).expect_err("expected typed backend error");
    assert!(
        err.message.contains("parametric ADT"),
        "expected parametric ADT error, got: {}",
        err.message
    );

    let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);
    assert!(
        dynamic_code.contains("Value::"),
        "expected dynamic backend codegen to use Value runtime"
    );
    let output = compile_and_run(&dynamic_code);
    assert_eq!(
        extract_bool_result(&output),
        Some(true),
        "unexpected dynamic output: {}",
        output
    );
}

#[test]
fn typed_backend_executes_higher_order_apply_twice() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def succ1 (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def apply_twice
          (pi f (pi n Nat Nat)
            (pi n Nat Nat))
          (lam f (pi n Nat Nat)
            (lam n Nat
              (f (f n)))))

        (def entry Nat
          (apply_twice succ1 (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Value::"),
        "typed backend should not emit Value runtime for higher-order subset"
    );
    assert!(
        !code.contains("Expected Func"),
        "typed backend should not emit dynamic function tag checks"
    );
    assert!(
        output.contains("Result: 3"),
        "expected output to contain Result: 3, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_higher_order_returned_closure_capture() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def make_k
          (pi n Nat (pi x Nat Nat))
          (lam n Nat
            (lam x Nat n)))

        (def entry Nat
          ((make_k (succ zero)) zero))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Value::"),
        "typed backend should not emit Value runtime for closure capture subset"
    );
    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_higher_order_match_selects_function() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (def succ1 (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def id_nat (pi n Nat Nat)
          (lam n Nat n))

        (def choose
          (pi b Bool (pi n Nat Nat))
          (lam b Bool
            (match b (pi n Nat Nat)
              (case (true) succ1)
              (case (false) id_nat))))

        (def entry Nat
          ((choose true) (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Expected Func"),
        "typed backend should not emit dynamic function-tag checks in match-selected calls"
    );
    assert!(
        output.contains("Result: 2"),
        "expected output to contain Result: 2, got {}",
        output
    );
}

#[test]
fn typed_backend_matches_dynamic_output_for_higher_order_program() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def succ1 (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def apply_twice
          (pi f (pi n Nat Nat)
            (pi n Nat Nat))
          (lam f (pi n Nat Nat)
            (lam n Nat
              (f (f n)))))

        (def entry Nat
          (apply_twice succ1 (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name.clone());
    let typed_code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);

    let typed_output = compile_and_run(&typed_code);
    assert_eq!(
        extract_nat_result(&typed_output),
        Some(3),
        "unexpected typed backend output for higher-order program: {}",
        typed_output
    );

    let dynamic_output = compile_and_run(&dynamic_code);
    let typed_value = extract_nat_result(&typed_output);
    let dynamic_value = extract_nat_result(&dynamic_output);
    assert_eq!(
        typed_value, dynamic_value,
        "typed and dynamic outputs differ for higher-order program: typed {:?}, dynamic {:?}",
        typed_output, dynamic_output
    );
}
