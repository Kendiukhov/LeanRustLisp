use cli::driver::{process_code, Artifact, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use insta::assert_snapshot;
use kernel::checker::Env;
use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::PathBuf;

fn run_pipeline_inner(
    source: &str,
    load_prelude: bool,
    macro_boundary_policy: MacroBoundaryPolicy,
    allow_axioms: bool,
) -> String {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(macro_boundary_policy);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions {
        collect_artifacts: true,
        prelude_frozen: load_prelude,
        allow_redefine: false,
        allow_axioms,
        ..Default::default()
    };

    if load_prelude {
        let prelude_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../stdlib/prelude.lrl");
        let prelude = fs::read_to_string(&prelude_path)
            .unwrap_or_else(|e| panic!("failed to read prelude {:?}: {}", prelude_path, e));
        let mut prelude_diagnostics = DiagnosticCollector::new();
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
        process_code(
            &prelude,
            "prelude",
            &mut env,
            &mut expander,
            &PipelineOptions::default(),
            &mut prelude_diagnostics,
        )
        .expect("prelude processing failed");
        env.set_allow_reserved_primitives(allow_reserved);
        expander.set_macro_boundary_policy(macro_boundary_policy);
        assert!(
            !prelude_diagnostics.has_errors(),
            "prelude diagnostics contained errors"
        );
    }

    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let result = process_code(
        source,
        "pipeline_golden",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    )
    .expect("Pipeline should succeed");
    env.set_allow_reserved_primitives(allow_reserved);

    let mut out = String::new();

    if !diagnostics.diagnostics.is_empty() {
        out.push_str("Diagnostics:\n");
        for diag in &diagnostics.diagnostics {
            out.push_str(&format!(
                "- {:?}: {}\n",
                diag.level,
                diag.message_with_code()
            ));
        }
        out.push('\n');
    }

    for artifact in result.artifacts {
        match artifact {
            Artifact::DefEqConfig {
                fuel,
                source,
                transparency,
            } => {
                out.push_str("DefEqConfig\n");
                out.push_str(&format!("  fuel: {}\n", fuel));
                out.push_str(&format!("  source: {}\n", source));
                out.push_str(&format!("  transparency: {:?}\n", transparency));
            }
            Artifact::ElaboratedDef { name, ty, val } => {
                out.push_str(&format!("ElaboratedDef {}\n", name));
                out.push_str(&format!("  ty: {}\n", ty));
                out.push_str(&format!("  val: {}\n", val));
            }
            Artifact::MirBody { name, body } => {
                out.push_str(&format!("MirBody {}\n", name));
                out.push_str(&format!("  {}\n", body));
            }
            Artifact::BorrowCheck {
                name,
                ownership_errors,
                result,
            } => {
                out.push_str(&format!("BorrowCheck {}\n", name));
                if ownership_errors.is_empty() && result.errors.is_empty() {
                    out.push_str("  ok\n");
                } else {
                    for err in ownership_errors {
                        out.push_str(&format!("  ownership error: {}\n", err));
                    }
                    for err in &result.errors {
                        out.push_str(&format!("  borrow error: {}\n", err));
                    }
                }
                out.push_str("  evidence:\n");
                for line in result.evidence().render_lines() {
                    out.push_str(&format!("    {}\n", line));
                }
            }
            Artifact::AxiomDependencies {
                name,
                axioms,
                classical,
            } => {
                out.push_str(&format!("AxiomDependencies {}\n", name));
                out.push_str(&format!("  axioms: {:?}\n", axioms));
                out.push_str(&format!("  classical: {:?}\n", classical));
            }
        }
        out.push('\n');
    }

    out
}

fn run_pipeline(source: &str) -> String {
    run_pipeline_inner(source, false, MacroBoundaryPolicy::Deny, false)
}

fn run_pipeline_with_prelude(source: &str) -> String {
    run_pipeline_inner(source, true, MacroBoundaryPolicy::Deny, false)
}

fn run_pipeline_with_macro_boundary_warn(source: &str) -> String {
    run_pipeline_inner(source, false, MacroBoundaryPolicy::Warn, false)
}

fn run_pipeline_with_allow_axioms(source: &str) -> String {
    run_pipeline_inner(source, false, MacroBoundaryPolicy::Deny, true)
}

fn hash_output(output: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    output.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn golden_pipeline_semantics() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def id (pi A Type (pi x A A))
          (lam A Type (lam x A x)))

        (def one Nat (succ zero))

        (def add_one (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def match_nat (pi n Nat Nat)
          (lam n Nat
            (match n Nat
              (case (zero) zero)
              (case (succ k) (succ k)))))
    "#;

    let output = run_pipeline(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_determinism() {
    let source = r#"
        (inductive copy Bool Type
          (true Bool)
          (false Bool))

        (def not (pi b Bool Bool)
          (lam b Bool
            (match b Bool
              (case (true) false)
              (case (false) true))))
    "#;

    let first = run_pipeline(source);
    let second = run_pipeline(source);
    assert_eq!(first, second, "Pipeline artifacts should be deterministic");
}

#[test]
fn golden_pipeline_determinism_hash() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def add (pi n Nat (pi m Nat Nat))
          (lam n Nat
            (lam m Nat
              (match n Nat
                (case (zero) m)
                (case (succ k ih) (succ ih))))))

        (def two Nat (succ (succ zero)))
        (def four Nat (add two two))
    "#;

    let first = run_pipeline(source);
    let second = run_pipeline(source);
    let first_hash = hash_output(&first);
    let second_hash = hash_output(&second);
    assert_eq!(
        first_hash, second_hash,
        "Pipeline output hash should be deterministic"
    );
}

#[test]
fn golden_pipeline_classical_axiom_tracking() {
    let source = r#"
        (axiom classical classical_choice (sort 0))
        (axiom postulate (sort 0))

        (noncomputable uses_classical (sort 0) classical_choice)
        (noncomputable uses_postulate (sort 0) postulate)
    "#;

    let output = run_pipeline(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_unsafe_axiom_tracking() {
    let source = r#"
        (axiom unsafe UnsafeAx (pi x (sort 0) (sort 0)))
        (unsafe uses_unsafe (pi x (sort 0) (sort 0)) UnsafeAx)
    "#;

    let output = run_pipeline(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_interior_mutability_allow_axioms() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive Foo Type
          (ctor mk_foo Foo))

        (inductive (interior_mutable may_panic_on_borrow_violation) RefCell (pi T Type Type)
          (ctor mk_refcell (pi {T Type} (pi x T (RefCell T)))))

        (noncomputable uses_refcell (pi x (RefCell Foo) Foo)
          (lam x (RefCell Foo) mk_foo))
    "#;

    let output = run_pipeline_with_allow_axioms(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_macro_boundary_warnings() {
    let source = r#"
        (defmacro mk_unsafe (name ty val) (unsafe name ty val))
        (defmacro mk_classical (name ty) (axiom classical name ty))
        (defmacro mk_axiom (name ty) (axiom name ty))
        (defmacro mk_import_classical () (import classical))

        (mk_unsafe Foo (sort 1) (sort 0))
        (mk_classical choice (sort 0))
        (mk_axiom postulate (sort 0))
        (mk_import_classical)
    "#;

    let output = run_pipeline_with_macro_boundary_warn(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_fnonce_coercion() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def apply_once
          (pi f (pi #[once] x Nat Nat) (pi #[once] v Nat Nat))
          (lam f (pi #[once] x Nat Nat)
            (lam v Nat (f v))))

        (def add_one (pi #[fn] x Nat Nat)
          (lam x Nat (succ x)))

        (def test_coercion Nat (apply_once add_one zero))
    "#;

    let output = run_pipeline(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_indexed_recursor() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive Vec (pi A (sort 1) (pi n Nat (sort 1)))
          (ctor nil (pi A (sort 1) (Vec A zero)))
          (ctor cons (pi A (sort 1) (pi n Nat (pi h A (pi t (Vec A n) (Vec A (succ n))))))))

        (def vlen (pi A (sort 1) (pi n Nat (pi v (Vec A n) Nat)))
          (lam A (sort 1)
            (lam n Nat
              (lam v (Vec A n)
                (match v Nat
                  (case (nil) zero)
                  (case (cons n h t ih) (succ ih)))))))
    "#;

    let output = run_pipeline(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_borrow_regions() {
    let source = r#"
        (unsafe borrow_twice (pi x Nat Nat)
          (lam x Nat
            (let r1 (Ref #[r] Shared Nat) (& x)
              (let r2 (Ref #[r] Shared Nat) (& x)
                zero))))
    "#;

    let output = run_pipeline_with_prelude(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_borrow_shared_total() {
    let source = r#"
        (def borrow_shared_total (pi x Nat Nat)
          (lam x Nat
            (let r (Ref #[r] Shared Nat) (& x)
              x)))
    "#;

    let output = run_pipeline_with_prelude(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_id_ref_shared_lifetimes() {
    let source = r#"
        (noncomputable use_shared (pi r (Ref #[r] Shared Nat) Nat)
          (lam r (Ref #[r] Shared Nat) zero))

        (noncomputable use_mut (pi r (Ref #[r] Mut Nat) Nat)
          (lam r (Ref #[r] Mut Nat) zero))

        (noncomputable id_ref (pi r (Ref #[r] Shared Nat) (Ref #[r] Shared Nat))
          (lam r (Ref #[r] Shared Nat) r))

        (noncomputable safe_id_ref (pi x Nat (pi y Nat Nat))
          (lam x Nat
            (lam y Nat
              (let tmp Nat
                (let r1 (Ref #[r] Shared Nat) (& x)
                  (let s1 (Ref #[r] Shared Nat) (id_ref r1)
                    (use_shared s1)))
                (let r2 (Ref #[r] Shared Nat) (& y)
                  (let s2 (Ref #[r] Shared Nat) (id_ref r2)
                    (let m (Ref #[r] Mut Nat) (&mut x)
                      (let tmp2 Nat (use_mut m)
                        (use_shared s2)))))))))
    "#;

    let output = run_pipeline_with_prelude(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_mixed_capture_fnmut() {
    let source = r#"
        (noncomputable use_mut (pi r (Ref #[r] Mut Nat) Nat)
          (lam r (Ref #[r] Mut Nat) zero))

        (noncomputable mixed_capture_fnmut (pi x Nat Nat)
          (lam x Nat
            (let r (Ref #[r] Mut Nat) (&mut x)
              (let g (pi y Nat Nat) (lam y Nat y)
                (let f (pi #[mut] _ Nat Nat)
                  (lam #[mut] _ Nat
                    (let tmp Nat (use_mut r)
                      (g zero)))
                  (let tmp2 Nat (g zero)
                    (f zero)))))))
    "#;

    let output = run_pipeline_with_prelude(source);
    assert_snapshot!(output);
}

#[test]
fn golden_pipeline_repeated_fn_calls() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def use_fn_twice (pi x Nat Nat)
          (lam x Nat
            (let f (pi y Nat Nat) (lam y Nat y)
              (let tmp Nat (f x)
                (f x)))))

        (def use_fnmut_twice (pi x Nat Nat)
          (lam x Nat
            (let f (pi #[mut] y Nat Nat) (lam #[mut] y Nat y)
              (let tmp Nat (f x)
                (f x)))))
    "#;

    let output = run_pipeline(source);
    assert_snapshot!(output);
}
