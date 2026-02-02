use cli::driver::{process_code, Artifact, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::Expander;
use kernel::checker::Env;
use insta::assert_snapshot;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn run_pipeline(source: &str) -> String {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions { collect_artifacts: true, ..Default::default() };

    let result = process_code(source, "pipeline_golden", &mut env, &mut expander, &options, &mut diagnostics)
        .expect("Pipeline should succeed");

    let mut out = String::new();

    if !diagnostics.diagnostics.is_empty() {
        out.push_str("Diagnostics:\n");
        for diag in &diagnostics.diagnostics {
            out.push_str(&format!("- {:?}: {}\n", diag.level, diag.message));
        }
        out.push('\n');
    }

    for artifact in result.artifacts {
        match artifact {
            Artifact::ElaboratedDef { name, ty, val } => {
                out.push_str(&format!("ElaboratedDef {}\n", name));
                out.push_str(&format!("  ty: {}\n", ty));
                out.push_str(&format!("  val: {}\n", val));
            }
            Artifact::MirBody { name, body } => {
                out.push_str(&format!("MirBody {}\n", name));
                out.push_str(&format!("  {}\n", body));
            }
            Artifact::BorrowCheck { name, errors } => {
                out.push_str(&format!("BorrowCheck {}\n", name));
                if errors.is_empty() {
                    out.push_str("  ok\n");
                } else {
                    for err in errors {
                        out.push_str(&format!("  error: {}\n", err));
                    }
                }
            }
            Artifact::AxiomDependencies { name, axioms, classical } => {
                out.push_str(&format!("AxiomDependencies {}\n", name));
                out.push_str(&format!("  axioms: {:?}\n", axioms));
                out.push_str(&format!("  classical: {:?}\n", classical));
            }
        }
        out.push('\n');
    }

    out
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
    assert_eq!(first_hash, second_hash, "Pipeline output hash should be deterministic");
}

#[test]
fn golden_pipeline_classical_axiom_tracking() {
    let source = r#"
        (axiom classical classical_choice (sort 0))
        (axiom postulate (sort 0))

        (def uses_classical (sort 0) classical_choice)
        (def uses_postulate (sort 0) postulate)
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
