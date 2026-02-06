use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;
const LIFETIME_PRELUDE: &str = r#"
    (inductive copy Nat (sort 1)
      (zero Nat)
      (succ (pi n Nat Nat)))

    (axiom Shared (sort 1))
    (axiom Mut (sort 1))
    (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
"#;

fn load_prelude(env: &mut Env, expander: &mut Expander, options: &PipelineOptions) {
    let mut diagnostics = DiagnosticCollector::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
    process_code(
        LIFETIME_PRELUDE,
        "prelude",
        env,
        expander,
        options,
        &mut diagnostics,
    )
    .expect("prelude processing failed");
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    env.set_allow_reserved_primitives(allow_reserved);
    assert!(
        !diagnostics.has_errors(),
        "prelude diagnostics contained errors"
    );
}

fn run_pipeline_with_prelude(source: &str) -> DiagnosticCollector {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let options = PipelineOptions::default();
    load_prelude(&mut env, &mut expander, &options);

    let mut diagnostics = DiagnosticCollector::new();
    let result = process_code(
        source,
        "lifetime_labels",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected pipeline to return Ok");
    diagnostics
}

#[test]
fn lifetime_labels_allow_distinct_returns() {
    let source = r#"
(noncomputable choose_left
  (pi a (Ref #[a] Shared Nat)
    (pi b (Ref #[b] Shared Nat)
      (Ref #[a] Shared Nat)))
  (lam a (Ref #[a] Shared Nat)
    (lam b (Ref #[b] Shared Nat) a)))
"#;

    let diagnostics = run_pipeline_with_prelude(source);
    assert!(
        !diagnostics.has_errors(),
        "expected no diagnostics for labeled lifetimes"
    );
}

#[test]
fn lifetime_elision_single_input_ok() {
    let source = r#"
(noncomputable id_ref
  (pi a (Ref Shared Nat) (Ref Shared Nat))
  (lam a (Ref Shared Nat) a))
"#;

    let diagnostics = run_pipeline_with_prelude(source);
    assert!(
        !diagnostics.has_errors(),
        "expected elided return lifetime to be accepted"
    );
}

#[test]
fn lifetime_elision_unifies_with_explicit_label() {
    let source = r#"
(noncomputable take_explicit
  (pi r (Ref #[a] Shared Nat) Nat)
  (lam r (Ref #[a] Shared Nat) zero))

(noncomputable call_with_elided
  (pi r (Ref Shared Nat) Nat)
  (lam r (Ref Shared Nat)
    (take_explicit r)))
"#;

    let diagnostics = run_pipeline_with_prelude(source);
    assert!(
        !diagnostics.has_errors(),
        "expected elided Ref to unify with explicit label"
    );
}

#[test]
fn lifetime_elision_rejects_ambiguous_return() {
    let source = r#"
(noncomputable ambiguous
  (pi a (Ref Shared Nat)
    (pi b (Ref Shared Nat)
      (Ref Shared Nat)))
  (lam a (Ref Shared Nat)
    (lam b (Ref Shared Nat) a)))
"#;

    let diagnostics = run_pipeline_with_prelude(source);
    assert!(
        diagnostics.has_errors(),
        "expected diagnostics for ambiguity"
    );
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|diag| diag.message.contains("Ambiguous lifetime in return type")),
        "expected ambiguous lifetime diagnostic, got {:?}",
        diagnostics.diagnostics
    );
}
