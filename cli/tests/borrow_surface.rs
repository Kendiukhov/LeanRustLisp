use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;
use std::fs;
use std::path::Path;

const BORROW_SURFACE_PRELUDE: &str = r#"
    (inductive copy Nat (sort 1)
      (zero Nat)
      (succ (pi n Nat Nat)))

    (axiom Shared (sort 1))
    (axiom Mut (sort 1))
    (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
    (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))
    (axiom borrow_mut (pi {A (sort 1)} (pi x A (Ref #[r] Mut A))))
"#;

fn load_fixture(rel_path: &str) -> String {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cli crate should have a parent directory");
    let fixture_path = repo_root.join(rel_path);
    fs::read_to_string(&fixture_path)
        .unwrap_or_else(|_| panic!("Missing fixture {:?}", fixture_path))
}

fn load_prelude(env: &mut Env, expander: &mut Expander, options: &PipelineOptions) {
    let mut diagnostics = DiagnosticCollector::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
    process_code(
        BORROW_SURFACE_PRELUDE,
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

fn format_diagnostics(diags: &DiagnosticCollector) -> String {
    if diags.diagnostics.is_empty() {
        return "<none>".to_string();
    }
    diags
        .diagnostics
        .iter()
        .map(|d| {
            let code = d.code.unwrap_or("-");
            format!("[{}] {}", code, d.message)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Surface borrow/NLL fixtures.
#[test]
fn borrow_surface_cases() {
    let source = load_fixture("tests/borrow_surface.lrl");

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    load_prelude(&mut env, &mut expander, &options);

    let result = process_code(
        &source,
        "borrow_surface.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(
        result.is_ok(),
        "expected pending borrow surface fixture to parse"
    );
    assert!(
        !diagnostics.has_errors(),
        "expected no diagnostics once borrow surface syntax is implemented"
    );
}

#[test]
fn borrow_surface_rejects_mutation() {
    let source = load_fixture("tests/borrow_surface_negative.lrl");

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    load_prelude(&mut env, &mut expander, &options);

    let result = process_code(
        &source,
        "borrow_surface_negative.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(
        result.is_ok(),
        "expected negative borrow surface fixture to parse"
    );
    assert!(
        diagnostics.has_errors(),
        "expected borrow diagnostics for overlapping shared/mutable borrows"
    );
}

#[test]
fn borrow_edge_cases_accept() {
    let source = load_fixture("tests/borrow_edge_cases.lrl");

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    load_prelude(&mut env, &mut expander, &options);

    let result = process_code(
        &source,
        "borrow_edge_cases.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected borrow edge-case fixture to parse");
    assert!(
        !diagnostics.has_errors(),
        "expected no diagnostics for borrow edge-case fixture\n{}",
        format_diagnostics(&diagnostics)
    );
}

#[test]
fn borrow_edge_cases_reject() {
    let source = load_fixture("tests/borrow_edge_cases_negative.lrl");

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    load_prelude(&mut env, &mut expander, &options);

    let result = process_code(
        &source,
        "borrow_edge_cases_negative.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(
        result.is_ok(),
        "expected negative borrow edge-case fixture to parse"
    );
    assert!(
        diagnostics.has_errors(),
        "expected diagnostics for borrow edge-case conflicts"
    );
}

#[test]
fn borrow_surface_rejects_closure_violation() {
    let source = r#"
    (def use_shared (pi r (Ref Shared Nat) Nat)
      (lam r (Ref Shared Nat) zero))

    (def bad (pi x Nat Nat)
      (lam x Nat
        (let r (Ref Shared Nat) (& x)
          (let f (pi y Nat Nat)
            (lam y Nat
              (let m (Ref Mut Nat) (&mut x)
                (use_shared r)))
            (f zero)))))
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    load_prelude(&mut env, &mut expander, &options);

    let result = process_code(
        source,
        "borrow_surface_closure_violation.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected source to parse");
    assert!(
        diagnostics.has_errors(),
        "expected borrow diagnostics for closure-based violation"
    );
}
