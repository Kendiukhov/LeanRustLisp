use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::Expander;
use kernel::checker::Env;

const MARKER_DEFS: &str = r#"
    (axiom unsafe interior_mutable Type)
    (axiom unsafe may_panic_on_borrow_violation Type)
    (axiom unsafe concurrency_primitive Type)
    (axiom unsafe atomic_primitive Type)
    (axiom unsafe indexable Type)
"#;

const REFCELL_INDUCTIVE: &str = r#"
    (inductive (interior_mutable may_panic_on_borrow_violation) RefCell (pi T Type Type)
      (ctor mk_refcell (pi {T Type} (pi x T (RefCell T))))
    )
"#;

const INTERIOR_ONLY_INDUCTIVE: &str = r#"
    (inductive (interior_mutable) Cell Type
      (mk_cell Cell)
    )
"#;

const CONFLICTING_MARKERS_INDUCTIVE: &str = r#"
    (inductive (may_panic_on_borrow_violation atomic_primitive) BadCell Type
      (mk_bad_cell BadCell)
    )
"#;

fn load_marker_defs(env: &mut Env, expander: &mut Expander) {
    let options = PipelineOptions::default();
    let mut diagnostics = DiagnosticCollector::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let result = process_code(
        MARKER_DEFS,
        "marker_prelude",
        env,
        expander,
        &options,
        &mut diagnostics,
    );
    env.set_allow_reserved_primitives(allow_reserved);
    assert!(result.is_ok(), "Expected marker definitions to parse");
    assert!(
        !diagnostics.has_errors(),
        "Marker definitions should not emit errors"
    );
    env.init_marker_registry()
        .expect("Failed to init marker registry");
}

#[test]
fn marker_resolution_requires_marker_defs() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let result = process_code(
        REFCELL_INDUCTIVE,
        "marker_missing",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "Expected process_code to return Ok");
    assert!(
        diagnostics.has_errors(),
        "Expected diagnostics for missing marker definitions"
    );
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.message.contains("Unknown type marker")),
        "Expected unknown type marker diagnostic"
    );
}

#[test]
fn marker_resolution_accepts_marker_defs() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let options = PipelineOptions::default();
    load_marker_defs(&mut env, &mut expander);

    let mut diagnostics = DiagnosticCollector::new();
    let result = process_code(
        REFCELL_INDUCTIVE,
        "marker_ok",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "Expected process_code to return Ok");
    assert!(
        !diagnostics.has_errors(),
        "Expected no diagnostics when marker definitions are present"
    );
}

#[test]
fn marker_resolution_rejects_interior_mutable_without_kind() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let options = PipelineOptions::default();
    load_marker_defs(&mut env, &mut expander);

    let mut diagnostics = DiagnosticCollector::new();
    let result = process_code(
        INTERIOR_ONLY_INDUCTIVE,
        "marker_interior_only",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "Expected process_code to return Ok");
    assert!(
        diagnostics.has_errors(),
        "Expected diagnostics for missing interior mutability kind"
    );
    assert!(
        diagnostics.diagnostics.iter().any(|d| d
            .message
            .contains("Interior mutability marker requires one of")),
        "Expected missing interior mutability kind diagnostic"
    );
}

#[test]
fn marker_resolution_rejects_conflicting_markers() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let options = PipelineOptions::default();
    load_marker_defs(&mut env, &mut expander);

    let mut diagnostics = DiagnosticCollector::new();
    let result = process_code(
        CONFLICTING_MARKERS_INDUCTIVE,
        "marker_conflict",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "Expected process_code to return Ok");
    assert!(
        diagnostics.has_errors(),
        "Expected diagnostics for conflicting markers"
    );
    assert!(
        diagnostics.diagnostics.iter().any(|d| d
            .message
            .contains("Conflicting interior mutability markers")),
        "Expected conflicting marker diagnostic"
    );
}
