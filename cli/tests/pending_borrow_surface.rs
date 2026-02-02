use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::Expander;
use kernel::checker::Env;
use std::fs;

/// Pending surface borrow/NLL fixtures. Enable when ref/borrow syntax lands.
#[test]
#[ignore]
fn pending_surface_borrow_cases() {
    let source = fs::read_to_string("tests/pending/borrow_surface.lrl")
        .expect("pending borrow surface fixture missing");

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let result = process_code(
        &source,
        "pending_borrow_surface.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected pending borrow surface fixture to parse");
    assert!(
        !diagnostics.has_errors(),
        "expected no diagnostics once borrow surface syntax is implemented"
    );
}
