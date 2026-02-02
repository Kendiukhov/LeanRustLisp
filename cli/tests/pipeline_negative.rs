use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::Expander;
use kernel::checker::Env;
use insta::assert_snapshot;

fn run_pipeline(source: &str) -> (String, bool, bool) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions { collect_artifacts: false, ..Default::default() };

    let result = process_code(source, "pipeline_negative", &mut env, &mut expander, &options, &mut diagnostics);

    let mut out = String::new();
    let is_err = result.is_err();
    let has_errors = diagnostics.has_errors();

    out.push_str(&format!("Status: {}\n", if is_err { "Err" } else { "Ok" }));
    if let Err(err) = &result {
        out.push_str(&format!("DriverError: {:?}\n", err));
    }

    if diagnostics.diagnostics.is_empty() {
        out.push_str("Diagnostics: none\n");
    } else {
        out.push_str("Diagnostics:\n");
        for diag in &diagnostics.diagnostics {
            out.push_str(&format!("- {}: {}\n", diag.level, diag.message));
        }
    }

    (out, has_errors, is_err)
}

#[test]
fn pipeline_negative_type_mismatch() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def bad Nat (lam x Nat x))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for type mismatch");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_parse_error() {
    let source = "(def oops"; // missing closing paren

    let (output, has_errors, is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for parse error");
    assert!(is_err, "Parse errors should return DriverError");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_kernel_recheck_bad_fix() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def bad_fix Nat
          (fix f Nat zero))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(has_errors, "Expected kernel re-check diagnostics for bad fixpoint");
    assert_snapshot!(output);
}
