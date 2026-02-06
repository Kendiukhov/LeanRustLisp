use cli::configure_defeq_fuel;
use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::Expander;
use kernel::checker::Env;
use kernel::nbe::reset_defeq_fuel_cache_for_tests;
use std::sync::{Mutex, OnceLock};

fn env_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn run_pipeline(source: &str) -> (String, bool, bool) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions {
        collect_artifacts: false,
        ..Default::default()
    };

    let result = process_code(
        source,
        "defeq_fuel_pipeline",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

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
            out.push_str(&format!("- {}: {}\n", diag.level, diag.message_with_code()));
        }
    }

    (out, has_errors, is_err)
}

fn defeq_fuel_source(chain_len: usize) -> String {
    let mut source = String::new();
    source.push_str("(inductive copy Nat2 Type\n  (zero Nat2)\n  (succ (pi n Nat2 Nat2)))\n\n");
    source.push_str("(def fn0 Type (pi n Nat2 Nat2))\n");
    for i in 1..=chain_len {
        source.push_str(&format!("(def fn{} Type fn{})\n", i, i - 1));
    }
    source.push_str(&format!("(axiom f fn{})\n", chain_len));
    source.push_str("(noncomputable use Nat2 (f zero))\n");
    source
}

#[test]
fn pipeline_defeq_fuel_exhausted_diagnostic() {
    let _guard = env_lock().lock().expect("env lock poisoned");
    std::env::set_var("LRL_DEFEQ_FUEL", "10");
    reset_defeq_fuel_cache_for_tests();
    configure_defeq_fuel(None).expect("failed to configure defeq fuel from env");
    let source = defeq_fuel_source(40);
    let (output, has_errors, _is_err) = run_pipeline(&source);
    std::env::remove_var("LRL_DEFEQ_FUEL");
    reset_defeq_fuel_cache_for_tests();

    assert!(
        has_errors,
        "Expected defeq fuel exhaustion diagnostic, got:\n{}",
        output
    );
    assert!(
        output.contains("Definitional equality fuel exhausted"),
        "Expected defeq fuel exhaustion message, got:\n{}",
        output
    );
    assert!(
        output.contains("LRL_DEFEQ_FUEL"),
        "Expected fuel guidance to mention LRL_DEFEQ_FUEL, got:\n{}",
        output
    );
    assert!(
        output.contains("source = LRL_DEFEQ_FUEL"),
        "Expected fuel source to mention LRL_DEFEQ_FUEL, got:\n{}",
        output
    );
}

#[test]
fn pipeline_defeq_fuel_succeeds_with_higher_budget() {
    let _guard = env_lock().lock().expect("env lock poisoned");
    std::env::set_var("LRL_DEFEQ_FUEL", "2000");
    reset_defeq_fuel_cache_for_tests();
    configure_defeq_fuel(None).expect("failed to configure defeq fuel from env");
    let source = defeq_fuel_source(40);
    let (output, has_errors, is_err) = run_pipeline(&source);
    std::env::remove_var("LRL_DEFEQ_FUEL");
    reset_defeq_fuel_cache_for_tests();

    assert!(
        !has_errors && !is_err,
        "Expected pipeline to succeed with higher defeq fuel, got:\n{}",
        output
    );
}
