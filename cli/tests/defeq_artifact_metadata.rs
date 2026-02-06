use cli::driver::{process_code, Artifact, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::Expander;
use kernel::ast::Transparency;
use kernel::checker::Env;
use kernel::nbe::{
    defeq_fuel_policy, reset_defeq_fuel_cache_for_tests, set_def_eq_fuel_policy, DefEqFuelSource,
};
use std::sync::{Mutex, OnceLock};

fn policy_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn run_pipeline_with_artifacts() -> Vec<Artifact> {
    let source = r#"
        (def id (pi A Type (pi x A A))
          (lam A Type (lam x A x)))
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions {
        collect_artifacts: true,
        ..Default::default()
    };

    let result = process_code(
        source,
        "defeq_artifact_metadata",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    )
    .expect("pipeline should succeed");

    if diagnostics.has_errors() {
        let rendered = diagnostics
            .diagnostics
            .iter()
            .map(|d| d.message_with_code())
            .collect::<Vec<_>>()
            .join("\n");
        panic!("unexpected diagnostics:\n{}", rendered);
    }

    result.artifacts
}

fn extract_defeq_config(artifacts: &[Artifact]) -> (usize, String, Transparency) {
    artifacts
        .iter()
        .find_map(|artifact| match artifact {
            Artifact::DefEqConfig {
                fuel,
                source,
                transparency,
            } => Some((*fuel, source.clone(), *transparency)),
            _ => None,
        })
        .expect("missing DefEqConfig artifact")
}

#[test]
fn artifact_records_default_defeq_policy_metadata() {
    let _guard = policy_lock().lock().expect("policy lock poisoned");
    // Defeq fuel policy is process-global; reset it to ensure this test starts from default.
    reset_defeq_fuel_cache_for_tests();

    let artifacts = run_pipeline_with_artifacts();
    let (fuel, source, transparency) = extract_defeq_config(&artifacts);
    let policy = defeq_fuel_policy();

    assert_eq!(fuel, policy.fuel);
    assert_eq!(source, policy.source.label());
    assert_eq!(transparency, Transparency::Reducible);

    reset_defeq_fuel_cache_for_tests();
}

#[test]
fn artifact_records_env_sourced_defeq_policy_metadata() {
    let _guard = policy_lock().lock().expect("policy lock poisoned");
    // Set the policy source to Env to verify artifact provenance is explicitly recorded.
    reset_defeq_fuel_cache_for_tests();
    set_def_eq_fuel_policy(321, DefEqFuelSource::Env).expect("failed to set defeq fuel policy");

    let artifacts = run_pipeline_with_artifacts();
    let (fuel, source, transparency) = extract_defeq_config(&artifacts);

    assert_eq!(fuel, 321);
    assert_eq!(source, DefEqFuelSource::Env.label());
    assert_eq!(transparency, Transparency::Reducible);

    reset_defeq_fuel_cache_for_tests();
}
