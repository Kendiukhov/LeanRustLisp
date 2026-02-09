use cli::driver::{process_code, Artifact, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::ast::Term;
use kernel::checker::Env;

fn diagnostics_to_string(diagnostics: &DiagnosticCollector) -> String {
    diagnostics
        .diagnostics
        .iter()
        .map(|diag| format!("- {}: {}", diag.level, diag.message_with_code()))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn constructor_alias_is_usable_without_entering_mir_pipeline() {
    // `mk_flag_ctor` should resolve as a constructor value, not as an ordinary definition.
    let source = r#"
        (inductive Flag (sort 1)
          (mk_flag_ctor Flag))

        (def make_flag_value Flag mk_flag_ctor)
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions {
        collect_artifacts: true,
        ..Default::default()
    };

    let result = process_code(
        source,
        "constructor_alias_pipeline",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    )
    .expect("process_code should succeed");

    assert!(
        !diagnostics.has_errors(),
        "unexpected diagnostics:\n{}",
        diagnostics_to_string(&diagnostics)
    );

    assert!(
        env.get_definition("mk_flag_ctor").is_none(),
        "constructor alias should not be admitted as an ordinary definition"
    );
    assert!(
        !env.constructor_candidates("mk_flag_ctor").is_empty(),
        "constructor alias should still resolve through constructor metadata"
    );

    let make_def = env
        .get_definition("make_flag_value")
        .expect("make_flag_value should be registered");
    assert!(
        matches!(
            make_def.value.as_deref(),
            Some(Term::Ctor(ind, idx, _)) if ind == "Flag" && *idx == 0
        ),
        "make_flag_value should elaborate to constructor value, got {:?}",
        make_def.value
    );

    let mut mir_artifact_names = Vec::new();
    for artifact in &result.artifacts {
        match artifact {
            Artifact::MirBody { name, .. } | Artifact::BorrowCheck { name, .. } => {
                mir_artifact_names.push(name.as_str());
            }
            _ => {}
        }
    }

    assert!(
        mir_artifact_names.contains(&"make_flag_value"),
        "user definition should still run through MIR pipeline"
    );
    assert!(
        !mir_artifact_names.contains(&"mk_flag_ctor"),
        "constructor alias should not produce MIR artifacts"
    );
}
