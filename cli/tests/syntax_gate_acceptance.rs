use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;

fn process_source(
    env: &mut Env,
    expander: &mut Expander,
    source: &str,
    filename: &str,
) -> DiagnosticCollector {
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    let result = process_code(source, filename, env, expander, &options, &mut diagnostics);
    assert!(
        result.is_ok(),
        "process_code returned DriverError for {}: {:?}",
        filename,
        result.err()
    );
    diagnostics
}

#[test]
fn legacy_modifier_spellings_emit_compatibility_warnings() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    let diagnostics = process_source(
        &mut env,
        &mut expander,
        "(module Main)\n(opaque legacy_opaque (sort 1) (sort 0))\n(transparent legacy_transparent (sort 1) (sort 0))",
        "legacy_modifiers",
    );

    let warning_messages: Vec<_> = diagnostics
        .diagnostics
        .iter()
        .filter(|diag| diag.level == Level::Warning)
        .map(|diag| diag.message.as_str())
        .collect();

    assert!(
        warning_messages
            .iter()
            .any(|msg| msg.contains("'(opaque ...)' is compatibility syntax")),
        "expected opaque compatibility warning, got {:?}",
        warning_messages
    );
    assert!(
        warning_messages
            .iter()
            .any(|msg| msg.contains("'(transparent ...)' is compatibility syntax")),
        "expected transparent compatibility warning, got {:?}",
        warning_messages
    );
}

#[test]
fn canonical_def_modifiers_do_not_emit_compatibility_warnings() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    let diagnostics = process_source(
        &mut env,
        &mut expander,
        "(module Main)\n(def opaque canonical_opaque (sort 1) (sort 0))\n(def transparent canonical_transparent (sort 1) (sort 0))",
        "canonical_modifiers",
    );

    let has_compat_warning = diagnostics
        .diagnostics
        .iter()
        .any(|diag| diag.level == Level::Warning && diag.message.contains("compatibility syntax"));

    assert!(
        !has_compat_warning,
        "canonical def form should not emit compatibility warnings: {:?}",
        diagnostics
            .diagnostics
            .iter()
            .map(|diag| diag.message_with_code())
            .collect::<Vec<_>>()
    );
}

#[test]
fn match_list_emits_deprecation_warning() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    let diagnostics = process_source(
        &mut env,
        &mut expander,
        "(module Main)\n(def uses_match_list (sort 1) (match_list xs T R (case (nil T) R) (case (cons T h tl) h)))",
        "match_list_deprecation",
    );

    assert!(
        diagnostics.diagnostics.iter().any(|diag| {
            diag.level == Level::Warning
                && diag
                    .message
                    .contains("'match_list' is deprecated core syntax")
        }),
        "expected match_list deprecation warning, got {:?}",
        diagnostics
            .diagnostics
            .iter()
            .map(|diag| diag.message_with_code())
            .collect::<Vec<_>>()
    );
}
