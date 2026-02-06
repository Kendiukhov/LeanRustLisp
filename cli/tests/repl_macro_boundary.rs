use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;

#[test]
fn repl_macro_boundary_deny_blocks_smuggle_without_side_effects() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    let options = PipelineOptions {
        show_types: true,
        show_eval: false,
        verbose: false,
        collect_artifacts: false,
        panic_free: false,
        require_axiom_tags: false,
        allow_axioms: false,
        prelude_frozen: true,
        allow_redefine: false,
    };

    let mut diagnostics = DiagnosticCollector::new();
    let result = process_code(
        "(defmacro smuggle_axiom () (quasiquote (axiom classical bad (sort 0))))",
        "repl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );
    assert!(result.is_ok(), "Expected macro definition to succeed");
    assert!(
        !diagnostics.has_errors(),
        "Unexpected diagnostics for macro definition"
    );

    let mut diagnostics = DiagnosticCollector::new();
    let result = process_code(
        "(smuggle_axiom)",
        "repl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );
    assert!(
        result.is_err(),
        "Expected macro boundary denial to abort REPL form"
    );
    assert!(
        diagnostics.has_errors(),
        "Expected diagnostics for macro boundary denial"
    );
    assert!(
        env.get_definition("bad").is_none(),
        "Smuggled axiom should not be present in env"
    );

    let mut diagnostics = DiagnosticCollector::new();
    let _ = process_code(
        "bad",
        "repl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );
    assert!(
        diagnostics.has_errors(),
        "Expected unresolved reference after denied macro expansion"
    );
    assert!(
        env.get_definition("bad").is_none(),
        "Smuggled axiom should remain absent"
    );
}
