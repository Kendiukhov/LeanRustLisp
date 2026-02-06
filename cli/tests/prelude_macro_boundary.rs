use cli::driver::{module_id_for_source, process_code, PipelineOptions};
use cli::set_prelude_macro_boundary_allowlist;
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;
use std::fs;
use std::path::PathBuf;

#[test]
fn prelude_macro_boundary_gate() {
    let prelude_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../stdlib/prelude.lrl");
    let prelude = fs::read_to_string(&prelude_path)
        .unwrap_or_else(|e| panic!("failed to read prelude {:?}: {}", prelude_path, e));
    let prelude_path_str = prelude_path.to_string_lossy().to_string();
    let prelude_module = module_id_for_source(&prelude_path_str);

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);

    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);

    let mut diagnostics = DiagnosticCollector::new();
    process_code(
        &prelude,
        &prelude_path_str,
        &mut env,
        &mut expander,
        &PipelineOptions::default(),
        &mut diagnostics,
    )
    .expect("prelude processing failed");

    env.set_allow_reserved_primitives(allow_reserved);
    expander.clear_macro_boundary_allowlist();

    let boundary_messages: Vec<_> = diagnostics
        .diagnostics
        .iter()
        .filter(|d| d.message.contains("macro boundary"))
        .map(|d| d.message.as_str())
        .collect();

    assert!(
        boundary_messages.is_empty(),
        "Prelude macro boundary violations (including staged quasiquote expansions):\n{}",
        boundary_messages.join("\n")
    );

    assert!(
        !diagnostics.has_errors(),
        "Prelude diagnostics contained errors:\n{}",
        diagnostics
            .diagnostics
            .iter()
            .map(|d| format!("- {:?}: {}", d.level, d.message))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
