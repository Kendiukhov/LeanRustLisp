use cli::compiler::{prelude_stack_for_backend, BackendMode};
use cli::driver::{module_id_for_source, process_code, PipelineOptions};
use cli::set_prelude_macro_boundary_allowlist;
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;
use std::fs;
use std::path::PathBuf;
use std::thread;

fn run_with_large_stack<F>(f: F)
where
    F: FnOnce() + Send + 'static,
{
    thread::Builder::new()
        .name("prelude-macro-boundary-large-stack".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("failed to spawn prelude macro boundary worker")
        .join()
        .expect("prelude macro boundary worker panicked");
}

#[test]
fn prelude_macro_boundary_gate() {
    run_with_large_stack(|| {
        let mut env = Env::new();
        let mut expander = Expander::new();
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        let prelude_options = PipelineOptions {
            prelude_frozen: false,
            allow_redefine: false,
            allow_axioms: true,
            ..Default::default()
        };

        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);

        let mut diagnostics = DiagnosticCollector::new();
        let mut prelude_modules = Vec::new();
        for prelude_source in prelude_stack_for_backend(BackendMode::Dynamic) {
            let prelude_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join(prelude_source);
            let prelude = fs::read_to_string(&prelude_path)
                .unwrap_or_else(|e| panic!("failed to read prelude {:?}: {}", prelude_path, e));
            let prelude_module = module_id_for_source(prelude_source);
            if !prelude_modules.is_empty() {
                expander.set_default_imports(prelude_modules.clone());
            }
            set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
            process_code(
                &prelude,
                prelude_source,
                &mut env,
                &mut expander,
                &prelude_options,
                &mut diagnostics,
            )
            .expect("prelude processing failed");
            expander.clear_macro_boundary_allowlist();
            prelude_modules.push(prelude_module);
        }

        env.set_allow_reserved_primitives(allow_reserved);
        expander.set_default_imports(prelude_modules);

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
    });
}
