use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;
use std::fs;
use std::path::Path;

const INDEXING_SURFACE_PRELUDE: &str = r#"
    (axiom unsafe interior_mutable Type)
    (axiom unsafe may_panic_on_borrow_violation Type)
    (axiom unsafe concurrency_primitive Type)
    (axiom unsafe atomic_primitive Type)
    (axiom unsafe indexable Type)

    (inductive copy Nat (sort 1)
      (zero Nat)
      (succ (pi n Nat Nat)))

    (inductive List (pi T (sort 1) (sort 1))
      (nil (pi {T (sort 1)} (List T)))
      (cons (pi {T (sort 1)} (pi h T (pi t (List T) (List T))))))

    (inductive (indexable) VecDyn (pi T (sort 1) (sort 1))
      (mk_vec_dyn (pi {T (sort 1)} (pi data (List T) (VecDyn T)))))

    (inductive (indexable) Slice (pi T (sort 1) (sort 1))
      (mk_slice (pi {T (sort 1)} (pi data (List T) (Slice T)))))

    (inductive (indexable) Array (pi T (sort 1) (sort 1))
      (mk_array (pi {T (sort 1)} (pi data (List T) (Array T)))))

    (axiom unsafe index_vec_dyn (pi {T (sort 1)} (pi v (VecDyn T) (pi i Nat T))))
    (axiom unsafe index_slice (pi {T (sort 1)} (pi v (Slice T) (pi i Nat T))))
    (axiom unsafe index_array (pi {T (sort 1)} (pi v (Array T) (pi i Nat T))))
"#;

fn load_fixture(rel_path: &str) -> String {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cli crate should have a parent directory");
    let fixture_path = repo_root.join(rel_path);
    fs::read_to_string(&fixture_path)
        .unwrap_or_else(|_| panic!("Missing fixture {:?}", fixture_path))
}

fn load_prelude(env: &mut Env, expander: &mut Expander, options: &PipelineOptions) {
    let mut diagnostics = DiagnosticCollector::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
    process_code(
        INDEXING_SURFACE_PRELUDE,
        "prelude",
        env,
        expander,
        options,
        &mut diagnostics,
    )
    .expect("prelude processing failed");
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    env.set_allow_reserved_primitives(allow_reserved);
    if diagnostics.has_errors() {
        let mut details = String::from("prelude diagnostics contained errors:\n");
        for diag in &diagnostics.diagnostics {
            details.push_str(&format!("- {}: {}\n", diag.level, diag.message_with_code()));
        }
        panic!("{}", details);
    }
}

#[test]
fn indexing_surface_accepts_indexable_containers() {
    let source = load_fixture("tests/indexing_surface.lrl");

    let mut env = Env::new();
    let mut expander = Expander::new();
    let options = PipelineOptions::default();
    load_prelude(&mut env, &mut expander, &options);

    let mut diagnostics = DiagnosticCollector::new();
    let result = process_code(
        &source,
        "indexing_surface.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected indexing surface fixture to parse");
    let errors: Vec<_> = diagnostics
        .diagnostics
        .iter()
        .filter(|d| d.level == Level::Error)
        .filter(|d| !d.message.starts_with("MIR typing error"))
        .collect();
    if !errors.is_empty() {
        let mut details = String::from("unexpected diagnostics for indexable containers:\n");
        for diag in errors {
            details.push_str(&format!("- {}: {}\n", diag.level, diag.message_with_code()));
        }
        panic!("{}", details);
    }
}

#[test]
fn indexing_surface_rejects_non_indexable() {
    let source = load_fixture("tests/indexing_negative.lrl");

    let mut env = Env::new();
    let mut expander = Expander::new();
    let options = PipelineOptions::default();
    load_prelude(&mut env, &mut expander, &options);

    let mut diagnostics = DiagnosticCollector::new();
    let result = process_code(
        &source,
        "indexing_negative.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected negative fixture to parse");
    let errors: Vec<_> = diagnostics
        .diagnostics
        .iter()
        .filter(|d| d.level == Level::Error)
        .filter(|d| !d.message.starts_with("MIR typing error"))
        .collect();
    assert!(
        !errors.is_empty(),
        "expected diagnostics for non-indexable indexing"
    );
}
