use cli::driver::{process_code, PipelineOptions};
use cli::expand::{expand_source_with_imports, ExpandMode};
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::macro_expander::Expander;
use insta::assert_snapshot;
use kernel::checker::Env;
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

fn create_temp_dir(prefix: &str) -> PathBuf {
    let mut dir = std::env::temp_dir();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    dir.push(format!("{}_{}_{}", prefix, std::process::id(), nanos));
    fs::create_dir_all(&dir).expect("Failed to create temp dir");
    dir
}

#[test]
fn import_macros_resolves_relative_path() {
    let dir = create_temp_dir("lrl_macro_import");
    let macros_path = dir.join("macros.lrl");
    let main_path = dir.join("main.lrl");

    let macros_src = r#"
        (defmacro mk-id (name)
          (def name (pi A (sort 1) (pi x A A))
            (lam A (sort 1) (lam x A x))))
    "#;

    let main_src = r#"
        (import-macros "macros.lrl")
        (mk-id my_id)
    "#;

    fs::write(&macros_path, macros_src).expect("Failed to write macros file");
    fs::write(&main_path, main_src).expect("Failed to write main file");

    let content = fs::read_to_string(&main_path).expect("Failed to read main file");
    let filename = main_path.to_string_lossy().to_string();

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let result = process_code(
        &content,
        &filename,
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    let errors: Vec<_> = diagnostics
        .diagnostics
        .iter()
        .filter(|d| d.level == Level::Error)
        .filter(|d| !d.message.starts_with("MIR typing error"))
        .collect();
    assert!(errors.is_empty(), "Unexpected diagnostics: {:?}", errors);
    let processed = result.expect("Process code should succeed");
    assert!(
        processed
            .deployed_definitions
            .contains(&"my_id".to_string()),
        "Expected imported macro to define my_id"
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn import_macros_missing_path_reports_error() {
    let dir = create_temp_dir("lrl_macro_import_missing");
    let main_path = dir.join("main.lrl");

    let main_src = r#"(import-macros "missing.lrl")"#;
    fs::write(&main_path, main_src).expect("Failed to write main file");

    let content = fs::read_to_string(&main_path).expect("Failed to read main file");
    let filename = main_path.to_string_lossy().to_string();

    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let result = process_code(
        &content,
        &filename,
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_err(), "Expected missing import to error");
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.message.contains("not found")),
        "Expected a not found diagnostic"
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn import_macros_expand_snapshot() {
    let fixture_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("macro_imports");
    let main_path = fixture_dir.join("main.lrl");

    let content = fs::read_to_string(&main_path).expect("Failed to read fixture main.lrl");
    let filename = main_path.to_string_lossy().to_string();

    let mut expander = Expander::new();
    let output = expand_source_with_imports(&content, &filename, &mut expander, ExpandMode::Full)
        .expect("Expansion should succeed");

    assert_snapshot!("import_macros_expand", output);
}
