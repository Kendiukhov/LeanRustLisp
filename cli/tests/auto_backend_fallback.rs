use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time went backwards")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_{}_{}_{}_{}",
        prefix,
        std::process::id(),
        nanos,
        rand_suffix(nanos)
    ));
    fs::create_dir_all(&dir).expect("failed to create temp directory");
    dir
}

fn rand_suffix(seed: u128) -> u64 {
    // Deterministic local suffix from timestamp to reduce temp-dir collision risk.
    (seed as u64) ^ ((seed >> 64) as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

fn write_program(path: &Path, source: &str) {
    fs::write(path, source).expect("failed to write source program");
}

fn run_cli(cwd: &Path, args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(cwd)
        .args(args)
        .output()
        .expect("failed to run cli binary")
}

fn assert_success(output: &Output, context: &str) {
    assert!(
        output.status.success(),
        "{} failed.\nstdout:\n{}\nstderr:\n{}",
        context,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_contains(haystack: &str, needle: &str, context: &str) {
    assert!(
        haystack.contains(needle),
        "{} missing expected text: {}\nactual:\n{}",
        context,
        needle,
        haystack
    );
}

#[test]
fn compile_defaults_to_auto_rejects_axioms_without_allow_axioms() {
    let temp_dir = unique_temp_dir("compile_auto_reject_axioms");
    let source_path = temp_dir.join("axiom_program.lrl");
    let output_bin = temp_dir.join("bin_out");

    let source = r#"
        (inductive copy MyNat (sort 1)
          (ctor mz MyNat)
          (ctor ms (pi n MyNat MyNat)))

        (axiom ext MyNat)
        (noncomputable entry MyNat ext)
    "#;
    write_program(&source_path, source);

    let args = vec![
        "compile".to_string(),
        source_path.to_string_lossy().to_string(),
        "-o".to_string(),
        output_bin.to_string_lossy().to_string(),
    ];
    let output = run_cli(&temp_dir, &args);
    // The CLI currently reports compilation diagnostics on stdout and exits 0.
    // Validate behavior via diagnostics and absence of produced binary.

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_contains(
        &stdout,
        "Program requires axiom stubs, but executable axioms are disabled",
        "compile auto reject without allow-axioms",
    );
    assert!(
        !output_bin.exists(),
        "binary should not be produced when executable axioms are disabled"
    );

    let _ = fs::remove_dir_all(&temp_dir);
}

#[test]
fn compile_defaults_to_auto_and_uses_typed_axiom_stubs_with_allow_axioms() {
    let temp_dir = unique_temp_dir("compile_auto_fallback");
    let source_path = temp_dir.join("axiom_program.lrl");
    let output_bin = temp_dir.join("bin_out");

    let source = r#"
        (inductive copy MyNat (sort 1)
          (ctor mz MyNat)
          (ctor ms (pi n MyNat MyNat)))

        (axiom ext MyNat)
        (noncomputable entry MyNat ext)
    "#;
    write_program(&source_path, source);

    let args = vec![
        "--allow-axioms".to_string(),
        "compile".to_string(),
        source_path.to_string_lossy().to_string(),
        "-o".to_string(),
        output_bin.to_string_lossy().to_string(),
    ];
    let output = run_cli(&temp_dir, &args);
    assert_success(&output, "compile");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_contains(
        &stdout,
        "WARNING: executable axioms enabled for typed backend",
        "compile typed axiom warning",
    );
    assert_contains(
        &stdout,
        "WARNING: executable axiom metadata written to",
        "compile axiom artifact warning",
    );
    assert_contains(&stdout, "Compilation successful", "compile success message");
    assert!(output_bin.exists(), "expected output binary to be created");

    let _ = fs::remove_dir_all(&temp_dir);
}

#[test]
fn compile_mir_defaults_to_auto_and_uses_typed_axiom_stubs_with_allow_axioms() {
    let temp_dir = unique_temp_dir("compile_mir_auto_fallback");
    let source_path = temp_dir.join("axiom_program.lrl");

    let source = r#"
        (inductive copy MyNat (sort 1)
          (ctor mz MyNat)
          (ctor ms (pi n MyNat MyNat)))

        (axiom ext MyNat)
        (noncomputable entry MyNat ext)
    "#;
    write_program(&source_path, source);

    let args = vec![
        "--allow-axioms".to_string(),
        "compile-mir".to_string(),
        source_path.to_string_lossy().to_string(),
    ];
    let output = run_cli(&temp_dir, &args);
    assert_success(&output, "compile-mir");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_contains(
        &stdout,
        "WARNING: executable axioms enabled for typed backend",
        "compile-mir typed axiom warning",
    );
    assert_contains(
        &stdout,
        "WARNING: executable axiom metadata written to",
        "compile-mir axiom artifact warning",
    );
    assert_contains(
        &stdout,
        "Compilation successful",
        "compile-mir success message",
    );
    assert!(
        temp_dir.join("output").exists(),
        "expected default output binary for compile-mir"
    );

    let _ = fs::remove_dir_all(&temp_dir);
}

#[test]
fn auto_mode_with_allow_axioms_remains_compatible_with_typed_prelude_loading() {
    let temp_dir = unique_temp_dir("typed_prelude_auto_fallback");
    let source_path = temp_dir.join("typed_prelude_axiom_program.lrl");
    let output_bin = temp_dir.join("bin_out");
    write_program(
        &source_path,
        r#"
            (axiom ext Nat)
            (noncomputable entry Nat ext)
        "#,
    );

    // For prelude auto-loading, run from repository root so stdlib prelude layers resolve.
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");

    let args = vec![
        "--allow-axioms".to_string(),
        "compile".to_string(),
        source_path.to_string_lossy().to_string(),
        "-o".to_string(),
        output_bin.to_string_lossy().to_string(),
    ];
    let output = run_cli(&repo_root, &args);
    assert_success(&output, "compile with typed prelude + auto fallback");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_contains(
        &stdout,
        "WARNING: executable axioms enabled for typed backend",
        "typed prelude typed-axiom warning",
    );
    assert_contains(
        &stdout,
        "Compilation successful",
        "typed prelude fallback success message",
    );
    assert!(output_bin.exists(), "expected output binary to be created");

    let _ = fs::remove_dir_all(&temp_dir);
}
