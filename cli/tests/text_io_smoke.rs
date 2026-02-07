use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::{Mutex, OnceLock};
use std::time::{SystemTime, UNIX_EPOCH};

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time went backwards")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_text_io_{}_{}_{}",
        prefix,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("failed to create temp directory");
    dir
}

fn run_cli(cwd: &Path, args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(cwd)
        .args(args)
        .output()
        .expect("failed to run cli binary")
}

fn assert_compilation_success(output: &Output, context: &str, bin_path: &Path) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("Compilation successful"),
        "{} did not report success.\nstdout:\n{}\nstderr:\n{}",
        context,
        stdout,
        stderr
    );
    assert!(
        bin_path.exists(),
        "{} did not produce output binary at {}",
        context,
        bin_path.display()
    );
}

fn compile_and_run(
    repo_root: &Path,
    source_path: &Path,
    output_bin: &Path,
    run_cwd: &Path,
    backend: &str,
    context: &str,
) -> String {
    let args = vec![
        "compile".to_string(),
        source_path.to_string_lossy().to_string(),
        "--backend".to_string(),
        backend.to_string(),
        "-o".to_string(),
        output_bin.to_string_lossy().to_string(),
    ];
    let compile_output = run_cli(repo_root, &args);
    assert_compilation_success(&compile_output, context, output_bin);

    let run_output = Command::new(output_bin)
        .current_dir(run_cwd)
        .output()
        .expect("failed to execute compiled binary");
    assert!(
        run_output.status.success(),
        "compiled binary failed for {}\nstdout:\n{}\nstderr:\n{}",
        context,
        String::from_utf8_lossy(&run_output.stdout),
        String::from_utf8_lossy(&run_output.stderr)
    );
    String::from_utf8_lossy(&run_output.stdout).to_string()
}

fn lrl_string_literal(raw: &str) -> String {
    let escaped = raw
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t");
    format!("\"{}\"", escaped)
}

fn text_io_test_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

#[test]
fn typed_backend_prints_text_literals() {
    let _guard = text_io_test_lock()
        .lock()
        .expect("text io test lock should not be poisoned");
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");
    let temp_dir = unique_temp_dir("print_text");
    let source_path = temp_dir.join("print_text.lrl");
    let output_bin = temp_dir.join("print_text_bin");
    fs::write(
        &source_path,
        "(def entry Text\n  (print \"Hello, World!\"))\n",
    )
    .expect("failed to write source");

    let stdout = compile_and_run(
        &repo_root,
        &source_path,
        &output_bin,
        &temp_dir,
        "typed",
        "typed backend text print",
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "Hello, World!"),
        "expected printed text line in output, got:\n{}",
        stdout
    );
}

#[test]
fn typed_backend_prints_long_text_literals() {
    let _guard = text_io_test_lock()
        .lock()
        .expect("text io test lock should not be poisoned");
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");
    let temp_dir = unique_temp_dir("print_text_long");
    let source_path = temp_dir.join("print_text_long.lrl");
    let output_bin = temp_dir.join("print_text_long_bin");

    // Keep this above one chunk (16 code points) to exercise chunked text-literal
    // lowering, while keeping compile time bounded for integration tests.
    let long_text = "Hello, World! ".repeat(2);
    let source = format!(
        "(def entry Text\n  (print {}))\n",
        lrl_string_literal(&long_text)
    );
    fs::write(&source_path, source).expect("failed to write source");

    let stdout = compile_and_run(
        &repo_root,
        &source_path,
        &output_bin,
        &temp_dir,
        "typed",
        "typed backend long text print",
    );
    assert!(
        stdout.lines().any(|line| line.trim() == long_text.trim()),
        "expected printed long text line in output, got:\n{}",
        stdout
    );
}

#[test]
fn typed_backend_roundtrips_file_io_with_text() {
    let _guard = text_io_test_lock()
        .lock()
        .expect("text io test lock should not be poisoned");
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");
    let temp_dir = unique_temp_dir("file_io");
    let source_path = temp_dir.join("file_io.lrl");
    let output_bin = temp_dir.join("file_io_bin");
    let target_file = temp_dir.join("a");

    let path_literal = lrl_string_literal("a");
    let source = format!(
        "(def entry Text\n  (let path Text {}\n    (let written Text (write_file path \"b\")\n      (print (read_file path)))))\n",
        path_literal
    );
    fs::write(&source_path, source).expect("failed to write file io source");

    let stdout = compile_and_run(
        &repo_root,
        &source_path,
        &output_bin,
        &temp_dir,
        "typed",
        "typed backend file io",
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "b"),
        "expected file io print output to include 'b', got:\n{}",
        stdout
    );
    let content = fs::read_to_string(&target_file).expect("expected written file");
    assert_eq!(content, "b");
}

#[test]
fn dynamic_backend_prints_text_literals() {
    let _guard = text_io_test_lock()
        .lock()
        .expect("text io test lock should not be poisoned");
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");
    let temp_dir = unique_temp_dir("dynamic_print_text");
    let source_path = temp_dir.join("dynamic_print_text.lrl");
    let output_bin = temp_dir.join("dynamic_print_text_bin");
    fs::write(
        &source_path,
        "(def entry Text\n  (print \"Hello, World!\"))\n",
    )
    .expect("failed to write source");

    let stdout = compile_and_run(
        &repo_root,
        &source_path,
        &output_bin,
        &temp_dir,
        "dynamic",
        "dynamic backend text print",
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "Hello, World!"),
        "expected printed text line in output, got:\n{}",
        stdout
    );
}

#[test]
fn dynamic_backend_roundtrips_file_io_with_text() {
    let _guard = text_io_test_lock()
        .lock()
        .expect("text io test lock should not be poisoned");
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");
    let temp_dir = unique_temp_dir("dynamic_file_io");
    let source_path = temp_dir.join("dynamic_file_io.lrl");
    let output_bin = temp_dir.join("dynamic_file_io_bin");
    let target_file = temp_dir.join("a");

    let path_literal = lrl_string_literal("a");
    let source = format!(
        "(def entry Text\n  (let path Text {}\n    (let written Text (write_file path \"b\")\n      (print (read_file path)))))\n",
        path_literal
    );
    fs::write(&source_path, source).expect("failed to write file io source");

    let stdout = compile_and_run(
        &repo_root,
        &source_path,
        &output_bin,
        &temp_dir,
        "dynamic",
        "dynamic backend file io",
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "b"),
        "expected file io print output to include 'b', got:\n{}",
        stdout
    );
    let content = fs::read_to_string(&target_file).expect("expected written file");
    assert_eq!(content, "b");
}
