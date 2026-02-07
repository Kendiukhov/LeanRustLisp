use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root")
}

fn collect_lrl_files(root: &Path, out: &mut Vec<PathBuf>) {
    let entries = match fs::read_dir(root) {
        Ok(entries) => entries,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Some(name) = path.file_name().and_then(|s| s.to_str()) else {
            continue;
        };
        if name.starts_with('.') || name.starts_with("._") {
            continue;
        }
        if path.is_dir() {
            // Package workspace fixtures are validated by dedicated package tests and do not
            // compile as standalone modules from repository root.
            if name == "packages" {
                continue;
            }
            collect_lrl_files(&path, out);
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("lrl") {
            out.push(path);
        }
    }
}

fn run_compile(repo_root: &Path, source_path: &Path, backend: &str) -> String {
    let test_cli_bin = PathBuf::from(env!("CARGO_BIN_EXE_cli"));
    let plain_cli_bin = test_cli_bin
        .parent()
        .and_then(|dir| dir.parent())
        .map(|dir| dir.join("cli"));
    let cli_bin = plain_cli_bin
        .as_ref()
        .filter(|path| path.exists())
        .cloned()
        .unwrap_or(test_cli_bin);
    let out_bin = std::env::temp_dir().join("lrl_corpus_expectations_out_bin");
    let output = Command::new(cli_bin)
        .current_dir(repo_root)
        .args([
            "compile",
            source_path
                .to_str()
                .expect("source path must be valid utf-8 for test"),
            "--backend",
            backend,
            "-o",
            out_bin
                .to_str()
                .expect("temp output path must be valid utf-8 for test"),
        ])
        .output()
        .expect("failed to run cli compile command");
    let _ = fs::remove_file(out_bin);
    let mut combined = String::new();
    combined.push_str(&String::from_utf8_lossy(&output.stdout));
    combined.push_str(&String::from_utf8_lossy(&output.stderr));
    combined
}

fn is_compile_success(output: &str) -> bool {
    output.contains("Compilation successful.")
}

fn is_compile_failure(output: &str) -> bool {
    output.contains("Compilation aborted due to errors.")
        || output.contains("Codegen aborted due to safety errors.")
        || output.contains("Compilation failed.")
        || output.contains("Prelude compilation failed.")
        || output.contains("fatal runtime error:")
        || output.contains("has overflowed its stack")
        || output.contains("error[")
        || output.contains("Error:")
}

#[test]
fn lrl_corpus_matches_expected_pass_fail_contract_for_typed_and_dynamic() {
    let repo_root = repo_root();
    let tests_root = repo_root.join("tests");
    let mut files = Vec::new();
    collect_lrl_files(&tests_root, &mut files);
    files.sort();

    let expected_negative_all_backends: HashSet<&'static str> = HashSet::from([
        "tests/bad_match.lrl",
        "tests/borrow_edge_cases_negative.lrl",
        "tests/borrow_surface_negative.lrl",
        "tests/indexing_negative.lrl",
        "tests/prop_elim_eq_bad.lrl",
        "tests/stdlib_sugared_usage.lrl",
    ]);
    let expected_negative_dynamic_only: HashSet<&'static str> = HashSet::new();

    let mut mismatches = Vec::new();
    for backend in ["typed", "dynamic"] {
        for file in &files {
            let rel = file
                .strip_prefix(&repo_root)
                .expect("file should be under repo root")
                .to_string_lossy()
                .replace('\\', "/");
            let should_fail = expected_negative_all_backends.contains(rel.as_str())
                || (backend == "dynamic" && expected_negative_dynamic_only.contains(rel.as_str()));
            if !should_fail {
                continue;
            }

            let output = run_compile(&repo_root, file, backend);
            let success = is_compile_success(&output);
            let failure = is_compile_failure(&output);
            let observed = if success && !failure { "pass" } else { "fail" };
            if observed != "fail" {
                let excerpt = output.lines().take(16).collect::<Vec<_>>().join("\n");
                mismatches.push(format!(
                    "[{}] {}: expected fail, observed {}\n{}",
                    backend, rel, observed, excerpt
                ));
            }
        }
    }

    assert!(
        mismatches.is_empty(),
        "negative LRL corpus contract mismatches:\n{}",
        mismatches.join("\n\n")
    );
}
