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
    (seed as u64) ^ ((seed >> 64) as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
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

#[test]
fn auto_backend_compiles_and_runs_promoted_regressions() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");

    let regressions_dir = repo_root.join("tests/auto_stress_regressions");
    let mut files = Vec::new();

    for entry in fs::read_dir(regressions_dir).expect("failed to read regressions dir") {
        let entry = entry.expect("failed to read dir entry");
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("lrl") {
            files.push(path);
        }
    }

    files.sort();

    if files.is_empty() {
        return;
    }

    for path in files {
        let temp_dir = unique_temp_dir("auto_stress_regression");
        let output_bin = temp_dir.join("out_bin");

        let args = vec![
            "compile".to_string(),
            path.to_string_lossy().to_string(),
            "--backend".to_string(),
            "auto".to_string(),
            "-o".to_string(),
            output_bin.to_string_lossy().to_string(),
        ];

        let compile_output = run_cli(&repo_root, &args);
        assert_success(
            &compile_output,
            &format!("auto compile regression {:?}", path),
        );

        assert!(
            output_bin.exists(),
            "expected output binary for regression {:?}",
            path
        );

        let run_output = Command::new(&output_bin)
            .output()
            .expect("failed to run regression binary");
        assert_success(&run_output, &format!("run regression binary {:?}", path));

        let _ = fs::remove_dir_all(&temp_dir);
    }
}
