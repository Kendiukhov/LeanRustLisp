use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root")
}

fn cli_bin() -> PathBuf {
    let test_cli_bin = PathBuf::from(env!("CARGO_BIN_EXE_cli"));
    let plain_cli_bin = test_cli_bin
        .parent()
        .and_then(|dir| dir.parent())
        .map(|dir| dir.join("cli"));
    plain_cli_bin
        .as_ref()
        .filter(|path| path.exists())
        .cloned()
        .unwrap_or(test_cli_bin)
}

fn unique_output_path(repo: &Path, label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock before unix epoch")
        .as_nanos();
    let build_dir = repo.join("build");
    fs::create_dir_all(&build_dir).expect("failed to create build directory");
    build_dir.join(format!("lrl_stdlib_alpha_{}_{}", label, nanos))
}

fn compile_typed(repo: &Path, source: &str, output_bin: &Path) {
    let out = Command::new(cli_bin())
        .current_dir(repo)
        .args([
            "compile",
            source,
            "--backend",
            "typed",
            "-o",
            output_bin
                .to_str()
                .expect("output path should be valid utf-8"),
        ])
        .output()
        .expect("failed to run typed compile");

    let mut combined = String::new();
    combined.push_str(&String::from_utf8_lossy(&out.stdout));
    combined.push_str(&String::from_utf8_lossy(&out.stderr));

    assert!(
        out.status.success(),
        "typed compile failed for {}:\n{}",
        source,
        combined
    );
    assert!(
        output_bin.exists(),
        "typed compile succeeded but output binary is missing for {} at {}:\n{}",
        source,
        output_bin.display(),
        combined
    );
}

fn run_binary(output_bin: &Path) -> String {
    assert!(
        output_bin.exists(),
        "compiled binary path does not exist: {}",
        output_bin.display()
    );
    let out = Command::new(output_bin)
        .output()
        .expect("failed to run compiled binary");

    let mut combined = String::new();
    combined.push_str(&String::from_utf8_lossy(&out.stdout));
    combined.push_str(&String::from_utf8_lossy(&out.stderr));

    assert!(
        out.status.success(),
        "compiled binary failed:\n{}",
        combined
    );

    combined
}

#[test]
fn stdlib_alpha_typed_smoke_programs() {
    let repo = repo_root();
    let cases = [
        ("tests/stdlib_alpha_typed/option_unwrap_some.lrl", "Result: 1"),
        ("tests/stdlib_alpha_typed/result_unwrap_ok.lrl", "Result: 1"),
        ("tests/stdlib_alpha_typed/pair_match_sum.lrl", "Result: 3"),
    ];

    for (source, expected) in cases {
        let output_bin = unique_output_path(&repo, "typed");
        compile_typed(&repo, source, &output_bin);
        let runtime = run_binary(&output_bin);
        let _ = fs::remove_file(&output_bin);

        assert!(
            runtime.contains(expected),
            "unexpected runtime output for {}:\n{}",
            source,
            runtime
        );
    }
}
