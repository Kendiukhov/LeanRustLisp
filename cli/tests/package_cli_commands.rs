use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cli crate must be inside workspace root")
        .to_path_buf()
}

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time should be after unix epoch")
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "lrl_package_cli_{}_{}_{}",
        prefix,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&path).expect("failed to create temp directory");
    path
}

fn copy_dir_recursive(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("failed to create destination fixture directory");
    let mut entries: Vec<PathBuf> = fs::read_dir(from)
        .expect("failed to read fixture source directory")
        .filter_map(|entry| entry.ok().map(|item| item.path()))
        .collect();
    entries.sort();

    for entry in entries {
        let name = entry
            .file_name()
            .expect("fixture entry should have a file name");
        if name.to_string_lossy().starts_with("._") {
            continue;
        }
        let target = to.join(name);
        if entry.is_dir() {
            copy_dir_recursive(&entry, &target);
        } else {
            fs::copy(&entry, &target).expect("failed to copy fixture file");
        }
    }
}

fn copy_fixture(relative: &str, test_name: &str) -> PathBuf {
    let source = workspace_root().join(relative);
    let target = unique_temp_dir(test_name);
    copy_dir_recursive(&source, &target);
    target
}

fn run_cli(cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(cwd)
        .args(args)
        .output()
        .expect("failed to run cli binary")
}

fn assert_success(output: &Output, context: &str) {
    assert!(
        output.status.success(),
        "{} failed\nstdout:\n{}\nstderr:\n{}",
        context,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn package_cli_build_run_and_clean_commands_work() {
    let fixture = copy_fixture("tests/packages/simple_workspace", "simple_workspace_cli");

    let build_output = run_cli(&fixture, &["build"]);
    assert_success(&build_output, "cli build");
    assert!(
        fixture.join("lrl.lock").exists(),
        "build command should generate lockfile"
    );

    let locked_output = run_cli(&fixture, &["build", "--locked"]);
    assert_success(&locked_output, "cli build --locked");

    let run_output = run_cli(&fixture, &["run", "app"]);
    assert_success(&run_output, "cli run app");

    let clean_output = run_cli(&fixture, &["clean"]);
    assert_success(&clean_output, "cli clean");
    assert!(
        !fixture.join("build/lrl").exists(),
        "clean command should remove build/lrl directory"
    );
}

#[test]
fn package_cli_new_command_scaffolds_manifest_and_source() {
    let root = unique_temp_dir("new_command");
    let output = run_cli(&root, &["new", "demo_pkg"]);
    assert_success(&output, "cli new demo_pkg");

    let package_root = root.join("demo_pkg");
    assert!(
        package_root.join("lrl.toml").exists(),
        "new command should create lrl.toml"
    );
    assert!(
        package_root.join("src/main.lrl").exists(),
        "new command should create src/main.lrl"
    );
}
