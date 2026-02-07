use cli::package_manager::{build_workspace_at, BuildOptions};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};
use std::thread;
use std::time::{SystemTime, UNIX_EPOCH};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cli crate must be inside workspace root")
        .to_path_buf()
}

fn unique_temp_dir(name: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after unix epoch")
        .as_nanos();
    path.push(format!("lrl_pkg_fixture_{}_{}", name, stamp));
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

fn run_with_large_stack<F>(f: F)
where
    F: FnOnce() + Send + 'static,
{
    thread::Builder::new()
        .name("package-management".to_string())
        .stack_size(32 * 1024 * 1024)
        .spawn(f)
        .expect("failed to spawn large-stack test worker")
        .join()
        .expect("large-stack test worker panicked");
}

fn package_test_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

#[test]
fn workspace_build_writes_deterministic_lockfile_and_uses_cache() {
    let _guard = package_test_lock()
        .lock()
        .expect("package test lock should not be poisoned");
    run_with_large_stack(|| {
        let fixture = copy_fixture("tests/packages/simple_workspace", "simple_workspace");

        let first = build_workspace_at(&fixture, BuildOptions::default())
            .expect("first workspace build should succeed");
        assert!(
            !first.built.is_empty(),
            "first build should compile packages, report={:?}",
            first
        );
        assert!(
            first.built.iter().any(|name| name.starts_with("dep@")),
            "first build should compile dependency package, report={:?}",
            first
        );
        assert!(
            first.built.iter().any(|name| name.starts_with("app@")),
            "first build should compile app package that consumes stdlib-backed dependency symbols, report={:?}",
            first
        );

        let lock_path = fixture.join("lrl.lock");
        assert!(
            lock_path.exists(),
            "build should create lockfile at '{}'",
            lock_path.display()
        );
        let lock_before =
            fs::read_to_string(&lock_path).expect("failed to read generated lockfile");
        assert!(
            lock_before.contains("name = \"dep\"") && lock_before.contains("name = \"app\""),
            "lockfile should contain resolved app/dep packages, lockfile:\n{}",
            lock_before
        );

        let second = build_workspace_at(&fixture, BuildOptions::default())
            .expect("second workspace build should succeed");
        let lock_after = fs::read_to_string(&lock_path).expect("failed to read generated lockfile");

        assert_eq!(
            lock_before, lock_after,
            "lockfile should be deterministic across builds"
        );
        assert!(
            !second.skipped.is_empty(),
            "second build should reuse cache, report={:?}",
            second
        );
    });
}

#[test]
fn workspace_multi_version_alias_build_succeeds() {
    let _guard = package_test_lock()
        .lock()
        .expect("package test lock should not be poisoned");
    run_with_large_stack(|| {
        let fixture = copy_fixture("tests/packages/multi_version_workspace", "alias_workspace");
        fs::write(
            fixture.join("lrl.toml"),
            "[workspace]\nmembers = [\"b_v1\", \"b_v2\", \"a\", \"c\", \"d_alias\"]\n",
        )
        .expect("failed to trim workspace members for alias-only scenario");

        let report = build_workspace_at(&fixture, BuildOptions::default())
            .expect("alias workspace build should succeed");
        assert!(
            report.built.iter().any(|name| name.starts_with("d_alias@")),
            "alias workspace should build d_alias package, report={:?}",
            report
        );

        let lock_path = fixture.join("lrl.lock");
        let lock = fs::read_to_string(&lock_path).expect("failed to read generated lockfile");
        assert_eq!(
            lock.matches("name = \"b\"").count(),
            2,
            "alias workspace lockfile should contain both b versions for explicit stdlib-facing alias imports, lockfile:\n{}",
            lock
        );
    });
}

#[test]
fn workspace_multi_version_ambiguous_import_fails() {
    let _guard = package_test_lock()
        .lock()
        .expect("package test lock should not be poisoned");
    run_with_large_stack(|| {
        let fixture = copy_fixture(
            "tests/packages/multi_version_workspace",
            "ambiguous_workspace",
        );

        let err = build_workspace_at(&fixture, BuildOptions::default())
            .expect_err("ambiguous workspace should fail during import resolution");
        assert!(
            err.to_string().contains("Ambiguous import: b resolves to"),
            "expected ambiguous import error, got: {}",
            err
        );
    });
}
