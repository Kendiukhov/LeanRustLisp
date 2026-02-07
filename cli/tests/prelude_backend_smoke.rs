use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time went backwards")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("lrl_{}_{}_{}", prefix, std::process::id(), nanos));
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

fn normalize_nat_result(stdout: &str) -> Option<u64> {
    let value = stdout
        .lines()
        .find_map(|line| line.trim().strip_prefix("Result: "))
        .map(str::trim)?;
    if let Some(rest) = value.strip_prefix("Nat(").and_then(|s| s.strip_suffix(')')) {
        rest.parse::<u64>().ok()
    } else {
        value.parse::<u64>().ok()
    }
}

#[test]
fn backend_smoke_compiles_program_matrix_with_unified_prelude_stack() {
    let temp_dir = unique_temp_dir("backend_smoke_matrix");
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");
    let programs: [(&str, &str); 4] = [
        (
            "nat_literal",
            r#"
            (def entry Nat (succ zero))
        "#,
        ),
        (
            "nat_add",
            r#"
            (def entry Nat (add (succ zero) (succ (succ zero))))
        "#,
        ),
        (
            "bool_ops",
            r#"
            (def entry Bool (and true (not false)))
        "#,
        ),
        (
            "if_nat",
            r#"
            (def entry Nat (if_nat true (succ zero) zero))
        "#,
        ),
    ];

    for backend in ["dynamic", "typed"] {
        for (name, source) in programs {
            let source_path = temp_dir.join(format!("{}_{}.lrl", backend, name));
            let output_bin = temp_dir.join(format!("{}_{}", backend, name));
            fs::write(&source_path, source).expect("failed to write source file");

            let args = vec![
                "compile".to_string(),
                source_path.to_string_lossy().to_string(),
                "--backend".to_string(),
                backend.to_string(),
                "-o".to_string(),
                output_bin.to_string_lossy().to_string(),
            ];
            let output = run_cli(&repo_root, &args);
            assert_compilation_success(
                &output,
                &format!("{} backend / {}", backend, name),
                &output_bin,
            );

            let run_output = Command::new(&output_bin)
                .output()
                .expect("failed to execute compiled binary");
            assert!(
                run_output.status.success(),
                "compiled binary failed for {} backend / {}\nstdout:\n{}\nstderr:\n{}",
                backend,
                name,
                String::from_utf8_lossy(&run_output.stdout),
                String::from_utf8_lossy(&run_output.stderr)
            );
        }
    }

    let _ = fs::remove_dir_all(&temp_dir);
}

#[test]
fn backend_smoke_append_nat_matches_outputs_across_backends() {
    let temp_dir = unique_temp_dir("backend_smoke_append");
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");

    let source = r#"
        (def len (pi #[once] l (List Nat) Nat)
          (lam #[once] l (List Nat)
            (match l Nat
              (case (nil) zero)
              (case (cons h t ih) (succ ih)))))

        (def entry Nat
          (len (append (cons zero (cons (succ zero) (nil)))
                       (cons (succ (succ zero)) (nil)))))
    "#;
    let source_path = temp_dir.join("append_nat.lrl");
    fs::write(&source_path, source).expect("failed to write append source file");

    let dynamic_bin = temp_dir.join("append_nat_dynamic");
    let typed_bin = temp_dir.join("append_nat_typed");

    let dynamic_stdout = compile_and_run(
        &repo_root,
        &source_path,
        &dynamic_bin,
        "dynamic",
        "dynamic backend / append_nat",
    );
    let typed_stdout = compile_and_run(
        &repo_root,
        &source_path,
        &typed_bin,
        "typed",
        "typed backend / append_nat",
    );

    let dynamic_result = normalize_nat_result(&dynamic_stdout)
        .expect("dynamic backend append_nat output missing numeric Result line");
    let typed_result = normalize_nat_result(&typed_stdout)
        .expect("typed backend append_nat output missing numeric Result line");

    assert_eq!(
        dynamic_result, typed_result,
        "append_nat normalized results should match across backends"
    );
    assert_eq!(dynamic_result, 3, "append_nat expected Result: 3");

    let _ = fs::remove_dir_all(&temp_dir);
}

#[test]
fn backend_smoke_prefix_arithmetic_operators_match_outputs_across_backends() {
    let temp_dir = unique_temp_dir("backend_smoke_prefix_ops");
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root");

    let cases: [(&str, &str, u64); 4] = [
        ("plus", "(def entry Nat (+ 1 2))", 3),
        ("minus", "(def entry Nat (- 5 2))", 3),
        ("multiply", "(def entry Nat (* 3 4))", 12),
        ("divide", "(def entry Nat (/ 9 2))", 4),
    ];

    for (name, source, expected) in cases {
        let source_path = temp_dir.join(format!("{}_ops.lrl", name));
        fs::write(&source_path, source).expect("failed to write prefix operator source file");

        let dynamic_bin = temp_dir.join(format!("{}_dynamic", name));
        let typed_bin = temp_dir.join(format!("{}_typed", name));

        let dynamic_stdout = compile_and_run(
            &repo_root,
            &source_path,
            &dynamic_bin,
            "dynamic",
            &format!("dynamic backend / prefix {}", name),
        );
        let typed_stdout = compile_and_run(
            &repo_root,
            &source_path,
            &typed_bin,
            "typed",
            &format!("typed backend / prefix {}", name),
        );

        let dynamic_result = normalize_nat_result(&dynamic_stdout)
            .expect("dynamic backend output missing numeric Result line");
        let typed_result = normalize_nat_result(&typed_stdout)
            .expect("typed backend output missing numeric Result line");

        assert_eq!(
            dynamic_result, typed_result,
            "prefix operator '{}' should match across backends",
            name
        );
        assert_eq!(
            dynamic_result, expected,
            "prefix operator '{}' expected Result: {}",
            name, expected
        );
    }

    let _ = fs::remove_dir_all(&temp_dir);
}
