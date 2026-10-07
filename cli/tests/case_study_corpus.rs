//! The ownership validation corpus of `case_studies/corpus/`.
//!
//! `case_studies/corpus/manifest.tsv` lists one row per violation class: a hand-written program,
//! its macro twin (a macro whose expansion is the same violating code), the stage and diagnostic
//! code that must reject them, and a message fragment. Positive controls (the nearest legal
//! variants) must be accepted and run. These tests run the real CLI binary from the repository
//! root, exactly as `case_studies/corpus/run_corpus.sh` does, and check every row:
//!
//! * violation classes: `cli run <file>` exits non-zero, its first `Error: [CODE]` line has the
//!   manifest's code, and the fragment occurs in the output, for the file and for its twin; the
//!   twin's code equals the hand-written file's code;
//! * macro-only classes (17, 21): the hand-written file is accepted, the twin is rejected at the
//!   macro boundary (`F0104`);
//! * positive controls: `cli run` accepts both files, and the binaries built with
//!   `cli compile --backend dynamic` print the manifest's expected line.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cli crate must be inside the workspace")
        .to_path_buf()
}

fn corpus_dir() -> PathBuf {
    repo_root().join("case_studies").join("corpus")
}

#[derive(Clone, Debug)]
struct Row {
    class: String,
    kind: String,
    file: String,
    twin: String,
    stage: String,
    code: String,
    fragment: String,
    twin_stage: String,
    twin_code: String,
    twin_fragment: String,
}

fn read_manifest() -> Vec<Row> {
    let path = corpus_dir().join("manifest.tsv");
    let text = fs::read_to_string(path).expect("manifest.tsv must exist");
    let mut rows = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() || line.starts_with('#') || line.starts_with("class\t") {
            continue;
        }
        let cols: Vec<&str> = line.split('\t').collect();
        assert_eq!(cols.len(), 11, "malformed manifest line: {:?}", line);
        rows.push(Row {
            class: cols[0].to_string(),
            kind: cols[1].to_string(),
            file: cols[2].to_string(),
            twin: cols[3].to_string(),
            stage: cols[4].to_string(),
            code: cols[5].to_string(),
            fragment: cols[6].to_string(),
            twin_stage: cols[7].to_string(),
            twin_code: cols[8].to_string(),
            twin_fragment: cols[9].to_string(),
        });
    }
    rows
}

/// The pipeline stage a diagnostic code belongs to (same mapping as `run_corpus.sh`).
fn stage_of(code: &str) -> &'static str {
    if code == "-" {
        "accepted"
    } else if code == "F0104" {
        "macro_boundary"
    } else if code.starts_with("F01") {
        "macro"
    } else if code.starts_with("F00") {
        "parser"
    } else if code.starts_with('F') {
        "elaborator"
    } else if code.starts_with('K') {
        "kernel"
    } else if code.starts_with('M') {
        "MIR"
    } else {
        "unknown"
    }
}

fn strip_ansi(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' && chars.peek() == Some(&'[') {
            chars.next();
            for d in chars.by_ref() {
                if d == 'm' {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// Code of the first `Error: [CODE] ...` line.
fn first_error_code(output: &str) -> Option<String> {
    output.lines().find_map(|line| {
        let rest = line.strip_prefix("Error: [")?;
        let end = rest.find(']')?;
        let code = &rest[..end];
        if !code.is_empty() && code.chars().all(|c| c.is_ascii_alphanumeric()) {
            Some(code.to_string())
        } else {
            None
        }
    })
}

struct RunOutcome {
    success: bool,
    output: String,
    code: String,
}

/// `cli run case_studies/corpus/<file>` from the repository root.
fn run_file(file: &str) -> RunOutcome {
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args(["run", &format!("case_studies/corpus/{}", file)])
        .output()
        .expect("run cli");
    let text = strip_ansi(&format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    ));
    let success = output.status.success();
    let code = match first_error_code(&text) {
        Some(code) => code,
        None if success && !text.lines().any(|l| l.starts_with("Error")) => "-".to_string(),
        None => "?".to_string(),
    };
    RunOutcome {
        success,
        output: text,
        code,
    }
}

/// `cli compile case_studies/corpus/<file> --backend dynamic -o <tmp>`, then runs the binary.
/// Returns the binary's output, or the compiler output prefixed with `NOBIN` if no binary was built.
fn compile_dynamic_and_run(file: &str) -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_case_study_corpus_{}_{}_{}",
        file.trim_end_matches(".lrl"),
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    let bin = dir.join("out_bin");
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args([
            "compile",
            &format!("case_studies/corpus/{}", file),
            "--backend",
            "dynamic",
            "-o",
            bin.to_str().expect("utf-8 path"),
        ])
        .output()
        .expect("run cli compile");
    let result = if output.status.success() && bin.exists() {
        let run = Command::new(&bin).output().expect("run compiled binary");
        String::from_utf8_lossy(&run.stdout).to_string()
    } else {
        format!(
            "NOBIN\n{}{}",
            strip_ansi(&String::from_utf8_lossy(&output.stdout)),
            strip_ansi(&String::from_utf8_lossy(&output.stderr))
        )
    };
    let _ = fs::remove_dir_all(&dir);
    result
}

/// Applies `check` to every row on a small pool of threads; returns the collected failures.
fn check_rows_in_parallel<F>(rows: &[Row], check: F) -> Vec<String>
where
    F: Fn(&Row) -> Vec<String> + Sync,
{
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(2)
        .clamp(1, 4);
    let next = AtomicUsize::new(0);
    let failures = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, Ordering::SeqCst);
                let Some(row) = rows.get(index) else {
                    break;
                };
                let row_failures = check(row);
                if !row_failures.is_empty() {
                    failures.lock().expect("failures lock").extend(row_failures);
                }
            });
        }
    });
    let mut failures = failures.into_inner().expect("failures lock");
    failures.sort();
    failures
}

fn excerpt(output: &str) -> String {
    output
        .lines()
        .filter(|l| l.starts_with("Error") || l.contains("macro '"))
        .take(4)
        .collect::<Vec<_>>()
        .join("\n      ")
}

/// Checks one file of a violation-class row against (code, fragment).
fn check_rejected_or_accepted(
    class: &str,
    file: &str,
    code: &str,
    fragment: &str,
    outcome: &RunOutcome,
) -> Vec<String> {
    let mut failures = Vec::new();
    if outcome.code != code {
        failures.push(format!(
            "[{}] {}: expected code {} ({}), observed {} ({})\n      {}",
            class,
            file,
            code,
            stage_of(code),
            outcome.code,
            stage_of(&outcome.code),
            excerpt(&outcome.output)
        ));
    }
    let expect_success = code == "-";
    if outcome.success != expect_success {
        failures.push(format!(
            "[{}] {}: expected {} exit status, got success={}",
            class,
            file,
            if expect_success {
                "a zero"
            } else {
                "a non-zero"
            },
            outcome.success
        ));
    }
    if fragment != "-" && !outcome.output.contains(fragment) {
        failures.push(format!(
            "[{}] {}: output does not contain {:?}\n      {}",
            class,
            file,
            fragment,
            excerpt(&outcome.output)
        ));
    }
    failures
}

#[test]
fn manifest_is_consistent_with_the_corpus_directory() {
    let rows = read_manifest();
    assert!(!rows.is_empty(), "manifest has no rows");
    let mut listed = Vec::new();
    for row in &rows {
        for file in [&row.file, &row.twin] {
            assert!(
                corpus_dir().join(file).is_file(),
                "[{}] manifest names a missing file: {}",
                row.class,
                file
            );
            listed.push(file.clone());
        }
        assert_eq!(
            row.twin,
            format!("{}_macro.lrl", row.file.trim_end_matches(".lrl")),
            "[{}] twin must be named <file>_macro.lrl",
            row.class
        );
        assert_eq!(
            stage_of(&row.code),
            row.stage,
            "[{}] stage does not match code",
            row.class
        );
        assert_eq!(
            stage_of(&row.twin_code),
            row.twin_stage,
            "[{}] twin stage does not match twin code",
            row.class
        );
        match row.kind.as_str() {
            "negative" => assert_eq!(
                row.code, row.twin_code,
                "[{}] a macro twin must expect the same code as its hand-written version",
                row.class
            ),
            "macro_only" => {
                assert_eq!(row.code, "-", "[{}] hand-written macro-only", row.class);
                assert_eq!(row.twin_code, "F0104", "[{}] macro-only twin", row.class);
            }
            "positive" => {
                assert_eq!(row.code, "-", "[{}] positive control", row.class);
                assert_eq!(row.twin_code, "-", "[{}] positive control", row.class);
            }
            other => panic!("[{}] unknown kind {:?}", row.class, other),
        }
    }
    let mut on_disk: Vec<String> = fs::read_dir(corpus_dir())
        .expect("read corpus dir")
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.file_name().to_string_lossy().to_string())
        .filter(|name| name.ends_with(".lrl") && !name.starts_with("._"))
        .collect();
    on_disk.sort();
    listed.sort();
    assert_eq!(
        on_disk, listed,
        "every .lrl file of the corpus must be listed exactly once"
    );
}

#[test]
fn violation_classes_are_rejected_with_the_expected_code_by_both_versions() {
    let rows: Vec<Row> = read_manifest()
        .into_iter()
        .filter(|row| row.kind != "positive")
        .collect();
    let failures = check_rows_in_parallel(&rows, |row| {
        let hand = run_file(&row.file);
        let twin = run_file(&row.twin);
        let mut failures =
            check_rejected_or_accepted(&row.class, &row.file, &row.code, &row.fragment, &hand);
        failures.extend(check_rejected_or_accepted(
            &row.class,
            &row.twin,
            &row.twin_code,
            &row.twin_fragment,
            &twin,
        ));
        if row.kind == "negative" && hand.code != twin.code {
            failures.push(format!(
                "[{}] macro twin {} reports {} but the hand-written {} reports {}",
                row.class, row.twin, twin.code, row.file, hand.code
            ));
        }
        failures
    });
    assert!(
        failures.is_empty(),
        "{} corpus expectation(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn positive_controls_are_accepted_and_run_in_both_versions() {
    let rows: Vec<Row> = read_manifest()
        .into_iter()
        .filter(|row| row.kind == "positive")
        .collect();
    let failures = check_rows_in_parallel(&rows, |row| {
        let mut failures = Vec::new();
        for (file, fragment) in [(&row.file, &row.fragment), (&row.twin, &row.twin_fragment)] {
            let outcome = run_file(file);
            if !outcome.success || outcome.code != "-" {
                failures.push(format!(
                    "[{}] {}: expected acceptance by `run`, got success={} code={}\n      {}",
                    row.class,
                    file,
                    outcome.success,
                    outcome.code,
                    excerpt(&outcome.output)
                ));
                continue;
            }
            let printed = compile_dynamic_and_run(file);
            if !printed.contains(fragment.as_str()) {
                failures.push(format!(
                    "[{}] {}: dynamic binary output does not contain {:?}:\n{}",
                    row.class, file, fragment, printed
                ));
            }
        }
        failures
    });
    assert!(
        failures.is_empty(),
        "{} positive control expectation(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
