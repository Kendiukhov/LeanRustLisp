//! The LRL examples printed in the paper (`paper/jot_r1/`) that are not part of a case study
//! live as separate files in `case_studies/paper_examples/`; `manifest.tsv` there lists, for
//! every file, whether `cli run` accepts it or the diagnostic code that rejects it, and a message
//! fragment. This test runs the real CLI binary from the repository root on every file:
//!
//! * rejected files: `cli run <file>` exits non-zero, its first `Error: [CODE]` line has the
//!   manifest's code, and the fragment occurs in the output;
//! * accepted files: `cli run <file>` exits zero without an `Error` line, and the binary built with
//!   `cli compile <file> --backend dynamic` prints the fragment (e.g. `Result: Nat(3)`).
//!
//! It also checks that every `.lrl` file of the directory is listed exactly once.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cli crate must be inside the workspace")
        .to_path_buf()
}

fn examples_dir() -> PathBuf {
    repo_root().join("case_studies").join("paper_examples")
}

#[derive(Clone, Debug)]
struct Row {
    file: String,
    outcome: String,
    code: String,
    fragment: String,
}

fn read_manifest() -> Vec<Row> {
    let text =
        fs::read_to_string(examples_dir().join("manifest.tsv")).expect("manifest.tsv must exist");
    let mut rows = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() || line.starts_with('#') || line.starts_with("file\t") {
            continue;
        }
        let cols: Vec<&str> = line.split('\t').collect();
        assert_eq!(cols.len(), 5, "malformed manifest line: {:?}", line);
        rows.push(Row {
            file: cols[0].to_string(),
            outcome: cols[1].to_string(),
            code: cols[2].to_string(),
            fragment: cols[3].to_string(),
        });
    }
    rows
}

fn strip_ansi(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' && chars.peek() == Some(&'[') {
            chars.next();
            for d in chars.by_ref() {
                if d.is_ascii_alphabetic() {
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
        Some(rest[..end].to_string())
    })
}

fn cli(args: &[&str]) -> (bool, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args(args)
        .output()
        .expect("run cli");
    let text = strip_ansi(&format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    ));
    (output.status.success(), text)
}

fn unique_temp_dir(file: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_paper_examples_{}_{}_{}",
        file.trim_end_matches(".lrl"),
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

/// Failures (empty if the row holds).
fn check_row(row: &Row) -> Vec<String> {
    let path = format!("case_studies/paper_examples/{}", row.file);
    let (success, output) = cli(&["run", &path]);
    let code = first_error_code(&output);
    let mut failures = Vec::new();
    match row.outcome.as_str() {
        "rejected" => {
            if success {
                failures.push(format!("{}: expected rejection, `run` succeeded", row.file));
            }
            if code.as_deref() != Some(row.code.as_str()) {
                failures.push(format!(
                    "{}: expected first code {}, got {:?}",
                    row.file, row.code, code
                ));
            }
            if !output.contains(&row.fragment) {
                failures.push(format!(
                    "{}: `run` output does not contain {:?}:\n{}",
                    row.file, row.fragment, output
                ));
            }
        }
        "accepted" => {
            if !success || output.lines().any(|line| line.starts_with("Error")) {
                failures.push(format!(
                    "{}: expected acceptance by `run`:\n{}",
                    row.file, output
                ));
                return failures;
            }
            let dir = unique_temp_dir(&row.file);
            let bin = dir.join("out_bin");
            let bin_str = bin.to_string_lossy().to_string();
            let (built, build_output) = cli(&[
                "compile",
                &path,
                "--backend",
                "dynamic",
                "-o",
                bin_str.as_str(),
            ]);
            if !built || !bin.exists() {
                failures.push(format!(
                    "{}: `compile --backend dynamic` failed:\n{}",
                    row.file, build_output
                ));
            } else {
                let run = Command::new(&bin).output().expect("run compiled binary");
                let printed = String::from_utf8_lossy(&run.stdout).to_string();
                if !run.status.success() || !printed.contains(&row.fragment) {
                    failures.push(format!(
                        "{}: dynamic binary (status {:?}) does not print {:?}:\n{}",
                        row.file,
                        run.status.code(),
                        row.fragment,
                        printed
                    ));
                }
            }
            let _ = fs::remove_dir_all(&dir);
        }
        other => failures.push(format!("{}: unknown outcome {:?}", row.file, other)),
    }
    failures
}

#[test]
fn manifest_lists_every_paper_example() {
    let rows = read_manifest();
    assert!(!rows.is_empty(), "manifest has no rows");
    let mut listed: Vec<String> = rows.iter().map(|row| row.file.clone()).collect();
    for row in &rows {
        assert!(
            examples_dir().join(&row.file).is_file(),
            "manifest names a missing file: {}",
            row.file
        );
        match row.outcome.as_str() {
            "accepted" => assert_eq!(row.code, "-", "{}: accepted row with a code", row.file),
            "rejected" => assert_ne!(row.code, "-", "{}: rejected row without a code", row.file),
            other => panic!("{}: unknown outcome {:?}", row.file, other),
        }
    }
    let mut on_disk: Vec<String> = fs::read_dir(examples_dir())
        .expect("read paper_examples dir")
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.file_name().to_string_lossy().to_string())
        .filter(|name| name.ends_with(".lrl") && !name.starts_with("._"))
        .collect();
    on_disk.sort();
    listed.sort();
    assert_eq!(
        on_disk, listed,
        "every .lrl file of case_studies/paper_examples must be listed exactly once"
    );
}

#[test]
fn paper_examples_behave_as_the_paper_states() {
    let rows = read_manifest();
    let failures: Vec<String> = std::thread::scope(|scope| {
        let handles: Vec<_> = rows
            .iter()
            .map(|row| scope.spawn(move || check_row(row)))
            .collect();
        handles
            .into_iter()
            .flat_map(|handle| handle.join().expect("row thread panicked"))
            .collect()
    });
    assert!(
        failures.is_empty(),
        "{} paper example expectation(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
