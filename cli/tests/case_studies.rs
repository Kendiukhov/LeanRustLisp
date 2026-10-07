//! The two case-study programs of `case_studies/lrl/` and their variants, run through the real
//! CLI binary from the repository root (as `case_studies/lrl/run_vectors.sh` and
//! `run_protocol.sh` do):
//!
//! * `vectors.lrl` (length-indexed vectors with kernel-checked proofs) and `protocol.lrl` (an
//!   affine protocol channel tied to a vector, with macro-generated operations) are accepted by
//!   `cli run`, and compile and run with both code generators (`--backend typed` and
//!   `--backend dynamic`), printing the outputs documented in the programs;
//! * every negative variant in `case_studies/lrl/neg/` is rejected with its diagnostic code (and
//!   a message fragment);
//! * the documented limits in `case_studies/lrl/limits/` (what the types do NOT enforce) are
//!   accepted and run.

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

struct CliOutcome {
    success: bool,
    output: String,
}

fn run_cli(args: &[&str]) -> CliOutcome {
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args(args)
        .output()
        .expect("run cli");
    CliOutcome {
        success: output.status.success(),
        output: strip_ansi(&format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )),
    }
}

/// `cli compile <file> --backend <backend> -o <tmp>`, then runs the binary. Returns the lines
/// the binary printed, or an error describing what failed.
fn compile_and_run(file: &str, backend: &str) -> Result<Vec<String>, String> {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after epoch")
        .as_nanos();
    let stem = Path::new(file)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("program");
    let dir = std::env::temp_dir().join(format!(
        "lrl_case_studies_{}_{}_{}_{}",
        stem,
        backend,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    let bin = dir.join("out_bin");
    let compiled = run_cli(&[
        "compile",
        file,
        "--backend",
        backend,
        "-o",
        bin.to_str().expect("utf-8 path"),
    ]);
    let result = if !compiled.success || !bin.exists() {
        Err(format!(
            "compile {} --backend {} failed:\n{}",
            file, backend, compiled.output
        ))
    } else if compiled.output.contains("falling back to dynamic") {
        Err(format!(
            "compile {} --backend {} fell back:\n{}",
            file, backend, compiled.output
        ))
    } else {
        let run = Command::new(&bin).output().expect("run compiled binary");
        let stdout = String::from_utf8_lossy(&run.stdout).to_string();
        if run.status.success() {
            Ok(stdout.lines().map(|l| l.trim().to_string()).collect())
        } else {
            Err(format!(
                "binary of {} ({}) failed:\n{}{}",
                file,
                backend,
                stdout,
                String::from_utf8_lossy(&run.stderr)
            ))
        }
    };
    let _ = fs::remove_dir_all(&dir);
    result
}

/// Runs the jobs on a small pool of threads and returns the failures, sorted.
fn run_in_parallel<T: Sync>(jobs: &[T], check: impl Fn(&T) -> Vec<String> + Sync) -> Vec<String> {
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
                let Some(job) = jobs.get(index) else {
                    break;
                };
                let job_failures = check(job);
                if !job_failures.is_empty() {
                    failures.lock().expect("failures lock").extend(job_failures);
                }
            });
        }
    });
    let mut failures = failures.into_inner().expect("failures lock");
    failures.sort();
    failures
}

/// (file, backend, lines printed by the binary, in order)
const PROGRAMS: &[(&str, &str, &[&str])] = &[
    (
        "case_studies/lrl/vectors.lrl",
        "typed",
        &["1", "3", "6", "5", "60", "3", "Result: 6"],
    ),
    (
        "case_studies/lrl/vectors.lrl",
        "dynamic",
        &["1", "3", "6", "5", "60", "3", "Result: Nat(6)"],
    ),
    (
        "case_studies/lrl/protocol.lrl",
        "typed",
        &["7", "8", "9", "5", "Result: 29"],
    ),
    (
        "case_studies/lrl/protocol.lrl",
        "dynamic",
        &["7", "8", "9", "5", "Result: Nat(29)"],
    ),
    (
        "case_studies/lrl/limits/protocol_drop_unclosed.lrl",
        "dynamic",
        &["7", "Result: Nat(0)"],
    ),
    (
        "case_studies/lrl/limits/protocol_reindex.lrl",
        "dynamic",
        &["1", "2", "3", "4", "5", "6", "Result: Nat(6)"],
    ),
];

#[test]
fn case_study_programs_are_accepted_and_run_with_both_backends() {
    let mut failures = run_in_parallel(
        &[
            "case_studies/lrl/vectors.lrl",
            "case_studies/lrl/protocol.lrl",
        ],
        |file| {
            let outcome = run_cli(&["run", file]);
            if outcome.success && !outcome.output.lines().any(|l| l.starts_with("Error")) {
                Vec::new()
            } else {
                vec![format!(
                    "cli run {} did not accept it:\n{}",
                    file, outcome.output
                )]
            }
        },
    );
    failures.extend(run_in_parallel(
        PROGRAMS,
        |(file, backend, expected)| match compile_and_run(file, backend) {
            Ok(lines) if lines == expected.iter().map(|s| s.to_string()).collect::<Vec<_>>() => {
                Vec::new()
            }
            Ok(lines) => vec![format!(
                "{} ({}): expected output {:?}, got {:?}",
                file, backend, expected, lines
            )],
            Err(err) => vec![err],
        },
    ));
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// (file under case_studies/lrl/neg/, first diagnostic code, message fragment)
const NEGATIVES: &[(&str, &str, &str)] = &[
    (
        "vectors_vhead_vnil.lrl",
        "F0214",
        "Unification failed: Nat.zero vs (Nat.succ",
    ),
    (
        "vectors_vappend_wrong_index.lrl",
        "F0214",
        "in 'vappend': Unification failed",
    ),
    (
        "vectors_vappend_wrong_length.lrl",
        "F0214",
        "in 'v3_claimed': Unification failed",
    ),
    (
        "vectors_false_vreverse_vsnoc.lrl",
        "F0214",
        "in 'vreverse_vsnoc_wrong'",
    ),
    (
        "vectors_false_reverse_concrete.lrl",
        "F0214",
        "in 'reverse_is_identity_on_12'",
    ),
    (
        "vectors_vmap_fnonce.lrl",
        "F0206",
        "in 'vmap_once': Function kind mismatch",
    ),
    (
        "vectors_vtail_direct_generic.lrl",
        "K0021",
        "[RecursiveFieldConsumedByIh]: recursive field 't'",
    ),
    (
        "protocol_send_twice.lrl",
        "K0021",
        "variable 'c' is used after it was moved",
    ),
    (
        "protocol_send_twice_macro.lrl",
        "K0021",
        "macro 'send-and-retry' expanded here",
    ),
    (
        "protocol_use_after_branch.lrl",
        "K0021",
        "variable 'c' is used after it was moved",
    ),
    (
        "protocol_send_on_closed.lrl",
        "F0214",
        "Unification failed: Nat.zero vs (Nat.succ",
    ),
    (
        "protocol_close_early.lrl",
        "F0214",
        "in 'early': Unification failed",
    ),
    (
        "protocol_send_all_wrong_length.lrl",
        "F0214",
        "in 'short': Unification failed",
    ),
    (
        "protocol_capture_by_hand.lrl",
        "K0003",
        "Expected function type, got App(Ind(\"List\", []), Ind(\"Nat\", []))",
    ),
    (
        "protocol_send_not_once.lrl",
        "F0206",
        "in code produced by macro 'defsend'",
    ),
];

#[test]
fn case_study_negative_variants_are_rejected_with_their_codes() {
    // Every negative file is listed, and every listed file exists.
    let neg_dir = repo_root().join("case_studies").join("lrl").join("neg");
    let mut on_disk: Vec<String> = fs::read_dir(neg_dir)
        .expect("neg directory")
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.file_name().to_string_lossy().to_string())
        .filter(|name| name.ends_with(".lrl") && !name.starts_with("._"))
        .collect();
    on_disk.sort();
    let mut listed: Vec<String> = NEGATIVES.iter().map(|(f, _, _)| f.to_string()).collect();
    listed.sort();
    assert_eq!(
        on_disk, listed,
        "case_studies/lrl/neg/ and NEGATIVES differ"
    );

    let failures = run_in_parallel(NEGATIVES, |(file, code, fragment)| {
        let outcome = run_cli(&["run", &format!("case_studies/lrl/neg/{}", file)]);
        let observed = first_error_code(&outcome.output);
        if !outcome.success
            && observed.as_deref() == Some(*code)
            && outcome.output.contains(fragment)
        {
            Vec::new()
        } else {
            vec![format!(
                "{}: expected rejection with {} and {:?}, observed {:?} (exit success: {}):\n{}",
                file, code, fragment, observed, outcome.success, outcome.output
            )]
        }
    });
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
