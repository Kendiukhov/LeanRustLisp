//! End-to-end tests for surface `match` with an explicit dependent motive,
//! `(match e (motive M) (case ...) ...)` (docs/spec/syntax_contract_0_1.md, "(match ...)"), and
//! for definitions whose body is a bare constructor (`(def z Nat zero)`), which used to be
//! admitted but then unresolvable ("Unbound variable").
//!
//! Every program is run through the real CLI from the repository root: `run --backend typed`
//! (kernel, MIR, typed Rust backend, execution of `main`) or `compile --backend dynamic` and the
//! produced binary. Programs whose typed Rust output is not accepted by rustc (large eliminations,
//! generic proof constructors; see the comments) are checked with the dynamic backend.

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

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_dependent_match_{}_{}_{}",
        prefix,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

struct CliRun {
    success: bool,
    stdout: String,
    stderr: String,
}

/// Runs `cli <args...>` from the repository root on a temporary copy of `source` (`{file}` and
/// `{out}` in `args` are replaced by the source path and an output binary path). If the command
/// succeeds and produced the output binary, the binary is run and its stdout appended.
fn run_cli(prefix: &str, source: &str, args: &[&str]) -> CliRun {
    let dir = unique_temp_dir(prefix);
    let path = dir.join(format!("{}.lrl", prefix));
    fs::write(&path, source).expect("write program");
    let out = dir.join("out_bin");
    let full_args: Vec<String> = args
        .iter()
        .map(|arg| match *arg {
            "{file}" => path.to_string_lossy().to_string(),
            "{out}" => out.to_string_lossy().to_string(),
            other => other.to_string(),
        })
        .collect();
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args(&full_args)
        .output()
        .expect("run cli");
    let mut stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    if output.status.success() && out.exists() {
        let run = Command::new(&out).output().expect("run compiled binary");
        stdout.push_str(&String::from_utf8_lossy(&run.stdout));
    }
    let _ = fs::remove_dir_all(&dir);
    CliRun {
        success: output.status.success(),
        stdout,
        stderr,
    }
}

fn run_typed(prefix: &str, source: &str) -> CliRun {
    run_cli(prefix, source, &["run", "{file}", "--backend", "typed"])
}

fn compile_dynamic(prefix: &str, source: &str) -> CliRun {
    run_cli(
        prefix,
        source,
        &["compile", "{file}", "--backend", "dynamic", "-o", "{out}"],
    )
}

fn assert_output(run: &CliRun, expected_line: &str) {
    assert!(
        run.success && run.stdout.lines().any(|line| line.trim() == expected_line),
        "expected success and a line `{}`;\nstdout:\n{}\nstderr:\n{}",
        expected_line,
        run.stdout,
        run.stderr
    );
}

fn assert_rejected_with(run: &CliRun, code: &str, fragment: &str) {
    let all = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !run.success && all.contains(code) && all.contains(fragment),
        "expected a failure with {} mentioning `{}`;\nstdout:\n{}\nstderr:\n{}",
        code,
        fragment,
        run.stdout,
        run.stderr
    );
}

const VEC: &str = r#"
(inductive Vec (pi A (sort 1) (pi n Nat (sort 1)))
  (ctor vnil (pi {A (sort 1)} (Vec A zero)))
  (ctor vcons (pi {A (sort 1)} (pi {n Nat} (pi h A (pi t (Vec A n) (Vec A (succ n))))))))
"#;

// ---------------------------------------------------------------------------------------------
// Bare-constructor definitions
// ---------------------------------------------------------------------------------------------

/// `(def z Nat zero)` and `(def fav Color green)` are ordinary definitions that later code can
/// refer to (they used to be skipped by name resolution, as if they were constructor aliases).
#[test]
fn bare_constructor_definitions_are_referenceable() {
    let source = r#"
(inductive Color (sort 1) (ctor red Color) (ctor green Color))
(def z Nat zero)
(def t Bool true)
(def fav Color green)
(def code (pi c Color Nat) (lam c Color (match c Nat (case (red) 1) (case (green) 2))))
(def two Nat (succ (succ z)))
(def main Nat (add (code fav) (match t Nat (case (true) two) (case (false) z))))
"#;
    assert_output(&run_typed("bare_ctor", source), "Result: 4");
}

// ---------------------------------------------------------------------------------------------
// Dependent motives
// ---------------------------------------------------------------------------------------------

/// A total `head` on `Vec A (succ n)`: the motive computes `Unit` for an empty vector and `A`
/// for a non-empty one, so the impossible `vnil` case returns a unit value and no runtime check
/// is needed. (The typed backend cannot give the recursor of this large elimination a Rust
/// type, so the program is compiled with the dynamic backend.)
#[test]
fn total_vector_head_with_a_dependent_motive_runs() {
    let source = format!(
        r#"
(inductive Unit (sort 1) (ctor unit Unit))
{VEC}
(def head (pi {{A (sort 1)}} (pi {{n Nat}} (pi v (Vec A (succ n)) A)))
  (lam {{A}} (sort 1) (lam {{n}} Nat (lam v (Vec A (succ n))
    (match v (motive (lam k Nat (lam w (Vec A k)
                       (match k (sort 1) (case (zero) Unit) (case (succ k1 ih) A)))))
      (case (vnil) unit)
      (case (vcons h t ih) h))))))
(def main Nat (head (vcons 7 (vcons 8 vnil))))
"#
    );
    assert_output(&compile_dynamic("vec_head", &source), "Result: Nat(7)");
}

/// Append on length-indexed vectors whose result length is `add n m`: each case type-checks by
/// computation of `add` (`add zero m = m`, `add (succ k) m = succ (add k m)`), and the
/// induction hypothesis has type `Vec A (add k m)`.
#[test]
fn vector_append_indexed_by_add_runs_in_both_backends() {
    let source = format!(
        r#"
{VEC}
(def vappend (pi {{A (sort 1)}} (pi {{n Nat}} (pi {{m Nat}}
               (pi xs (Vec A n) (pi #[once] ys (Vec A m) (Vec A (add n m)))))))
  (lam {{A}} (sort 1) (lam {{n}} Nat (lam {{m}} Nat (lam xs (Vec A n) (lam #[once] ys (Vec A m)
    (match xs (motive (lam k Nat (lam w (Vec A k) (Vec A (add k m)))))
      (case (vnil) ys)
      (case (vcons h t ih) (vcons h ih)))))))))
(def vsum (pi {{n Nat}} (pi v (Vec Nat n) Nat))
  (lam {{n}} Nat (lam v (Vec Nat n)
    (match v Nat (case (vnil) zero) (case (vcons h t ih) (add h ih))))))
(def main Nat (vsum (vappend (vcons 1 (vcons 2 vnil)) (vcons 3 (vcons 4 vnil)))))
"#
    );
    assert_output(&run_typed("vec_append", &source), "Result: 10");
    assert_output(&compile_dynamic("vec_append", &source), "Result: Nat(10)");
}

/// A proof by induction, `add n zero = n`, and the congruence lemma it uses, both written as
/// matches with dependent motives (`cong` matches on the equality proof, with a motive over its
/// index). (Generic proof constructors are not yet supported by the typed backend, so the
/// program is compiled with the dynamic backend.)
#[test]
fn proof_by_induction_with_a_dependent_motive_is_checked_and_runs() {
    let source = r#"
(def cong (pi {A (sort 1)} (pi {B (sort 1)} (pi f (pi x A B)
            (pi {x A} (pi {y A} (pi e (Eq A x y) (Eq B (f x) (f y))))))))
  (lam {A} (sort 1) (lam {B} (sort 1) (lam f (pi x A B) (lam {x} A (lam {y} A (lam e (Eq A x y)
    (match e (motive (lam b A (lam w (Eq A x b) (Eq B (f x) (f b)))))
      (case (refl) (refl B (f x)))))))))))
(def add_zero_right (pi n Nat (Eq Nat (add n zero) n))
  (lam n Nat
    (match n (motive (lam k Nat (Eq Nat (add k zero) k)))
      (case (zero) (refl Nat zero))
      (case (succ k ih) (cong succ ih)))))
(def two_plus_zero (Eq Nat (add 2 zero) 2) (add_zero_right 2))
(def main Nat (add 2 zero))
"#;
    assert_output(&compile_dynamic("add_zero_proof", source), "Result: Nat(2)");
}

/// Each case is checked against the motive at its constructor: a wrong proof in the `zero`
/// case is a unification error.
#[test]
fn case_bodies_are_checked_against_the_motive_at_their_constructor() {
    let source = r#"
(def bad (pi n Nat (Eq Nat (add n zero) n))
  (lam n Nat
    (match n (motive (lam k Nat (Eq Nat (add k zero) k)))
      (case (zero) (refl Nat 1))
      (case (succ k ih) (refl Nat (succ k))))))
"#;
    assert_rejected_with(
        &run_typed("bad_case", source),
        "F0214",
        "(Eq Nat (Nat.succ Nat.zero) (Nat.succ Nat.zero)) vs (Eq Nat Nat.zero Nat.zero)",
    );
}

/// The motive must abstract over the scrutinee type's indices and the scrutinee.
#[test]
fn motive_without_the_index_binder_is_rejected() {
    let source = format!(
        r#"
{VEC}
(def bad (pi {{n Nat}} (pi v (Vec Nat n) Nat))
  (lam {{n}} Nat (lam v (Vec Nat n)
    (match v (motive (lam w (Vec Nat n) Nat))
      (case (vnil) zero)
      (case (vcons h t ih) h)))))
"#
    );
    assert_rejected_with(
        &run_typed("bad_motive", &source),
        "F0205",
        "expected a match motive over 1 index argument(s) and the scrutinee",
    );
}

#[test]
fn motive_clause_takes_exactly_one_term() {
    let source = r#"
(def bad (pi n Nat Nat)
  (lam n Nat (match n (motive (lam k Nat Nat) extra) (case (zero) zero) (case (succ k ih) k))))
"#;
    assert_rejected_with(
        &run_typed("motive_arity", source),
        "F0102",
        "Expected (motive M) with exactly one motive term",
    );
}

/// The constant-motive form is unchanged: a dependent result type is not inferred from it.
#[test]
fn constant_motive_form_is_unchanged() {
    let ok = r#"
(def pred (pi n Nat Nat) (lam n Nat (match n Nat (case (zero) zero) (case (succ k ih) k))))
(def main Nat (pred 5))
"#;
    assert_output(&run_typed("const_motive", ok), "Result: 4");
    let dependent_without_motive = r#"
(def bad (pi n Nat (Eq Nat (add n zero) n))
  (lam n Nat
    (match n (Eq Nat (add n zero) n)
      (case (zero) (refl Nat zero))
      (case (succ k ih) (refl Nat (succ k))))))
"#;
    assert_rejected_with(
        &run_typed("const_motive_dep", dependent_without_motive),
        "F0214",
        "Unification failed",
    );
}
