//! End-to-end regression tests for the MIR side of recursor elimination and indexed families:
//!
//! * MIR types erase the indices of indexed families (docs/spec/mir/typing.md), so values of
//!   `Vec A n`, `Fin n` and equality proofs pass MIR typing (they used to fail with `M300`);
//! * a minor premise of a recursive constructor that only reads (calls) a captured `Fn`
//!   function value is a `Copy` closure (it captures the function by shared reference), so it
//!   can be passed to the recursive call and then called (it used to fail with `M100`);
//!   mutable and consuming captures keep it non-Copy;
//! * the minor premises of a non-recursive inductive are alternatives, lowered inside their own
//!   switch arm: only the branch that is taken runs;
//! * an arm whose constructor indices clash with the scrutinee's indices is unreachable.
//!
//! Programs are processed with the real dynamic prelude stack through `process_code` (the path
//! shared by `run`, the REPL and `compile`); a few are also executed with `run --backend typed`.

use cli::driver::{module_id_for_source, process_code, PipelineOptions};
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;
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

fn load_dynamic_prelude(env: &mut Env, expander: &mut Expander) {
    let root = repo_root();
    let options = PipelineOptions {
        allow_axioms: true,
        ..Default::default()
    };
    let mut modules = Vec::new();
    env.set_allow_reserved_primitives(true);
    for relative in cli::compiler::prelude_stack_for_backend(cli::compiler::BackendMode::Dynamic) {
        let path = root.join(relative);
        let content = fs::read_to_string(&path).expect("prelude file must exist");
        let path_str = path.to_string_lossy().to_string();
        let module_id = module_id_for_source(&path_str);
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        cli::set_prelude_macro_boundary_allowlist(expander, &module_id);
        if !modules.is_empty() {
            expander.set_default_imports(modules.clone());
        }
        let mut diagnostics = DiagnosticCollector::new();
        let _ = process_code(
            &content,
            &path_str,
            env,
            expander,
            &options,
            &mut diagnostics,
        );
        expander.clear_macro_boundary_allowlist();
        assert!(
            !diagnostics.has_errors(),
            "prelude '{}' failed to load",
            relative
        );
        modules.push(module_id);
    }
    env.set_allow_reserved_primitives(false);
    expander.set_default_imports(modules);
}

/// Error diagnostics (`[code] message`) reported for `source`. Runs on a thread with a large
/// stack: elaborating the full prelude in a debug build needs more than the default test stack.
fn errors_for(source: &str) -> Vec<String> {
    let source = source.to_string();
    std::thread::Builder::new()
        .name("mir-recursor-lowering".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || errors_for_on_current_thread(&source))
        .expect("spawn test thread")
        .join()
        .expect("test thread panicked")
}

fn errors_for_on_current_thread(source: &str) -> Vec<String> {
    let mut env = Env::new();
    let mut expander = Expander::new();
    load_dynamic_prelude(&mut env, &mut expander);
    let options = PipelineOptions {
        prelude_frozen: true,
        allow_axioms: true,
        ..Default::default()
    };
    let mut diagnostics = DiagnosticCollector::new();
    let _ = process_code(
        source,
        "mir_recursor_lowering.lrl",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );
    diagnostics
        .diagnostics
        .iter()
        .filter(|diag| diag.level == Level::Error)
        .map(|diag| format!("[{}] {}", diag.code.unwrap_or("-"), diag.message))
        .collect()
}

fn assert_accepted(source: &str) {
    let errors = errors_for(source);
    assert!(
        errors.is_empty(),
        "expected the program to be accepted, got:\n{}",
        errors.join("\n")
    );
}

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_mir_recursor_lowering_{}_{}_{}",
        prefix,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

/// Runs `source` with `cli run <file> --backend typed` (which compiles and executes `main`)
/// and returns (success, stdout, stderr).
fn run_typed(prefix: &str, source: &str) -> (bool, String, String) {
    let dir = unique_temp_dir(prefix);
    let file = dir.join(format!("{}.lrl", prefix));
    fs::write(&file, source).expect("write program");
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args([
            "run",
            file.to_str().expect("utf-8 path"),
            "--backend",
            "typed",
        ])
        .output()
        .expect("run cli");
    let _ = fs::remove_dir_all(&dir);
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

// ---------------------------------------------------------------------------------------------
// Indexed families (MIR types erase indices)
// ---------------------------------------------------------------------------------------------

const NVEC: &str = r#"
(inductive NVec (pi n Nat (sort 1))
  (ctor nnil (NVec zero))
  (ctor ncons (pi n Nat (pi h Nat (pi t (NVec n) (NVec (succ n)))))))
"#;

/// The repository's golden `vlen` (cli/tests/golden/mir/lowering/recursor_vec.lrl) plus a
/// count that uses the induction hypothesis; both used to fail MIR typing with `M300`
/// ("expected NVec [IndexTerm(Var(1))], got NVec [IndexTerm(Var(0))]").
#[test]
fn indexed_family_match_passes_mir_typing_and_runs() {
    let source = format!(
        "{}{}",
        NVEC,
        r#"
(def vlen (pi n Nat (pi v (NVec n) Nat))
  (lam n Nat (lam v (NVec n)
    (match v Nat
      (case (nnil) zero)
      (case (ncons n h t ih) zero)))))
(def vcount (pi n Nat (pi v (NVec n) Nat))
  (lam n Nat (lam v (NVec n)
    (match v Nat
      (case (nnil) zero)
      (case (ncons k h t ih) (succ ih))))))
(def main Nat (vcount (succ (succ zero)) (ncons (succ zero) 5 (ncons zero 7 nnil))))
"#
    );
    assert_accepted(&source);
    let (ok, stdout, stderr) = run_typed("vcount", &source);
    assert!(
        ok && stdout.contains("Result: 2"),
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

/// A length-indexed vector whose `vcons` has an implicit field `{n Nat}`. Besides the index
/// mismatch (`M300`), the recursor lowering used to skip implicit constructor binders, so the
/// fields passed to the minor premise were misaligned with the runtime layout and the
/// minor's binders ("expected Vec ..., got Nat").
#[test]
fn indexed_family_with_implicit_fields_runs() {
    let source = r#"
(inductive Vec (pi A (sort 1) (pi n Nat (sort 1)))
  (ctor vnil (pi {A (sort 1)} (Vec A zero)))
  (ctor vcons (pi {A (sort 1)} (pi {n Nat} (pi h A (pi t (Vec A n) (Vec A (succ n))))))))
(def vhead (pi n Nat (pi v (Vec Nat (succ n)) Nat))
  (lam n Nat (lam v (Vec Nat (succ n))
    (match v Nat
      (case (vnil) zero)
      (case (vcons h t ih) h)))))
(def vsum (pi n Nat (pi v (Vec Nat n) Nat))
  (lam n Nat (lam v (Vec Nat n)
    (match v Nat
      (case (vnil) zero)
      (case (vcons h t ih) (add h ih))))))
(def main Nat
  (add (vhead (succ zero) (vcons 4 (vcons 9 vnil)))
       (vsum (succ (succ zero)) (vcons 4 (vcons 9 vnil)))))
"#;
    assert_accepted(source);
    let (ok, stdout, stderr) = run_typed("vhead", source);
    assert!(
        ok && stdout.contains("Result: 17"),
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

/// Equality proofs (an indexed family in Prop): congruence by the `Eq` recursor and its use
/// in an inductive proof. Used to fail MIR typing (`M300`); the erased single-constructor
/// proof is now matched without reading a discriminant (the typed backend could not read
/// the discriminant of an erased value: `TB900`).
#[test]
fn equality_proofs_pass_mir_and_run() {
    let source = r#"
(def cong_l
  (pi f (pi x (List Nat) (List Nat)) (pi x (List Nat) (pi y (List Nat) (pi e (Eq (List Nat) x y) (Eq (List Nat) (f x) (f y))))))
  (lam f (pi x (List Nat) (List Nat)) (lam x (List Nat) (lam y (List Nat) (lam e (Eq (List Nat) x y)
    ((rec Eq) (List Nat) x
      (lam y2 (List Nat) (lam e2 (Eq (List Nat) x y2) (Eq (List Nat) (f x) (f y2))))
      (refl (List Nat) (f x))
      y e))))))
(def main Nat zero)
"#;
    assert_accepted(source);
    let (ok, stdout, stderr) = run_typed("cong", source);
    assert!(
        ok && stdout.contains("Result: 0"),
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

/// A large elimination whose motive computes `Unit` at index `zero` and `Nat` at `succ k`:
/// the `nnil` arm of a scrutinee of type `NVec (succ n)` is unreachable (its index `zero`
/// clashes with `succ n`) and is pruned, so its `Unit` result no longer fails MIR typing
/// against the `Nat` destination ("expected Nat, got Adt(Unit)").
#[test]
fn large_elimination_impossible_arm_is_pruned() {
    let source = format!(
        "{}{}",
        NVEC,
        r#"
(inductive copy Unit (sort 1) (ctor unit Unit))
(def HeadTy (pi k Nat (sort 1))
  (lam k Nat (match k (sort 1) (case (zero) Unit) (case (succ j ih) Nat))))
(def nhead (pi n Nat (pi v (NVec (succ n)) Nat))
  (lam n Nat
    (lam v (NVec (succ n))
      ((rec NVec)
        (lam k Nat (lam w (NVec k) (HeadTy k)))
        unit
        (lam k Nat (lam h Nat (lam t (NVec k) (lam ih (HeadTy k) h))))
        (succ n) v))))
"#
    );
    assert_accepted(&source);
}

// ---------------------------------------------------------------------------------------------
// Minor premises of recursive constructors (Copy closures)
// ---------------------------------------------------------------------------------------------

/// The succ case calls (reads) a captured `Fn` function on every iteration. The minor
/// captures it by shared reference and is Copy, so the recursor lowering passes it to the
/// recursive call without moving it. Used to fail with `M100` ("use of moved value").
#[test]
fn recursive_minor_reading_captured_function_runs() {
    let source = r#"
(def iter (pi f (pi x Nat Nat) (pi #[once] n Nat Nat))
  (lam f (pi x Nat Nat) (lam #[once] n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m ih) (f ih))))))
(def main Nat (iter (lam x Nat (succ (succ x))) (succ (succ (succ zero)))))
"#;
    assert_accepted(source);
    let (ok, stdout, stderr) = run_typed("iter", source);
    assert!(
        ok && stdout.contains("Result: 6"),
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

/// Calling a captured `FnMut` function is a mutable use: the minor captures it by mutable
/// reference or by move, stays non-Copy, and MIR still rejects passing it to the recursive
/// call and then calling it.
#[test]
fn recursive_minor_mutating_captured_function_stays_rejected() {
    let errors = errors_for(
        r#"
(def iter_mut (pi #[mut] f (pi #[mut] x Nat Nat) (pi #[once] n Nat Nat))
  (lam #[mut] f (pi #[mut] x Nat Nat) (lam #[once] n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m ih) (f ih))))))
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.starts_with("[M100]") && e.contains("iter_mut")),
        "expected a MIR ownership error (M100), got:\n{}",
        errors.join("\n")
    );
}

// ---------------------------------------------------------------------------------------------
// Non-recursive inductives: minors are alternatives
// ---------------------------------------------------------------------------------------------

/// Only the branch that is taken may run. Both branches print; before, both minors were
/// evaluated before the switch, so `pick true` printed `1` and `2`.
#[test]
fn non_recursive_match_runs_only_the_taken_branch() {
    let source = r#"
(def pick (pi b Bool Nat)
  (lam b Bool
    (match b Nat
      (case (true) (print_nat (succ zero)))
      (case (false) (print_nat (succ (succ zero)))))))
(def main Nat (pick true))
"#;
    assert_accepted(source);
    let (ok, stdout, stderr) = run_typed("pick", source);
    let printed: Vec<&str> = stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .filter(|line| !line.starts_with("Result") && !line.starts_with("Compil"))
        .collect();
    assert!(
        ok && printed == vec!["1"] && stdout.contains("Result: 1"),
        "expected only the taken branch to print\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

/// A match on `Option` whose `some` case is a λ over the field: the minor is inlined in its
/// arm (no closure) and the program still computes the right value.
#[test]
fn non_recursive_lambda_minor_is_inlined_and_runs() {
    let source = r#"
(def get_or (pi d Nat (pi o (Option Nat) Nat))
  (lam d Nat (lam o (Option Nat)
    (match o Nat
      (case (none) d)
      (case (some v) (succ v))))))
(def main Nat (add (get_or 3 (some 4)) (get_or 3 none)))
"#;
    assert_accepted(source);
    let (ok, stdout, stderr) = run_typed("get_or", source);
    assert!(
        ok && stdout.contains("Result: 8"),
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

// ---------------------------------------------------------------------------------------------
// Fixpoints capturing outer variables
// ---------------------------------------------------------------------------------------------

/// A `fix` whose body captures an outer function value. Lowering used to rebuild the body as a
/// fresh `(shift body) arg` term whose closures had no span/capture metadata ("Missing closure
/// span metadata ... while lowering capturing closure"); the dynamic backend's fixpoint code
/// did not compile (`Value::Func` applied to a `Weak`) and the typed backend required a self
/// slot in the environment of capture-free fixpoints.
#[test]
fn fixpoint_capturing_outer_function_runs() {
    let source = r#"
(def is_zero (pi n Nat Bool)
  (lam n Nat (match n Bool (case (zero) true) (case (succ m ih) false))))
(def pred (pi n Nat Nat)
  (lam n Nat (match n Nat (case (zero) zero) (case (succ m ih) m))))
(partial count_print (pi f (pi x Nat Nat) (pi n Nat (Comp Nat)))
  (lam f (pi x Nat Nat)
    (fix go (pi n Nat (Comp Nat))
      (lam n Nat
        (match (is_zero n) (Comp Nat)
          (case (true) (ret Nat))
          (case (false) (let r Nat (f (pred n)) (go (pred n)))))))))
(partial main (Comp Nat) (count_print (lam x Nat (print_nat x)) (succ (succ (succ zero)))))
"#;
    assert_accepted(source);
    let (ok, stdout, stderr) = run_typed("count_print", source);
    let printed: Vec<&str> = stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .filter(|line| !line.starts_with("Result") && !line.starts_with("Compil"))
        .collect();
    assert!(
        ok && printed == vec!["2", "1", "0"],
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}
