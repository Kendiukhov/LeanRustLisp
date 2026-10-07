//! Regression tests for problems found by the second verification round of the JOT revision:
//!
//! * references stored in data (a constructor field, a type argument such as
//!   `Pair Nat (Ref Shared T)`, or a closure stored in a field) used to lose their loans in the
//!   MIR borrow checker: the owner could be moved, mutably borrowed again, or dropped while the
//!   data structure still held the reference;
//! * the dynamic backend jumped to the wrong arm for constructor index 2 and above (the switch
//!   re-read the discriminant number as a `Nat` scrutinee), silently miscomputing every match on
//!   a type with three or more constructors;
//! * compiled code evaluated proofs: an elimination of a proof holding data panicked at run time
//!   (the proof itself had been erased to `()`), and MIR rejected programs whose proof terms
//!   mention values the kernel (which never visits proofs) considers unused;
//! * the `affine` marker on a proposition was silently ignored (proofs are always Copy).
//!
//! Static checks use the real dynamic prelude stack through `process_code` (the path shared by
//! `run`, the REPL and `compile`); runtime checks compile with the CLI and run the binary.

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
        .name("loans-proofs-switch".to_string())
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
        "loans_proofs_switch_regressions.lrl",
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

fn assert_rejected_with(source: &str, code: &str, needle: &str) {
    let errors = errors_for(source);
    assert!(
        errors
            .iter()
            .any(|e| e.starts_with(&format!("[{}]", code)) && e.contains(needle)),
        "expected a {} error mentioning {:?}, got:\n{}",
        code,
        needle,
        errors.join("\n")
    );
}

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_loans_proofs_switch_{}_{}_{}",
        prefix,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

/// Compiles `source` with `cli compile --backend <backend>` and runs the binary. Returns the
/// compiler's success, the binary's success, and the binary's stdout followed by its stderr.
fn compile_and_run(prefix: &str, source: &str, backend: &str) -> (bool, bool, String) {
    let dir = unique_temp_dir(prefix);
    let file = dir.join(format!("{}.lrl", prefix));
    let bin = dir.join(format!("{}_{}", prefix, backend));
    fs::write(&file, source).expect("write program");
    let compile = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args([
            "compile",
            file.to_str().expect("utf-8 path"),
            "--backend",
            backend,
            "-o",
            bin.to_str().expect("utf-8 path"),
        ])
        .output()
        .expect("run cli compile");
    let compiled = compile.status.success() && bin.exists();
    let (ran, output) = if compiled {
        let run = Command::new(&bin).output().expect("run compiled binary");
        (
            run.status.success(),
            format!(
                "{}{}",
                String::from_utf8_lossy(&run.stdout),
                String::from_utf8_lossy(&run.stderr)
            ),
        )
    } else {
        (
            false,
            format!(
                "{}{}",
                String::from_utf8_lossy(&compile.stdout),
                String::from_utf8_lossy(&compile.stderr)
            ),
        )
    };
    let _ = fs::remove_dir_all(&dir);
    (compiled, ran, output)
}

fn assert_runs_with(prefix: &str, source: &str, typed: &str, dynamic: &str) {
    for (backend, expected) in [("typed", typed), ("dynamic", dynamic)] {
        let (compiled, ran, output) = compile_and_run(prefix, source, backend);
        assert!(
            compiled && ran && output.contains(expected),
            "{} backend: expected {:?} (compiled={}, ran={}), output:\n{}",
            backend,
            expected,
            compiled,
            ran,
            output
        );
    }
}

// ---------------------------------------------------------------------------------------------
// References stored in data keep their loans (MIR borrow checker)
// ---------------------------------------------------------------------------------------------

const REFS: &str = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def burn (pi t Tok Nat) (lam t Tok (match t Nat (case (mk_tok n) n))))
(def look (pi r (Ref #[r] Shared Tok) Nat) (lam r (Ref #[r] Shared Tok) (succ zero)))
(def poke (pi r (Ref #[r] Mut Tok) Nat) (lam r (Ref #[r] Mut Tok) (succ zero)))
(inductive RB (sort 1) (ctor rb (pi r (Ref #[r] Shared Tok) RB)))
(inductive MB (sort 1) (ctor mb (pi r (Ref #[r] Mut Tok) MB)))
(def lookb (pi b RB Nat) (lam b RB (match b Nat (case (rb r) (look r)))))
(def pokeb (pi b MB Nat) (lam b MB (match b Nat (case (mb r) (poke r)))))
(inductive FBox (sort 1) (ctor fbox (pi g (pi u Nat Nat) FBox)))
(def callb (pi b FBox Nat) (lam b FBox (match b Nat (case (fbox g) (g zero)))))
"#;

fn with_refs(body: &str) -> String {
    format!("{}\n{}", REFS, body)
}

/// Moving the owner while a structure holding a shared reference to it is still used: `M201`
/// (the loan used to end when the structure was built).
#[test]
fn reference_stored_in_a_constructor_keeps_its_loan() {
    assert_rejected_with(
        &with_refs(
            r#"
(def f (pi t Tok Nat)
  (lam t Tok (let b RB (rb (& t)) (let n Nat (burn t) (add n (lookb b))))))
"#,
        ),
        "M201",
        "borrowed as Shared",
    );
    // The same when the structure is returned by a function given the reference.
    assert_rejected_with(
        &with_refs(
            r#"
(def wrap (pi r (Ref #[r] Shared Tok) RB) (lam r (Ref #[r] Shared Tok) (rb r)))
(def f (pi t Tok Nat)
  (lam t Tok (let b RB (wrap (& t)) (let n Nat (burn t) (add n (lookb b))))))
"#,
        ),
        "M201",
        "borrowed as Shared",
    );
}

/// The same through a type argument (`Pair Nat (Ref Shared Tok)`) and through a list.
#[test]
fn reference_stored_through_a_type_argument_keeps_its_loan() {
    assert_rejected_with(
        &with_refs(
            r#"
(def f (pi t Tok Nat)
  (lam t Tok (let p (Pair Nat (Ref #[r] Shared Tok)) (mk_pair zero (& t))
    (let n Nat (burn t) (add n (match p Nat (case (mk_pair a b) (look b))))))))
"#,
        ),
        "M201",
        "borrowed as Shared",
    );
    assert_rejected_with(
        &with_refs(
            r#"
(def f (pi t Tok Nat)
  (lam t Tok (let l (List (Ref #[r] Shared Tok)) (cons (& t) nil)
    (let n Nat (burn t) (add n (match l Nat (case (nil) zero) (case (cons h tl ih) (look h))))))))
"#,
        ),
        "M201",
        "borrowed as Shared",
    );
}

/// A closure that captures a reference, stored in a structure: the structure holds the loan.
#[test]
fn closure_capturing_a_reference_stored_in_a_constructor_keeps_its_loan() {
    assert_rejected_with(
        &with_refs(
            r#"
(def f (pi t Tok Nat)
  (lam t Tok (let r (Ref #[r] Shared Tok) (& t)
    (let b FBox (fbox (lam u Nat (add u (look r))))
      (let n Nat (burn t) (add n (callb b)))))))
"#,
        ),
        "M201",
        "borrowed as Shared",
    );
}

/// Two live mutable borrows held by two structures, and a mutable borrow held by a structure
/// next to a shared borrow: `M200`.
#[test]
fn mutable_references_stored_in_constructors_conflict() {
    assert_rejected_with(
        &with_refs(
            r#"
(def f (pi t Tok Nat)
  (lam t Tok (let a MB (mb (&mut t)) (let b MB (mb (&mut t)) (add (pokeb a) (pokeb b))))))
"#,
        ),
        "M200",
        "already borrowed as Mut",
    );
    assert_rejected_with(
        &with_refs(
            r#"
(def f (pi t Tok Nat)
  (lam t Tok (let a MB (mb (&mut t)) (let r (Ref #[r] Shared Tok) (& t) (add (look r) (pokeb a))))))
"#,
        ),
        "M200",
        "already borrowed as Mut",
    );
}

/// A structure holding a reference to a parameter (directly, or through a captured reference
/// in a stored closure) may not be returned: `M203` (this was accepted by the original
/// compiler as well).
#[test]
fn reference_stored_in_a_constructor_may_not_escape() {
    assert_rejected_with(
        &with_refs("(def leak (pi t Tok RB) (lam t Tok (rb (& t))))"),
        "M203",
        "does not live long enough",
    );
    assert_rejected_with(
        &with_refs("(def mk (pi t Tok FBox) (lam t Tok (fbox (lam u Nat (add u (look (& t)))))))"),
        "M203",
        "does not live long enough",
    );
}

/// Positive controls: the loan ends with the last use of the structure; values that cannot hold
/// a reference (`Option Nat`, a capture-free closure, a `Nat` computed from a reference) hold no
/// loan; several shared references may be stored at once.
#[test]
fn loans_held_by_data_end_with_the_data() {
    let source = with_refs(
        r#"
(def f1 (pi t Tok Nat)
  (lam t Tok (let b RB (rb (& t)) (let n Nat (lookb b) (add n (burn t))))))
(def lookup (pi r (Ref #[r] Shared Tok) (Option Nat)) (lam r (Ref #[r] Shared Tok) (some (look r))))
(def f2 (pi t Tok Nat)
  (lam t Tok (let o (Option Nat) (lookup (& t))
    (let n Nat (burn t) (add n (match o Nat (case (none) zero) (case (some x) x)))))))
(def f3 (pi t Tok Nat)
  (lam t Tok (let b FBox (fbox (lam u Nat (succ u))) (let n Nat (burn t) (add n (callb b))))))
(def f4 (pi t Tok Nat)
  (lam t Tok (let a RB (rb (& t)) (let b RB (rb (& t)) (add (add (lookb a) (lookb b)) (burn t))))))
(inductive NB (sort 1) (ctor nb (pi n Nat (pi g (pi u Nat Nat) NB))))
(def getn (pi b NB Nat) (lam b NB (match b Nat (case (nb n g) (g n)))))
(def f5 (pi t Tok Nat)
  (lam t Tok (let b NB (nb (look (& t)) succ) (let n Nat (burn t) (add n (getn b))))))
(def main Nat (add (f1 (mk_tok 2)) (add (f2 (mk_tok 2)) (add (f3 (mk_tok 2)) (add (f4 (mk_tok 2)) (f5 (mk_tok 2)))))))
"#,
    );
    assert_accepted(&source);
    // 3 + 3 + 3 + 4 + 4
    assert_runs_with("loans_end", &source, "Result: 17", "Result: Nat(17)");
}

/// A function may return a structure holding the reference it was given: the loan belongs to
/// the caller, so there is no "does not live long enough" (static check only: the typed backend
/// cannot yet pass `List (Ref ...)` type arguments).
#[test]
fn structure_holding_a_parameter_reference_may_be_returned() {
    assert_accepted(&with_refs(
        r#"
(def wrap2 (pi r (Ref #[r] Shared Tok) (List (Ref #[r] Shared Tok)))
  (lam r (Ref #[r] Shared Tok) (cons r (cons r nil))))
(def g (pi t Tok Nat)
  (lam t Tok (let l (List (Ref #[r] Shared Tok)) (wrap2 (& t))
    (let n Nat (match l Nat (case (nil) zero) (case (cons h tl ih) (look h))) (add n (burn t))))))
"#,
    ));
}

// ---------------------------------------------------------------------------------------------
// Dynamic backend: switch on the constructor index
// ---------------------------------------------------------------------------------------------

/// Constructor indices 2 and above used to jump to arm 1 in the dynamic backend
/// (`code blue + code green + code red` was 5 instead of 6).
#[test]
fn dynamic_backend_dispatches_on_every_constructor_index() {
    let source = r#"
(inductive Color (sort 1) (ctor red Color) (ctor green Color) (ctor blue Color))
(def code (pi c Color Nat) (lam c Color (match c Nat (case (red) 1) (case (green) 2) (case (blue) 3))))
(inductive Ch (sort 1) (ctor enda Ch) (ctor endb Ch) (ctor step (pi r Ch Ch)))
(def depth (pi c Ch Nat)
  (lam c Ch (match c Nat (case (enda) 5) (case (endb) zero) (case (step r ih) (succ ih)))))
(def main Nat (add (add (code blue) (add (code green) (code red))) (depth (step (step endb)))))
"#;
    assert_runs_with("switch_index", source, "Result: 8", "Result: Nat(8)");
}

// ---------------------------------------------------------------------------------------------
// Proofs are not evaluated by compiled code
// ---------------------------------------------------------------------------------------------

const HOLDS: &str = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def burn (pi t Tok Nat) (lam t Tok (match t Nat (case (mk_tok n) n))))
(inductive Tru (sort 0) (ctor triv Tru))
(inductive Holds (sort 0) (ctor hold (pi t Tok Holds)))
"#;

/// Eliminating a proof that stores data (into `Prop`) used to be compiled: the dynamic binary
/// panicked ("Field access on unsupported runtime value": the proof was erased to `()`), the
/// typed backend refused it (`TB005`). The elimination is a proof, so it is not run.
#[test]
fn eliminating_a_data_carrying_proof_is_not_run() {
    let source = format!(
        "{}{}",
        HOLDS,
        r#"
(def f (pi p Holds Nat) (lam p Holds
  (let a Tru (match p Tru (case (hold x) (let n Nat (burn x) triv)))
    (let b Tru (match p Tru (case (hold x) (let n Nat (burn x) triv))) 4))))
(def main Nat (f (hold (mk_tok 2))))
"#
    );
    assert_accepted(&source);
    assert_runs_with("proof_elim", &source, "Result: 4", "Result: Nat(4)");
}

/// A value mentioned only inside proof terms is not consumed (kernel), and MIR no longer
/// evaluates those proof terms, so it agrees (this used to be `M100` "use of moved value").
#[test]
fn values_used_only_inside_proofs_are_not_moved() {
    let source = format!(
        "{}{}",
        HOLDS,
        r#"
(def keep (pi A (sort 1) (pi x A (pi #[once] p (Eq A x x) A)))
  (lam A (sort 1) (lam x A (lam #[once] p (Eq A x x) x))))
(def use_keep (pi A (sort 1) (pi x A A))
  (lam A (sort 1) (lam x A (keep A x (refl A x)))))
(def stash (pi t Tok Nat) (lam t Tok (let p Holds (hold t) (burn t))))
(def main Nat (stash (mk_tok 3)))
"#
    );
    assert_accepted(&source);
    assert_runs_with("proof_values", &source, "Result: 3", "Result: Nat(3)");
}

// ---------------------------------------------------------------------------------------------
// The affine marker
// ---------------------------------------------------------------------------------------------

/// Proofs are always Copy, so `affine` on an inductive in `Prop` would be silently ignored: it
/// is rejected (`K0052`).
#[test]
fn affine_marker_is_rejected_on_a_proposition() {
    assert_rejected_with(
        r#"
(inductive (affine) Perm (sort 0) (ctor grant Perm))
"#,
        "K0052",
        "affine",
    );
}
