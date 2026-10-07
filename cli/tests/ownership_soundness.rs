//! Regression tests for ownership soundness holes found while verifying the JOT revision changes.
//!
//! Each program is processed with the real dynamic prelude stack through `process_code` (the
//! path shared by `run`, the REPL and `compile`), and the test checks which stage rejects it:
//! kernel diagnostics carry `K` codes (`K0021` for ownership), MIR diagnostics `M` codes.

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
        .name("ownership-soundness".to_string())
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
        "ownership_soundness.lrl",
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

fn assert_kernel_rejects(source: &str, needle: &str) {
    let errors = errors_for(source);
    assert!(
        errors
            .iter()
            .any(|e| e.starts_with("[K0021]") && e.contains(needle)),
        "expected a kernel ownership error (K0021) mentioning {:?}, got:\n{}",
        needle,
        errors.join("\n")
    );
}

fn assert_no_kernel_error(source: &str) -> Vec<String> {
    let errors = errors_for(source);
    assert!(
        !errors.iter().any(|e| e.starts_with("[K")),
        "expected the kernel to accept the program, got:\n{}",
        errors.join("\n")
    );
    errors
}

fn assert_accepted(source: &str) {
    let errors = errors_for(source);
    assert!(
        errors.is_empty(),
        "expected the program to be accepted, got:\n{}",
        errors.join("\n")
    );
}

const TOK: &str = r#"
(inductive Tok (sort 1) (ctor mk_tok (pi f (pi x Nat Nat) Tok)))
(inductive TL (sort 1) (ctor tnil TL) (ctor tcons (pi h Tok (pi t TL TL))))
(def idn (pi x Nat Nat) (lam x Nat x))
"#;

fn with_tok(body: &str) -> String {
    format!("{}\n{}", TOK, body)
}

// ---------------------------------------------------------------------------------------------
// Copy derivation
// ---------------------------------------------------------------------------------------------

/// An index binder of a constructor is a stored field. It used to be treated as a parameter,
/// which made `W t` Copy although it holds a `Tok`.
#[test]
fn copy_derivation_counts_index_binders_as_fields() {
    let source = with_tok(
        r#"
(inductive W (pi t Tok (sort 1))
  (ctor mkw (pi t Tok (W t)))
  (ctor w2 (pi n Nat (pi t Tok (W t)))))
(def eat (pi #[once] w (W (mk_tok idn)) (pi #[once] k Nat Nat))
  (lam #[once] w (W (mk_tok idn)) (lam #[once] k Nat (succ k))))
(def dupw (pi #[once] w (W (mk_tok idn)) Nat)
  (lam #[once] w (W (mk_tok idn)) (eat w (eat w zero))))
"#,
    );
    assert_kernel_rejects(&source, "UseAfterMove");
}

/// Indexed families derive Copy from their parameters (indices do not matter): `Vec Nat n` is
/// Copy like `List Nat`; `Vec Tok n` is not.
#[test]
fn copy_derivation_supports_indexed_families() {
    let vec_decl = r#"
(inductive Vec (pi A (sort 1) (pi n Nat (sort 1)))
  (ctor vnil (pi {A (sort 1)} (Vec A zero)))
  (ctor vcons (pi {A (sort 1)} (pi {n Nat} (pi h A (pi t (Vec A n) (Vec A (succ n))))))))
"#;
    let copy_ok = with_tok(&format!(
        "{}\n{}",
        vec_decl,
        r#"
(inductive VP (sort 1) (ctor mk_vp (pi a (Vec Nat (succ zero)) (pi b (Vec Nat (succ zero)) VP))))
(def dupv (pi v (Vec Nat (succ zero)) VP) (lam v (Vec Nat (succ zero)) (mk_vp v v)))
"#
    ));
    assert_no_kernel_error(&copy_ok);

    let not_copy = with_tok(&format!(
        "{}\n{}",
        vec_decl,
        r#"
(inductive VQ (sort 1) (ctor mk_vq (pi a (Vec Tok (succ zero)) (pi b (Vec Tok (succ zero)) VQ))))
(def dupt (pi v (Vec Tok (succ zero)) VQ) (lam v (Vec Tok (succ zero)) (mk_vq v v)))
"#
    ));
    assert_kernel_rejects(&not_copy, "UseAfterMove");
}

// ---------------------------------------------------------------------------------------------
// Recursors: minor premises that may run more than once
// ---------------------------------------------------------------------------------------------

/// The succ case runs once per `succ`: it may not consume the captured token.
#[test]
fn recursive_case_may_not_consume_captured_value() {
    let source = with_tok(
        r#"
(def spread (pi k Tok (pi #[once] n Nat TL))
  (lam k Tok (lam #[once] n Nat
    (match n TL
      (case (zero) tnil)
      (case (succ m ih) (tcons k ih))))))
"#,
    );
    assert_kernel_rejects(&source, "ConsumedInRepeatedScope");
}

/// Same program produced by a macro, and as a top-level expression.
#[test]
fn recursive_case_capture_is_rejected_through_macros_and_expressions() {
    let via_macro = with_tok(
        r#"
(defmacro spread_on (k n) (match n TL (case (zero) tnil) (case (succ m ih) (tcons k ih))))
(def spread (pi k Tok (pi #[once] n Nat TL))
  (lam k Tok (lam #[once] n Nat (spread_on k n))))
"#,
    );
    assert_kernel_rejects(&via_macro, "ConsumedInRepeatedScope");

    let as_expression = with_tok(
        r#"
((lam k Tok (lam #[once] n Nat (match n TL (case (zero) tnil) (case (succ m ih) (tcons k ih)))))
  (mk_tok idn) (succ (succ zero)))
"#,
    );
    assert_kernel_rejects(&as_expression, "ConsumedInRepeatedScope");
}

/// A FnOnce closure passed (through the raw recursor) as a minor premise that runs repeatedly.
#[test]
fn repeated_minor_premise_must_be_a_lambda() {
    let source = with_tok(
        r#"
(def spread (pi k Tok (pi #[once] n Nat TL))
  (lam k Tok (lam #[once] n Nat
    (let f (pi #[once] m Nat (pi #[once] ih TL TL))
           (lam #[once] m Nat (lam #[once] ih TL (tcons k ih)))
      ((rec Nat) (lam z Nat TL) tnil f n)))))
"#,
    );
    assert_kernel_rejects(&source, "RepeatedMinorNotLambda");
}

/// The recursor consumes a non-Copy recursive field to compute its induction hypothesis, so the
/// minor premise may not use the field as well.
#[test]
fn non_copy_recursive_field_is_consumed_by_its_induction_hypothesis() {
    let source = with_tok(
        r#"
(inductive TQ (sort 1) (ctor qnil TQ) (ctor qcons (pi a TL (pi b TQ TQ))))
(def suffixes (pi l TL TQ)
  (lam l TL
    (match l TQ
      (case (tnil) qnil)
      (case (tcons h t ih) (qcons t ih)))))
"#,
    );
    assert_kernel_rejects(&source, "RecursiveFieldConsumedByIh");
}

/// A partially applied recursor is a function value that can be called many times: its
/// field-less minor premise (here a list holding the token) would be returned every time.
#[test]
fn partially_applied_recursor_reuses_minor_values() {
    let source = with_tok(
        r#"
(inductive TLP (sort 1) (ctor mk_tlp (pi a TL (pi b TL TLP))))
(def twice (pi k Tok TLP)
  (lam k Tok
    (let r (pi n Nat TL) ((rec Nat) (lam z Nat TL) (tcons k tnil) (lam m Nat (lam ih TL ih)))
      (mk_tlp (r zero) (r zero)))))
"#,
    );
    assert_kernel_rejects(&source, "RepeatedMinorValueNotCopy");
}

/// A recursor applied without its scrutinee holds minor-premise values built before any
/// dispatch, also for a non-recursive type: the kernel walks its minor premises in order, every
/// one repeatable (O-Rec-Seq), not as alternatives. Two field-less cases that consume the same
/// captured token were accepted by the kernel (only lowering rejected the partial application).
/// With the scrutinee supplied exactly one case runs, so the same two cases stay accepted.
#[test]
fn unsaturated_non_recursive_recursor_walks_minor_premises_in_order() {
    const AFFINE_TOK: &str = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def burn (pi t Tok Nat) (lam t Tok (match t Nat (case (mk_tok n) n))))
"#;
    assert_kernel_rejects(
        &format!(
            "{}{}",
            AFFINE_TOK,
            r#"
(def bad (pi k Tok (pi #[once] b Bool Nat))
  (lam k Tok (lam #[once] b Bool
    (let r (pi c Bool Nat) ((rec Bool) (lam z Bool Nat) (burn k) (burn k))
      (r b)))))
"#
        ),
        "[UseAfterMove]: variable 'k' is used after it was moved",
    );
    assert_accepted(&format!(
        "{}{}",
        AFFINE_TOK,
        r#"
(def good (pi k Tok (pi #[once] b Bool Nat))
  (lam k Tok (lam #[once] b Bool
    ((rec Bool) (lam z Bool Nat) (burn k) (burn k) b))))
"#
    ));
}

/// The minor premises may not be supplied later through a partial application of the
/// recursor (bound to a variable), where the recursor rule cannot see them.
#[test]
fn recursor_minor_premises_must_be_supplied_in_place() {
    let source = r#"
(inductive Tok (sort 1) (ctor mk_tok (pi f (pi x Nat Nat) Tok)))
(def eat (pi t Tok (pi #[once] n Nat Nat)) (lam t Tok (lam #[once] n Nat (succ n))))
(def bad (pi k Tok (pi #[once] n Nat Nat))
  (lam k Tok (lam #[once] n Nat
    (let r (pi s (pi #[once] m Nat (pi #[once] ih Nat Nat)) (pi n Nat Nat))
           ((rec Nat) (lam z Nat Nat) zero)
      (r (lam #[once] m Nat (lam #[once] ih Nat (eat k ih))) n)))))
"#;
    assert_kernel_rejects(source, "RecursorWithoutMinorPremises");
}

/// Branching recursive type: the leaf case runs once per leaf.
#[test]
fn branching_type_leaf_case_is_repeated() {
    let source = with_tok(
        r#"
(inductive Tree (sort 1) (ctor leaf Tree) (ctor node (pi l Tree (pi r Tree Tree))))
(inductive TLP (sort 1) (ctor mk_tlp (pi a TL (pi b TL TLP))))
(def leaves (pi k Tok (pi #[once] t Tree TLP))
  (lam k Tok (lam #[once] t Tree
    (match t TLP
      (case (leaf) (mk_tlp (tcons k tnil) tnil))
      (case (node l ihl r ihr) ihl)))))
"#,
    );
    assert_kernel_rejects(&source, "RepeatedMinorValueNotCopy");
}

/// A fixpoint body runs once per recursive call.
#[test]
fn fixpoint_body_may_not_consume_captured_value() {
    let source = r#"
(inductive Tok (sort 1) (ctor mk_tok (pi f (pi x Nat Nat) Tok)))
(partial eat (pi k Tok (Comp Nat)) (lam k Tok (ret Nat)))
(partial loop_eat (pi k Tok (pi #[once] n Nat (Comp Nat)))
  (lam k Tok
    (fix go (pi #[once] n Nat (Comp Nat))
      (lam #[once] n Nat (bind Nat Nat (eat k) (go n))))))
"#;
    assert_kernel_rejects(source, "ConsumedInRepeatedScope");
}

/// Positive controls: the base case of a linear recursion runs exactly once; a match on a
/// non-recursive type runs one branch; a Copy recursive field may be used with its IH.
#[test]
fn single_run_minor_premises_may_consume() {
    assert_accepted(&with_tok(
        r#"
(def at_end (pi k Tok (pi #[once] n Nat TL))
  (lam k Tok (lam #[once] n Nat
    (match n TL
      (case (zero) (tcons k tnil))
      (case (succ m ih) ih)))))
(def pick (pi k Tok (pi #[once] b Bool TL))
  (lam k Tok (lam #[once] b Bool
    (match b TL
      (case (true) (tcons k tnil))
      (case (false) tnil)))))
(def tails_len (pi #[once] l (List Nat) Nat)
  (lam #[once] l (List Nat)
    (match l Nat
      (case (nil) zero)
      (case (cons h t ih) (add (length t) ih)))))
"#,
    ));
}

/// The succ case may call (read) a captured function on every iteration: the kernel accepts.
#[test]
fn recursive_case_may_read_captured_function() {
    assert_no_kernel_error(
        r#"
(def iter (pi f (pi x Nat Nat) (pi #[once] n Nat Nat))
  (lam f (pi x Nat Nat) (lam #[once] n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m ih) (f ih))))))
"#,
    );
}

// ---------------------------------------------------------------------------------------------
// Reads after moves
// ---------------------------------------------------------------------------------------------

/// Calling a function value after it was moved is a use after move; calling it before moving
/// it is fine.
#[test]
fn calling_a_moved_function_value_is_rejected() {
    let decls = r#"
(inductive FBox (sort 1) (ctor mk_fbox (pi f (pi x Nat Nat) FBox)))
(inductive R (sort 1) (ctor mk_r (pi b FBox (pi n Nat R))))
(inductive R2 (sort 1) (ctor mk_r2 (pi n Nat (pi b FBox R2))))
"#;
    assert_kernel_rejects(
        &format!(
            "{}{}",
            decls,
            r#"
(def use_after (pi f (pi x Nat Nat) R)
  (lam f (pi x Nat Nat) (mk_r (mk_fbox f) (f zero))))
"#
        ),
        "UseAfterMove",
    );
    assert_accepted(&format!(
        "{}{}",
        decls,
        r#"
(def read_then_move (pi f (pi x Nat Nat) R2)
  (lam f (pi x Nat Nat) (mk_r2 (f zero) (mk_fbox f))))
"#
    ));
}

// ---------------------------------------------------------------------------------------------
// MIR
// ---------------------------------------------------------------------------------------------

/// Two `&mut x` passed to one curried call (p04): the first loan is held by the partial
/// application and conflicts with the second.
#[test]
fn two_mutable_borrows_through_curried_call_are_rejected() {
    let errors = errors_for(
        r#"
(def use_two (pi a (Ref #[r] Mut Nat) (pi b (Ref #[r] Mut Nat) Nat))
  (lam a (Ref #[r] Mut Nat) (lam b (Ref #[r] Mut Nat) zero)))
(def two_mut (pi x Nat Nat)
  (lam x Nat (use_two (&mut x) (&mut x))))
"#,
    );
    assert!(
        errors.iter().any(|e| e.starts_with("[M200]")),
        "expected M200, got:\n{}",
        errors.join("\n")
    );
}

/// Shared borrows through a curried call stay legal, and so does a mutable borrow followed by
/// another one once the first call has returned. (A second `&mut x` inside a later argument of
/// the same call, `(use_mut_nat (&mut x) (use_mut_nat (&mut x) zero))`, is rejected, as in
/// Rust: the first loan is held by the partial application while the argument is evaluated.)
#[test]
fn sequential_borrows_through_curried_calls_are_accepted() {
    assert_accepted(
        r#"
(def use_two_shared (pi a (Ref #[r] Shared Nat) (pi b (Ref #[r] Shared Nat) Nat))
  (lam a (Ref #[r] Shared Nat) (lam b (Ref #[r] Shared Nat) zero)))
(def two_shared (pi x Nat Nat)
  (lam x Nat (use_two_shared (& x) (& x))))
(def use_mut_nat (pi a (Ref #[r] Mut Nat) (pi n Nat Nat))
  (lam a (Ref #[r] Mut Nat) (lam n Nat n)))
(def mut_then_mut (pi x Nat Nat)
  (lam x Nat (let n Nat (use_mut_nat (&mut x) zero) (use_mut_nat (&mut x) n))))
"#,
    );
}

/// An unsaturated recursor application cannot be compiled; it is rejected with a lowering
/// error instead of producing a binary that panics.
#[test]
fn partially_applied_recursor_is_a_lowering_error() {
    let errors = errors_for(
        r#"
(def dbl (pi n Nat Nat) ((rec Nat) (lam z Nat Nat) zero (lam m Nat (lam ih Nat (succ (succ ih))))))
"#,
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("Partially applied recursor")),
        "expected a lowering error, got:\n{}",
        errors.join("\n")
    );
}

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_ownership_soundness_{}_{}_{}",
        prefix,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

/// p23: a program accepted by every check used to panic at run time in the typed backend
/// ("moved local") because copy propagation duplicated a move. It must now run.
#[test]
fn typed_binary_runs_after_copy_propagation() {
    let dir = unique_temp_dir("p23");
    let source = dir.join("let_mut_min.lrl");
    fs::write(
        &source,
        r#"
(def use_mut (pi r (Ref #[r] Mut Nat) Nat) (lam r (Ref #[r] Mut Nat) zero))
(def nll_ok (pi x Nat Nat)
  (lam x Nat (let r (Ref #[r] Mut Nat) (&mut x) (use_mut r))))
(def main Nat (nll_ok zero))
"#,
    )
    .expect("write probe");
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args([
            "run",
            source.to_str().expect("utf-8 path"),
            "--backend",
            "typed",
        ])
        .output()
        .expect("run cli");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let _ = fs::remove_dir_all(&dir);
    assert!(
        output.status.success() && stdout.contains("Result: 0"),
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

/// The old copy propagation also miscompiled the stdlib folds silently: `foldr plus_step zero
/// [1,2,3,4]` printed `Result: 0` in both backends. The corpus file states the expected value.
#[test]
fn typed_binary_computes_stdlib_foldr() {
    let source = repo_root().join("tests/stdlib_suite/data_list/list_foldr_sum.lrl");
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args([
            "run",
            source.to_str().expect("utf-8 path"),
            "--backend",
            "typed",
        ])
        .output()
        .expect("run cli");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("Result: 10"),
        "typed run of list_foldr_sum.lrl failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

/// Runs `cli <args...>` from the repository root on a temporary copy of `source`; returns
/// (success, stdout, stderr).
fn run_cli_on_source(prefix: &str, source: &str, args: &[&str]) -> (bool, String, String) {
    let dir = unique_temp_dir(prefix);
    let path = dir.join(format!("{}.lrl", prefix));
    fs::write(&path, source).expect("write probe");
    let path_str = path.to_str().expect("utf-8 path").to_string();
    let mut full_args: Vec<String> = Vec::new();
    for arg in args {
        if *arg == "{file}" {
            full_args.push(path_str.clone());
        } else if *arg == "{out}" {
            full_args.push(dir.join("out_bin").to_string_lossy().to_string());
        } else {
            full_args.push(arg.to_string());
        }
    }
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .args(&full_args)
        .output()
        .expect("run cli");
    let mut stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let bin = dir.join("out_bin");
    if output.status.success() && bin.exists() {
        let run = Command::new(&bin).output().expect("run compiled binary");
        stdout.push_str(&String::from_utf8_lossy(&run.stdout));
    }
    let _ = fs::remove_dir_all(&dir);
    (output.status.success(), stdout, stderr)
}

// ---------------------------------------------------------------------------------------------
// Non-recursive matches: the branches are alternatives
// ---------------------------------------------------------------------------------------------

/// Only one branch of a match on a non-recursive type runs, so every branch may consume the same
/// captured value (the kernel walks the branches from the same state and joins the results).
#[test]
fn non_recursive_match_branches_may_consume_the_same_value() {
    assert_accepted(&with_tok(
        r#"
(def route (pi k Tok (pi #[once] b Bool TL))
  (lam k Tok (lam #[once] b Bool
    (match b TL
      (case (true) (tcons k tnil))
      (case (false) (tcons k tnil))))))
"#,
    ));
}

/// After the match, a value consumed by any branch is moved; the scrutinee is consumed before
/// the branch runs.
#[test]
fn value_consumed_in_a_branch_is_moved_after_the_match() {
    assert_kernel_rejects(
        &with_tok(
            r#"
(def route2 (pi k Tok (pi #[once] b Bool TL))
  (lam k Tok (lam #[once] b Bool
    (tcons k (match b TL (case (true) (tcons k tnil)) (case (false) (tcons k tnil)))))))
"#,
        ),
        "UseAfterMove",
    );
    assert_kernel_rejects(
        &with_tok(
            r#"
(def route3 (pi k Tok (pi #[once] b Bool TL))
  (lam k Tok (lam #[once] b Bool
    (let r TL (match b TL (case (true) (tcons k tnil)) (case (false) tnil))
      (tcons k r)))))
"#,
        ),
        "UseAfterMove",
    );
    assert_kernel_rejects(
        &with_tok(
            r#"
(inductive OT (sort 1) (ctor onone OT) (ctor osome (pi t Tok OT)))
(def keep (pi o OT OT) (lam o OT o))
(def rematch (pi o OT OT)
  (lam o OT (match o OT (case (onone) onone) (case (osome t) (keep o)))))
"#,
        ),
        "UseAfterMove",
    );
}

const PICK: &str = r#"
(inductive Tok (sort 1) (ctor mk_tok (pi f (pi x Nat Nat) Tok)))
(def idn (pi x Nat Nat) (lam x Nat x))
(def spend (pi t Tok (pi #[once] n Nat Nat))
  (lam t Tok (lam #[once] n Nat (match t Nat (case (mk_tok f) (f n))))))
(def pick (pi t Tok (pi #[once] b Bool Nat))
  (lam t Tok (lam #[once] b Bool
    (match b Nat
      (case (true) (spend t (succ zero)))
      (case (false) (spend t (succ (succ zero))))))))
(def main Nat (pick (mk_tok idn) false))
"#;

/// The same program compiles and runs under both backends (only the taken branch runs).
#[test]
fn non_recursive_match_consuming_in_both_branches_runs_in_both_backends() {
    let (ok, stdout, stderr) =
        run_cli_on_source("pick_typed", PICK, &["run", "{file}", "--backend", "typed"]);
    assert!(
        ok && stdout.contains("Result: 2"),
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
    let (ok, stdout, stderr) = run_cli_on_source(
        "pick_dyn",
        PICK,
        &["compile", "{file}", "--backend", "dynamic", "-o", "{out}"],
    );
    assert!(
        ok && stdout.contains("Result: Nat(2)"),
        "dynamic compile/run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

// ---------------------------------------------------------------------------------------------
// Borrowing is not moving
// ---------------------------------------------------------------------------------------------

const LOOK: &str = r#"
(inductive Tok (sort 1) (ctor mk_tok (pi f (pi x Nat Nat) Tok)))
(def idn (pi x Nat Nat) (lam x Nat x))
(def look (pi r (Ref #[r] Shared Tok) Nat) (lam r (Ref #[r] Shared Tok) (succ zero)))
(def poke (pi r (Ref #[r] Mut Tok) Nat) (lam r (Ref #[r] Mut Tok) (succ zero)))
(def eat (pi t Tok Nat) (lam t Tok (succ (succ zero))))
"#;

fn with_look(body: &str) -> String {
    format!("{}\n{}", LOOK, body)
}

/// Moving a value while a shared borrow of it is still used is rejected by MIR's borrow check
/// (`M201`), not by the kernel, which counts a borrow as a read.
#[test]
fn moving_a_borrowed_value_is_rejected_by_mir() {
    let errors = errors_for(&with_look(
        r#"
(def bwc (pi t Tok Nat)
  (lam t Tok (let r (Ref #[r] Shared Tok) (& t) (let n Nat (eat t) (look r)))))
"#,
    ));
    assert!(
        errors.iter().any(|e| e.starts_with("[M201]")),
        "expected M201, got:\n{}",
        errors.join("\n")
    );
    assert!(
        !errors.iter().any(|e| e.starts_with("[K")),
        "the kernel should accept the program, got:\n{}",
        errors.join("\n")
    );
}

/// A borrow whose last use precedes the move, two shared borrows of the same non-Copy value,
/// and a dead mutable borrow followed by a move are all accepted.
#[test]
fn borrows_are_reads_not_moves() {
    assert_accepted(&with_look(
        r#"
(def bdc (pi t Tok Nat)
  (lam t Tok (let r (Ref #[r] Shared Tok) (& t) (let n Nat (look r) (add n (eat t))))))
(def two (pi t Tok Nat)
  (lam t Tok (let r1 (Ref #[r] Shared Tok) (& t)
    (let r2 (Ref #[r] Shared Tok) (& t) (add (look r1) (look r2))))))
(def mdc (pi t Tok Nat)
  (lam t Tok (let n Nat (poke (&mut t)) (add n (eat t)))))
"#,
    ));
}

/// Borrowing a value that was already moved is a use after move (kernel).
#[test]
fn borrowing_a_moved_value_is_rejected_by_the_kernel() {
    assert_kernel_rejects(
        &with_look(
            r#"
(def bam (pi t Tok Nat) (lam t Tok (let n Nat (eat t) (look (& t)))))
"#,
        ),
        "UseAfterMove",
    );
    assert_kernel_rejects(
        &with_look(
            r#"
(def mam (pi t Tok Nat) (lam t Tok (let n Nat (eat t) (poke (&mut t)))))
"#,
        ),
        "UseAfterMove",
    );
}

/// A closure that only borrows a captured value is `Fn`: it can be called repeatedly, and the
/// value can be moved after the closure's last use.
#[test]
fn closure_borrowing_a_capture_is_fn() {
    assert_accepted(&with_look(
        r#"
(def reread (pi t Tok Nat)
  (lam t Tok
    (let g (pi u Nat Nat) (lam u Nat (look (& t)))
      (add (add (g zero) (g zero)) (eat t)))))
"#,
    ));
}

// ---------------------------------------------------------------------------------------------
// Erased positions: types, proofs, motives, indices, parameters
// ---------------------------------------------------------------------------------------------

/// Generic congruence, symmetry, transitivity and transport over an arbitrary (non-Copy) `A`:
/// the motive and the parameters of the `Eq` recursor mention `x : A` only in erased positions.
#[test]
fn generic_equality_lemmas_are_accepted() {
    assert_accepted(
        r#"
(def cong
  (pi A (sort 1) (pi B (sort 1) (pi f (pi x A B)
    (pi x A (pi y A (pi e (Eq A x y) (Eq B (f x) (f y))))))))
  (lam A (sort 1) (lam B (sort 1) (lam f (pi x A B)
    (lam x A (lam y A (lam e (Eq A x y)
      ((rec Eq) A x
        (lam y2 A (lam e2 (Eq A x y2) (Eq B (f x) (f y2))))
        (refl B (f x))
        y e))))))))
(def sym
  (pi A (sort 1) (pi x A (pi y A (pi e (Eq A x y) (Eq A y x)))))
  (lam A (sort 1) (lam x A (lam y A (lam e (Eq A x y)
    ((rec Eq) A x (lam y2 A (lam e2 (Eq A x y2) (Eq A y2 x))) (refl A x) y e))))))
(def trans
  (pi A (sort 1) (pi x A (pi y A (pi z A
    (pi e1 (Eq A x y) (pi e2 (Eq A y z) (Eq A x z)))))))
  (lam A (sort 1) (lam x A (lam y A (lam z A
    (lam e1 (Eq A x y) (lam e2 (Eq A y z)
      ((rec Eq) A y (lam z2 A (lam e3 (Eq A y z2) (Eq A x z2))) e1 z e2))))))))
(def transport
  (pi A (sort 1) (pi P (pi a A (sort 1)) (pi x A (pi y A
    (pi e (Eq A x y) (pi px (P x) (P y)))))))
  (lam A (sort 1) (lam P (pi a A (sort 1)) (lam x A (lam y A
    (lam e (Eq A x y) (lam px (P x)
      ((rec Eq) A x (lam y2 A (lam e2 (Eq A x y2) (P y2))) px y e))))))))
(def add_zero_right (pi n Nat (Eq Nat (add n zero) n))
  (lam n Nat
    ((rec Nat)
      (lam k Nat (Eq Nat (add k zero) k))
      (refl Nat zero)
      (lam k Nat (lam ih (Eq Nat (add k zero) k)
        (cong Nat Nat succ (add k zero) k ih)))
      n)))
"#,
    );
}

/// A proof argument is erased: building `refl A x` does not consume `x`.
#[test]
fn proof_arguments_do_not_consume() {
    assert_no_kernel_error(
        r#"
(def keep (pi A (sort 1) (pi x A (pi #[once] p (Eq A x x) A)))
  (lam A (sort 1) (lam x A (lam #[once] p (Eq A x x) x))))
(def use_keep (pi A (sort 1) (pi x A A))
  (lam A (sort 1) (lam x A (keep A x (refl A x)))))
"#,
    );
}

/// Proofs are erased and therefore Copy, even when the proposition stores a non-Copy witness:
/// a closure returning a captured proof is `Fn` (kernel, elaborator and MIR).
#[test]
fn proofs_are_copy() {
    assert_accepted(
        r#"
(inductive Holds (pi A (sort 1) (pi a A (sort 0)))
  (ctor holds (pi A (sort 1) (pi a A (pi w A (Holds A a))))))
(def k (pi A (sort 1) (pi a A (pi h (Holds A a) (pi u Nat (Holds A a)))))
  (lam A (sort 1) (lam a A (lam h (Holds A a) (lam u Nat h)))))
"#,
    );
}

/// A capture that only occurs as a recursor index is erased: the closure is `Fn` (this used to
/// be a false `K0043` "annotated Fn but requires FnOnce").
#[test]
fn index_only_capture_does_not_raise_the_kind() {
    assert_accepted(&with_tok(
        r#"
(inductive W (pi t Tok (sort 1))
  (ctor mkw (pi t Tok (W t)))
  (ctor w2 (pi n Nat (pi t Tok (W t)))))
(def get (pi t Tok (pi w (W t) Tok))
  (lam t Tok (lam w (W t)
    (match w Tok
      (case (mkw s) s)
      (case (w2 n s) s)))))
"#,
    ));
}

// ---------------------------------------------------------------------------------------------
// Function kinds: the elaborator and the kernel agree
// ---------------------------------------------------------------------------------------------

/// Calling a captured `Fn` function inside a match case (an `FnOnce` minor premise) reads it:
/// the enclosing closure is `Fn` for both the elaborator and the kernel (probe q1j used to be
/// accepted by the elaborator and rejected by the kernel with `K0043`).
#[test]
fn reading_a_capture_inside_a_minor_premise_keeps_fn() {
    assert_accepted(
        r#"
(def k (pi g (pi x Nat Nat) (pi n Nat Nat))
  (lam g (pi x Nat Nat) (lam n Nat (match n Nat (case (zero) zero) (case (succ m ih) (g m))))))
"#,
    );
}

/// A closure that consumes a non-Copy capture is `FnOnce`; annotating it `Fn` is rejected by the
/// elaborator (F0206) before the kernel sees it.
#[test]
fn consuming_a_capture_requires_fnonce_in_the_elaborator() {
    let errors = errors_for(&with_tok(
        r#"
(def konst (pi k Tok (pi n Nat Tok)) (lam k Tok (lam n Nat k)))
"#,
    ));
    assert!(
        errors.iter().any(|e| e.starts_with("[F0206]")),
        "expected F0206, got:\n{}",
        errors.join("\n")
    );
}

// ---------------------------------------------------------------------------------------------
// The `affine` marker
// ---------------------------------------------------------------------------------------------

const CHAN: &str = r#"
(inductive (affine) Chan (sort 1) (ctor mk_chan (pi id Nat Chan)))
(inductive CP (sort 1) (ctor mk_cp (pi a Chan (pi b Chan CP))))
"#;

/// A type marked `affine` is not Copy even though its only field is a `Nat`.
#[test]
fn affine_type_cannot_be_used_twice() {
    assert_kernel_rejects(
        &format!(
            "{}{}",
            CHAN,
            r#"
(def dup (pi c Chan CP) (lam c Chan (mk_cp c c)))
"#
        ),
        "UseAfterMove",
    );
    // Without the marker the same type derives Copy.
    assert_accepted(
        r#"
(inductive Chan (sort 1) (ctor mk_chan (pi id Nat Chan)))
(inductive CP (sort 1) (ctor mk_cp (pi a Chan (pi b Chan CP))))
(def dup (pi c Chan CP) (lam c Chan (mk_cp c c)))
"#,
    );
}

/// `copy` and `affine` together are rejected; the marker adds no axiom dependency (a total
/// definition using the type stays computable).
#[test]
fn affine_marker_conflicts_with_copy_and_adds_no_axioms() {
    let errors = errors_for(
        r#"
(inductive copy (affine) Chan (sort 1) (ctor mk_chan (pi id Nat Chan)))
"#,
    );
    assert!(
        errors.iter().any(|e| e.starts_with("[K0052]")),
        "expected K0052, got:\n{}",
        errors.join("\n")
    );
    assert_accepted(&format!(
        "{}{}",
        CHAN,
        r#"
(def send (pi c Chan (pi #[once] n Nat Chan))
  (lam c Chan (lam #[once] n Nat (match c Chan (case (mk_chan i) (mk_chan (add i n)))))))
(def close (pi c Chan Nat) (lam c Chan (match c Nat (case (mk_chan i) i))))
(def session Nat (close (send (send (mk_chan zero) (succ zero)) (succ (succ zero)))))
"#
    ));
}

/// A linear session over an affine channel runs under both backends.
#[test]
fn affine_channel_session_runs_in_both_backends() {
    let source = format!(
        "{}{}",
        CHAN,
        r#"
(def send (pi c Chan (pi #[once] n Nat Chan))
  (lam c Chan (lam #[once] n Nat (match c Chan (case (mk_chan i) (mk_chan (add i n)))))))
(def close (pi c Chan Nat) (lam c Chan (match c Nat (case (mk_chan i) i))))
(def main Nat (close (send (send (mk_chan zero) (succ (succ zero))) (succ (succ (succ zero))))))
"#
    );
    let (ok, stdout, stderr) = run_cli_on_source(
        "chan_typed",
        &source,
        &["run", "{file}", "--backend", "typed"],
    );
    assert!(
        ok && stdout.contains("Result: 5"),
        "typed run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
    let (ok, stdout, stderr) = run_cli_on_source(
        "chan_dyn",
        &source,
        &["compile", "{file}", "--backend", "dynamic", "-o", "{out}"],
    );
    assert!(
        ok && stdout.contains("Result: Nat(5)"),
        "dynamic compile/run failed\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

// ---------------------------------------------------------------------------------------------
// Diagnostics name the variable
// ---------------------------------------------------------------------------------------------

/// `K0021` messages name the variable (its source binder name), not a de Bruijn index.
#[test]
fn ownership_diagnostics_name_the_variable() {
    assert_kernel_rejects(
        &with_tok(
            r#"
(def twice (pi tok Tok TL) (lam tok Tok (tcons tok (tcons tok tnil))))
"#,
        ),
        "variable 'tok' is used after it was moved",
    );
    assert_kernel_rejects(
        &with_tok(
            r#"
(def spread (pi k Tok (pi #[once] n Nat TL))
  (lam k Tok (lam #[once] n Nat
    (match n TL
      (case (zero) tnil)
      (case (succ m ih) (tcons k ih))))))
"#,
        ),
        "non-Copy variable 'k' is consumed inside a minor premise",
    );
    assert_kernel_rejects(
        &with_tok(
            r#"
(inductive TQ (sort 1) (ctor qnil TQ) (ctor qcons (pi a TL (pi b TQ TQ))))
(def suffixes (pi l TL TQ)
  (lam l TL
    (match l TQ
      (case (tnil) qnil)
      (case (tcons h rest ih) (qcons rest ih)))))
"#,
        ),
        "recursive field 'rest'",
    );
    assert_kernel_rejects(
        &with_tok(
            r#"
(def letdup (pi k Tok TL) (lam k Tok (let held Tok k (tcons held (tcons held tnil)))))
"#,
        ),
        "variable 'held'",
    );
}

/// The examples of `docs/spec/function_kinds.md` §9 behave as the spec says.
#[test]
fn function_kinds_spec_examples() {
    // 9.1, 9.2, 9.3 (accepted part) and 9.5.
    assert_accepted(
        r#"
(def make_adder
  (pi x Nat (pi fn y Nat Nat))
  (lam x Nat
    (lam y Nat (add x y))))
(inductive (affine) Ticket (sort 1)
  (ctor mk_ticket (pi id Nat Ticket)))
(def make_once
  (pi t Ticket (pi #[once] _ Nat Ticket))
  (lam t Ticket
    (lam _ Nat t)))
(def step_twice
  (pi g (pi #[mut] x Nat Nat) (pi #[mut] n Nat Nat))
  (lam g (pi #[mut] x Nat Nat)
    (lam #[mut] n Nat (g (g n)))))
(def apply_once
  (pi f (pi #[once] x Nat Nat) (pi #[once] v Nat Nat))
  (lam f (pi #[once] x Nat Nat)
    (lam #[once] v Nat (f v))))
(def add_one
  (pi #[fn] x Nat Nat)
  (lam x Nat (succ x)))
(def test_coercion Nat (apply_once add_one zero))
"#,
    );
    let expect_code = |source: &str, code: &str| {
        let errors = errors_for(source);
        assert!(
            errors.iter().any(|e| e.starts_with(code)),
            "expected {}, got:\n{}",
            code,
            errors.join("\n")
        );
    };
    // 9.3, rejected part.
    expect_code(
        r#"
(def step_twice_bad
  (pi g (pi #[mut] x Nat Nat) (pi n Nat Nat))
  (lam g (pi #[mut] x Nat Nat)
    (lam n Nat (g (g n)))))
"#,
        "[F0206]",
    );
    // 9.4.
    expect_code(
        r#"
(inductive (affine) Ticket (sort 1)
  (ctor mk_ticket (pi id Nat Ticket)))
(def bad_kind
  (pi t Ticket (pi #[fn] _ Nat Ticket))
  (lam t Ticket
    (lam #[fn] _ Nat t)))
"#,
        "[F0207]",
    );
    // The previous version of 9.5 (inner `pi` of kind Fn) is rejected.
    expect_code(
        r#"
(def apply_once
  (pi f (pi #[once] x Nat Nat) (pi v Nat Nat))
  (lam f (pi #[once] x Nat Nat)
    (lam v Nat (f v))))
"#,
        "[F0206]",
    );
}
