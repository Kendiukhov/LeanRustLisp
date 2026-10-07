//! End-to-end tests for the typed Rust backend on programs that used to need the dynamic
//! backend (docs/spec/codegen/typed-backend.md, "Values of Types Computed at Run Time"):
//!
//! * recursors of *large eliminations* -- a motive that computes different types for different
//!   indices, e.g. a total `head` on `Vec A (succ n)` whose motive is `Unit` at `zero` and `A` at
//!   `succ` -- used to be emitted with the use site's result type and failed rustc with `E0308`;
//!   they are now emitted with a uniform boxed signature (`LrlOpaque`) and adapted to the use
//!   site with checked conversions;
//! * a large elimination that would box a partially known type is rejected with `TB010`, and
//!   `--backend auto` falls back to the dynamic backend;
//! * a polymorphic entry definition used to fail rustc with `E0283`;
//! * a polymorphic `map` whose recursive case calls a captured function was rejected by MIR
//!   (`M100`) because the minor premise was analysed in a misaligned context;
//! * values of types computed at run time outside recursors (a definition whose result type is a
//!   large elimination, `transport`) were rejected by MIR typing (`M300`) in both backends; a
//!   reference still cannot pass through such a type;
//! * constructors of inductives with a value parameter were emitted with a `()` argument for it
//!   (rustc E0308).
//!
//! Every program is run through the real CLI from the repository root.

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
        "lrl_typed_large_elim_{}_{}_{}",
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
        assert!(
            run.status.success(),
            "compiled binary failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr)
        );
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

fn compile(prefix: &str, source: &str, backend: &str) -> CliRun {
    run_cli(
        prefix,
        source,
        &["compile", "{file}", "--backend", backend, "-o", "{out}"],
    )
}

fn assert_output_lines(run: &CliRun, expected_lines: &[&str]) {
    let lines: Vec<&str> = run.stdout.lines().map(str::trim).collect();
    let found = expected_lines
        .iter()
        .all(|expected| lines.iter().any(|line| line == expected));
    assert!(
        run.success && found,
        "expected success and lines {:?};\nstdout:\n{}\nstderr:\n{}",
        expected_lines,
        run.stdout,
        run.stderr
    );
}

const VEC: &str = r#"
(inductive Unit (sort 1) (ctor unit Unit))
(inductive Vec (pi A (sort 1) (pi n Nat (sort 1)))
  (ctor vnil (pi {A (sort 1)} (Vec A zero)))
  (ctor vcons (pi {A (sort 1)} (pi {n Nat} (pi h A (pi t (Vec A n) (Vec A (succ n))))))))
"#;

/// The total head of a non-empty vector: its motive is `Unit` at index `zero` and `A` at
/// `succ`, so the impossible `vnil` case returns `unit` and the induction hypothesis has a type
/// that is not known statically (`Opaque` in MIR). Typed run and typed binary both work.
#[test]
fn total_vector_head_runs_with_the_typed_backend() {
    let source = format!(
        r#"{VEC}
(def vhead (pi {{A (sort 1)}} (pi {{n Nat}} (pi v (Vec A (succ n)) A)))
  (lam {{A}} (sort 1) (lam {{n}} Nat (lam v (Vec A (succ n))
    (match v (motive (lam k Nat (lam w (Vec A k)
                       (match k (sort 1) (case (zero) Unit) (case (succ k1 ih) A)))))
      (case (vnil) unit)
      (case (vcons h t ih) h))))))
(def main Nat (vhead (vcons 7 (vcons 8 vnil))))
"#
    );
    assert_output_lines(&run_typed("vhead_run", &source), &["Result: 7"]);
    assert_output_lines(&compile("vhead_bin", &source, "typed"), &["Result: 7"]);
}

/// The same large elimination written with the raw recursor and a type-level function defined
/// by recursion on the index (`HeadTy`), on a vector of naturals.
#[test]
fn large_elimination_through_the_raw_recursor_runs_with_the_typed_backend() {
    let source = r#"
(inductive copy Unit (sort 1) (ctor unit Unit))
(inductive NVec (pi n Nat (sort 1))
  (ctor nnil (NVec zero))
  (ctor ncons (pi n Nat (pi h Nat (pi t (NVec n) (NVec (succ n)))))))
(def HeadTy (pi k Nat (sort 1))
  (lam k Nat (match k (sort 1) (case (zero) Unit) (case (succ j ih) Nat))))
(def nhead (pi n Nat (pi v (NVec (succ n)) Nat))
  (lam n Nat (lam v (NVec (succ n))
    ((rec NVec)
      (lam k Nat (lam w (NVec k) (HeadTy k)))
      unit
      (lam k Nat (lam h Nat (lam t (NVec k) (lam ih (HeadTy k) h))))
      (succ n) v))))
(def main Nat (nhead (succ zero) (ncons (succ zero) 9 (ncons zero 4 nnil))))
"#;
    assert_output_lines(&run_typed("nhead_run", source), &["Result: 9"]);
}

/// A vector program combining the large elimination (`vhead`) with ordinary recursors (append
/// by `vsnoc`, reverse, a polymorphic map that calls a captured function in its recursive case,
/// sum) and generic equality lemmas; both backends print the same values.
#[test]
fn vector_program_agrees_across_backends() {
    let source = format!(
        r#"{VEC}
(def vhead (pi {{A (sort 1)}} (pi {{n Nat}} (pi v (Vec A (succ n)) A)))
  (lam {{A}} (sort 1) (lam {{n}} Nat (lam v (Vec A (succ n))
    (match v (motive (lam k Nat (lam w (Vec A k)
                       (match k (sort 1) (case (zero) Unit) (case (succ k1 ih) A)))))
      (case (vnil) unit)
      (case (vcons h t ih) h))))))
(def vmap (pi {{A (sort 1)}} (pi {{B (sort 1)}} (pi {{n Nat}} (pi f (pi x A B) (pi v (Vec A n) (Vec B n))))))
  (lam {{A}} (sort 1) (lam {{B}} (sort 1) (lam {{n}} Nat (lam f (pi x A B) (lam v (Vec A n)
    (match v (motive (lam k Nat (lam w (Vec A k) (Vec B k))))
      (case (vnil) vnil)
      (case (vcons h t ih) (vcons (f h) ih)))))))))
(def vsnoc (pi {{A (sort 1)}} (pi {{n Nat}} (pi v (Vec A n) (pi #[once] x A (Vec A (succ n))))))
  (lam {{A}} (sort 1) (lam {{n}} Nat (lam v (Vec A n) (lam #[once] x A
    (match v (motive (lam k Nat (lam w (Vec A k) (Vec A (succ k)))))
      (case (vnil) (vcons x vnil))
      (case (vcons h t ih) (vcons h ih))))))))
(def vreverse (pi {{A (sort 1)}} (pi {{n Nat}} (pi v (Vec A n) (Vec A n))))
  (lam {{A}} (sort 1) (lam {{n}} Nat (lam v (Vec A n)
    (match v (motive (lam k Nat (lam w (Vec A k) (Vec A k))))
      (case (vnil) vnil)
      (case (vcons h t ih) (vsnoc ih h)))))))
(def vsum (pi {{n Nat}} (pi v (Vec Nat n) Nat))
  (lam {{n}} Nat (lam v (Vec Nat n)
    (match v Nat (case (vnil) zero) (case (vcons h t ih) (add h ih))))))
(def sym (pi {{A (sort 1)}} (pi {{x A}} (pi {{y A}} (pi e (Eq A x y) (Eq A y x)))))
  (lam {{A}} (sort 1) (lam {{x}} A (lam {{y}} A (lam e (Eq A x y)
    (match e (motive (lam b A (lam w (Eq A x b) (Eq A b x))))
      (case (refl) (refl A x))))))))
(def checked (pi n Nat (pi e (Eq Nat n n) Nat)) (lam n Nat (lam e (Eq Nat n n) n)))
(def main Nat
  (let v (Vec Nat (succ (succ (succ zero)))) (vcons 1 (vcons 2 (vcons 3 vnil)))
    (add (print_nat (vhead (vreverse v)))
      (add (print_nat (vsum (vmap (lam x Nat (add x x)) v)))
           (checked 4 (sym (refl Nat 4)))))))
"#
    );
    assert_output_lines(
        &compile("vec_typed", &source, "typed"),
        &["3", "12", "Result: 19"],
    );
    assert_output_lines(
        &compile("vec_dynamic", &source, "dynamic"),
        &["3", "12", "Result: Nat(19)"],
    );
}

/// A large elimination whose motive value at `succ` is a list of elements of a type computed at
/// run time would have to box a *partially* known type (`List<LrlOpaque>`), which the typed
/// backend refuses (`TB010`) rather than risk a failing downcast; `auto` falls back.
#[test]
fn partially_known_large_elimination_is_rejected_by_typed_and_falls_back() {
    let source = format!(
        r#"{VEC}
(def HeadTy (pi k Nat (sort 1)) (lam k Nat (match k (sort 1) (case (zero) Unit) (case (succ j ih) Nat))))
(def odd (pi {{n Nat}} (pi v (Vec Nat (succ n)) (List (HeadTy n))))
  (lam {{n}} Nat (lam v (Vec Nat (succ n))
    (match v (motive (lam k Nat (lam w (Vec Nat k) (match k (sort 1) (case (zero) Unit) (case (succ j ih) (List (HeadTy j)))))))
      (case (vnil) unit)
      (case (vcons h t ih) nil)))))
(def odd_len (pi {{n Nat}} (pi v (Vec Nat (succ n)) Nat))
  (lam {{n}} Nat (lam v (Vec Nat (succ n))
    (match (odd {{n}} v) Nat (case (nil) 7) (case (cons h t ih) 8)))))
(def main Nat (odd_len {{zero}} (vcons {{Nat}} {{zero}} 1 (vnil {{Nat}}))))
"#
    );
    let typed = compile("partial_typed", &source, "typed");
    let all = format!("{}{}", typed.stdout, typed.stderr);
    assert!(
        !typed.success && all.contains("TB010") && !all.contains("error["),
        "expected a TB010 rejection before rustc;\nstdout:\n{}\nstderr:\n{}",
        typed.stdout,
        typed.stderr
    );
    let auto = compile("partial_auto", &source, "auto");
    assert_output_lines(&auto, &["Result: Nat(7)"]);
    assert!(
        format!("{}{}", auto.stdout, auto.stderr).contains("falling back to dynamic"),
        "expected the auto fallback warning;\nstdout:\n{}\nstderr:\n{}",
        auto.stdout,
        auto.stderr
    );
}

/// The entry definition is a polymorphic function (tests/prop_elim_eq_bad.lrl): it is printed,
/// never applied, and its type parameters are instantiated with `()` (rustc used to fail with
/// `E0283`, type annotations needed).
#[test]
fn polymorphic_entry_definition_compiles_with_the_typed_backend() {
    let source = r#"
(def proof_to_nat (pi A Type (pi a A (pi b A (pi p (Eq A a b) Nat))))
  (lam A Type (lam a A (lam b A (lam p (Eq A a b)
    (match p Nat (case (refl A' a') (succ zero))))))))
"#;
    assert_output_lines(&compile("poly_entry", source, "typed"), &["Result: <func>"]);
}

/// A polymorphic map over `List A` (not Copy) whose recursive case calls a captured function:
/// the minor premise does not use the tail at run time, so the arm is handed to the recursor's
/// entry function. (It was rejected with `M100` because the minor was analysed in a context
/// shifted by the fields preceding the recursive field.)
#[test]
fn polymorphic_map_calling_a_captured_function_is_accepted() {
    let source = r#"
(def lmap (pi {A (sort 1)} (pi {B (sort 1)} (pi f (pi x A B) (pi v (List A) (List B)))))
  (lam {A} (sort 1) (lam {B} (sort 1) (lam f (pi x A B) (lam v (List A)
    (match v (List B)
      (case (nil) nil)
      (case (cons h t ih) (cons (f h) ih))))))))
(def lsum (pi l (List Nat) Nat)
  (lam l (List Nat) (match l Nat (case (nil) zero) (case (cons h t ih) (add h ih)))))
(def main Nat (lsum (lmap (lam x Nat (succ x)) (cons 1 (cons 2 (cons 3 nil))))))
"#;
    assert_output_lines(&compile("lmap_typed", source, "typed"), &["Result: 9"]);
    assert_output_lines(
        &compile("lmap_dynamic", source, "dynamic"),
        &["Result: Nat(9)"],
    );
}

// ---------------------------------------------------------------------------------------------
// Values of types computed at run time outside recursors (docs/spec/mir/typing.md, "Types
// Computed at Run Time"). These programs used to be rejected by MIR typing (`M300`) in both
// backends.
// ---------------------------------------------------------------------------------------------

/// A definition whose result type is computed by a large elimination on its argument
/// (`pick : Π b. BoolOrNat b`) used where the argument is known, and a dependent match on a
/// known scrutinee whose other alternative has an unrelated type.
#[test]
fn definition_with_a_computed_result_type_is_used_at_known_types() {
    let source = r#"
(def BoolOrNat (pi b Bool (sort 1)) (lam b Bool (match b (sort 1) (case (true) Nat) (case (false) Bool))))
(def pick (pi b Bool (BoolOrNat b))
  (lam b Bool (match b (motive (lam x Bool (BoolOrNat x))) (case (true) 5) (case (false) false))))
(def direct Nat (match true (motive (lam x Bool (BoolOrNat x))) (case (true) 3) (case (false) false)))
(def main Nat (add (pick true) (add direct (if_nat (pick false) 1 2))))
"#;
    assert_output_lines(&compile("pick_typed", source, "typed"), &["Result: 10"]);
    assert_output_lines(
        &compile("pick_dynamic", source, "dynamic"),
        &["Result: Nat(10)"],
    );
}

const TRANSPORT: &str = r#"
(def transport
  (pi {A (sort 1)} (pi P (pi a A (sort 1)) (pi {x A} (pi {y A}
    (pi e (Eq A x y) (pi px (P x) (P y)))))))
  (lam {A} (sort 1) (lam P (pi a A (sort 1)) (lam {x} A (lam {y} A
    (lam e (Eq A x y) (lam px (P x)
      (match e (motive (lam b A (lam w (Eq A x b) (P b))))
        (case (refl) px)))))))))
"#;

/// `transport` along an equality into a type family: inside its body the type `P y` is stuck;
/// at the use sites it is `Nat` and `Vec Nat 2`.
#[test]
fn transport_into_a_type_family_is_used_at_known_types() {
    let source = format!(
        r#"{VEC}{TRANSPORT}
(def vsum (pi {{n Nat}} (pi v (Vec Nat n) Nat))
  (lam {{n}} Nat (lam v (Vec Nat n)
    (match v Nat (case (vnil) zero) (case (vcons h t ih) (add h ih))))))
(def two_eq (Eq Nat (add 1 1) 2) (refl Nat 2))
(def main Nat
  (add (transport (lam n Nat Nat) (refl Nat 3) 7)
       (vsum {{2}} (transport {{Nat}} (lam n Nat (Vec Nat n)) {{(add 1 1)}} {{2}} two_eq
                     (vcons {{Nat}} {{1}} 4 (vcons {{Nat}} {{0}} 5 (vnil {{Nat}})))))))
"#
    );
    assert_output_lines(
        &compile("transport_typed", &source, "typed"),
        &["Result: 16"],
    );
    assert_output_lines(
        &compile("transport_dynamic", &source, "dynamic"),
        &["Result: Nat(16)"],
    );
}

/// A reference must not pass through a value of a type computed at run time: the borrow
/// checker cannot see regions inside it, so MIR typing keeps rejecting the flow (`M300`). The
/// same program without `transport` is rejected by the borrow checker (`M201`).
#[test]
fn reference_cannot_pass_through_a_type_computed_at_run_time() {
    let prefix = r#"
(inductive (affine) Tok (sort 1) (ctor mk Tok))
(def burn (pi t Tok Nat) (lam t Tok (match t Nat (case (mk) 1))))
(def peek (pi r (Ref #[r] Shared Tok) Nat) (lam r (Ref #[r] Shared Tok) 2))
"#;
    let through = format!(
        r#"{prefix}{TRANSPORT}
(def bad (pi t Tok Nat)
  (lam t Tok
    (let r (Ref #[r] Shared Tok) (transport (lam n Nat (Ref #[r] Shared Tok)) (refl Nat 3) (& t))
      (add (burn t) (peek r)))))
"#
    );
    let direct = format!(
        r#"{prefix}
(def bad (pi t Tok Nat)
  (lam t Tok
    (let r (Ref #[r] Shared Tok) (& t)
      (add (burn t) (peek r)))))
"#
    );
    for (name, source, code) in [
        ("ref_through", &through, "M300"),
        ("ref_direct", &direct, "M201"),
    ] {
        let run = run_cli(name, source, &["run", "{file}"]);
        let all = format!("{}{}", run.stdout, run.stderr);
        assert!(
            !run.success && all.contains(code),
            "expected {} for {};\nstdout:\n{}\nstderr:\n{}",
            code,
            name,
            run.stdout,
            run.stderr
        );
    }
}

/// A match whose motive values are functions taking an argument of a computed type: MIR and the
/// dynamic backend accept it; the typed backend would have to unbox a partially known function
/// type and refuses (`TB010`), so `auto` falls back to the dynamic backend.
#[test]
fn function_valued_large_elimination_runs_and_typed_falls_back() {
    let source = r#"
(inductive Unit (sort 1) (ctor unit Unit))
(def T (pi k Nat (sort 1)) (lam k Nat (match k (sort 1) (case (zero) Unit) (case (succ j ih) Nat))))
(def f (pi k Nat (pi #[once] x (T k) Nat))
  (lam k Nat (lam #[once] x (T k)
    ((match k (motive (lam j Nat (pi #[once] y (T j) Nat)))
       (case (zero) (lam #[once] y (T zero) zero))
       (case (succ j ih) (lam #[once] y (T (succ j)) y)))
     x))))
(def main Nat (f 1 5))
"#;
    assert_output_lines(
        &compile("fnmotive_dynamic", source, "dynamic"),
        &["Result: Nat(5)"],
    );
    let typed = compile("fnmotive_typed", source, "typed");
    let all = format!("{}{}", typed.stdout, typed.stderr);
    assert!(
        !typed.success && all.contains("TB010"),
        "expected a TB010 rejection;\nstdout:\n{}\nstderr:\n{}",
        typed.stdout,
        typed.stderr
    );
    assert_output_lines(
        &compile("fnmotive_auto", source, "auto"),
        &["Result: Nat(5)"],
    );
}

/// Inductives with a value parameter (`k : Nat`, a uniform constructor binder the kernel treats
/// as a parameter): the constructor receives the parameter's value. The typed backend used to
/// declare that argument as `()` while call sites pass the `u64` (rustc E0308), which kept the
/// vector and protocol case studies on the dynamic backend.
#[test]
fn inductive_with_a_value_parameter_runs_with_the_typed_backend() {
    let source = r#"
(inductive NBox (pi k Nat (sort 1)) (ctor nbox (pi {k Nat} (pi x Nat (NBox k)))))
(def unbox (pi {k Nat} (pi b (NBox k) Nat)) (lam {k} Nat (lam b (NBox k) (match b Nat (case (nbox x) x)))))
(inductive C (pi A (sort 1) (pi n Nat (sort 1))) (ctor mk_c (pi {A (sort 1)} (pi {n Nat} (pi id Nat (C A n))))))
(def cid (pi {A (sort 1)} (pi {n Nat} (pi c (C A n) Nat))) (lam {A} (sort 1) (lam {n} Nat (lam c (C A n) (match c Nat (case (mk_c i) i))))))
(def open_c (pi n Nat (pi i Nat (C Bool n))) (lam n Nat (lam i Nat (mk_c {Bool} {n} i))))
(def main Nat (add (unbox (nbox {3} 7)) (cid (open_c 2 5))))
"#;
    assert_output_lines(
        &compile("value_param_typed", source, "typed"),
        &["Result: 12"],
    );
    assert_output_lines(
        &compile("value_param_dynamic", source, "dynamic"),
        &["Result: Nat(12)"],
    );
}
