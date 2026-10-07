//! Regression tests for issues found by the review of the JOT revision (findings named in each
//! test): the kernel's elimination restriction, universe rule and strict positivity check for
//! inductive declarations (and its clean-up after a failed declaration), MIR lowering of proof-typed closures and of nested captures of mutable references, and the
//! lifetime elision rule. Each test runs the real CLI from the repository root (helpers as in
//! `case_study_regressions.rs`). Kernel-level tests of the same rules are in
//! `kernel/tests/core_rule_regressions.rs`.

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
        "lrl_review_regr_{}_{}_{}",
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

impl CliRun {
    fn combined(&self) -> String {
        strip_ansi(&format!("{}\n{}", self.stdout, self.stderr))
    }
}

fn strip_ansi(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' && chars.peek() == Some(&'[') {
            chars.next();
            for c in chars.by_ref() {
                if c.is_ascii_alphabetic() {
                    break;
                }
            }
            continue;
        }
        out.push(c);
    }
    out
}

/// Runs `cli <args...>` from the repository root on a temporary copy of `source` (`{file}` and
/// `{out}` in `args` are replaced by the source path and an output binary path). If the command
/// succeeds and produced the output binary, the binary is run and its stdout appended; a
/// failing binary fails the test.
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

fn run_dynamic(prefix: &str, source: &str) -> CliRun {
    run_cli(prefix, source, &["run", "{file}"])
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

fn assert_accepted(run: &CliRun) {
    assert!(
        run.success && !run.combined().contains("Error"),
        "expected acceptance;\nstdout:\n{}\nstderr:\n{}",
        run.stdout,
        run.stderr
    );
}

fn assert_output_lines(run: &CliRun, expected_lines: &[&str]) {
    let lines: Vec<String> = run
        .combined()
        .lines()
        .map(|line| line.trim().to_string())
        .collect();
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

fn assert_rejected_with(run: &CliRun, fragments: &[&str]) {
    let text = run.combined();
    assert!(
        !run.success && fragments.iter().all(|fragment| text.contains(fragment)),
        "expected rejection mentioning {:?};\nstdout:\n{}\nstderr:\n{}",
        fragments,
        run.stdout,
        run.stderr
    );
}

/// The `run` output lines equal to `line` (trimmed).
fn count_lines(run: &CliRun, line: &str) -> usize {
    run.combined()
        .lines()
        .filter(|candidate| candidate.trim() == line)
        .count()
}

// -----------------------------------------------------------------------------------------------
// R1_claims_vs_code #3: elimination restriction
// -----------------------------------------------------------------------------------------------

/// A field whose type is the sort `Prop` is not a proof: allowing large elimination of `PW` made
/// `Prop` a definitional retract of the proposition `PW` (`up (mkpw P) ≡ P`; the setting of
/// Hurkens' paradox). It was accepted and evaluated (`Eval: Ind("TrueP", [])`).
#[test]
fn prop_valued_field_does_not_allow_large_elimination() {
    let source = r#"
(inductive TrueP (sort 0) (ctor tt TrueP))
(inductive PW (sort 0) (ctor mkpw (pi P (sort 0) PW)))
(def up (pi w PW (sort 0))
  (lam w PW (match w (sort 0) (case (mkpw P) P))))
(def retract_ok (pi P (sort 0) (Eq (sort 0) (up (mkpw P)) P))
  (lam P (sort 0) (refl (sort 0) P)))
(up (mkpw TrueP))
"#;
    let run = run_dynamic("prop_retract", source);
    assert_rejected_with(
        &run,
        &["[K0027]", "Large elimination from Prop inductive 'PW'"],
    );
    assert!(
        !run.combined().contains("Eval:"),
        "the retraction must not be evaluated:\n{}",
        run.combined()
    );
}

/// Large eliminations the rule allows: an empty proposition (`False`, raw recursor), one
/// constructor whose fields are proofs with propositions as parameters (And-like), one constructor
/// with a Type PARAMETER and a proof field (rejected before: parameters had to be Prop-like too),
/// and equality (transport, the controlled exception).
#[test]
fn large_elimination_allows_proof_fields_and_any_parameters() {
    let source = r#"
(inductive TrueP (sort 0) (ctor tt TrueP))
(def absurd_nat (pi f False Nat) (lam f False ((rec False) (lam g False Nat) f)))
(inductive AndP (pi A (sort 0) (pi B (sort 0) (sort 0)))
  (ctor intro (pi {A (sort 0)} (pi {B (sort 0)} (pi a A (pi b B (AndP A B)))))))
(def and_weight (pi h (AndP TrueP TrueP) Nat)
  (lam h (AndP TrueP TrueP) (match h Nat (case (intro a b) (succ (succ zero))))))
(inductive Wrap (pi A (sort 1) (sort 0)) (ctor mkw (pi {A (sort 1)} (pi p TrueP (Wrap A)))))
(def from_wrap (pi w (Wrap Nat) Nat)
  (lam w (Wrap Nat) (match w Nat (case (mkw p) (succ zero)))))
(def transport
  (pi A (sort 1) (pi P (pi a A (sort 1)) (pi x A (pi y A
    (pi e (Eq A x y) (pi px (P x) (P y)))))))
  (lam A (sort 1) (lam P (pi a A (sort 1)) (lam x A (lam y A
    (lam e (Eq A x y) (lam px (P x)
      ((rec Eq) A x (lam y2 A (lam e2 (Eq A x y2) (P y2))) px y e))))))))
(def main Nat
  (add (and_weight (intro tt tt))
    (add (from_wrap (mkw tt))
      (transport Nat (lam n Nat Nat) zero zero (refl Nat zero) (succ (succ (succ zero)))))))
"#;
    assert_accepted(&run_dynamic("large_elim_ok", source));
    assert_output_lines(
        &compile("large_elim_ok_dynamic", source, "dynamic"),
        &["Result: Nat(6)"],
    );
}

/// An inductive whose arity is the empty proposition `False` (not a sort) was registered, and the
/// inductive itself then had type `False`: `(def oops False Bot)` was a closed proof of `False`,
/// from which `rec False` produced anything. The kernel now requires the arity to end in a sort.
/// Found while verifying the review fixes; kernel-level tests in
/// `kernel/tests/core_rule_regressions.rs`.
#[test]
fn inductive_arity_must_be_a_sort_not_a_proposition() {
    let source = r#"
(inductive Bot False)
(def oops False Bot)
(def any_nat Nat ((rec False) (lam f False Nat) oops))
(def main Nat (succ zero))
"#;
    let run = run_dynamic("arity_false", source);
    assert_rejected_with(
        &run,
        &[
            "[K0004]",
            "Error registering inductive 'Bot'",
            "ExpectedSort",
        ],
    );
    assert!(
        run.combined().contains("Unbound variable: Bot"),
        "oops must not be admitted:\n{}",
        run.combined()
    );
}

/// An inductive whose arity is written through a definition that unfolds to a sort used to skip
/// the kernel's universe check entirely (the check read the arity syntactically): `UA : OType`
/// (= `(sort 1)`) with a field of type `(sort 3)` was accepted. Found while verifying the
/// review fixes; kernel-level tests in `kernel/tests/core_rule_regressions.rs`.
#[test]
fn aliased_inductive_arity_is_universe_checked() {
    let large = r#"
(def OType (sort 2) (sort 1))
(inductive UA OType (ctor mkUA (pi A (sort 3) UA)))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("aliased_arity_large", large),
        &[
            "[K0017]",
            "Error registering inductive 'UA'",
            "UniverseLevelTooSmall",
        ],
    );
    let small = r#"
(def OType (sort 2) (sort 1))
(inductive UB OType (ctor mkUB (pi n Nat UB)))
(def main Nat (match (mkUB (succ zero)) Nat (case (mkUB n) n)))
"#;
    assert_output_lines(
        &compile("aliased_arity_small", small, "dynamic"),
        &["Result: Nat(1)"],
    );
}

// -----------------------------------------------------------------------------------------------
// X_verify V1: universe rule for inductive declarations
// -----------------------------------------------------------------------------------------------

/// X_verify's `u_type_in_type.lrl`: a data inductive in `(sort 1)` with a field of type
/// `(sort 1)`. The kernel counted that field at level 1 instead of 2 and accepted `U`; `El` then
/// made `(sort 1)` a definitional retract of `U : (sort 1)` (`El (mkU A) ≡ A`), the setting of
/// Hurkens' paradox for `Type : Type`, and the program ran (exit 0). The same declaration in
/// `(sort 2)` is fine and runs with both backends. Kernel-level tests in
/// `kernel/tests/core_rule_regressions.rs`.
#[test]
fn type_valued_field_requires_a_large_inductive() {
    let small = r#"
(inductive U (sort 1) (ctor mkU (pi A (sort 1) U)))
(def El (pi u U (sort 1)) (lam u U (match u (sort 1) (case (mkU A) A))))
(def to (pi A (sort 1) (pi a A (El (mkU A)))) (lam A (sort 1) (lam a A a)))
(def from (pi A (sort 1) (pi a (El (mkU A)) A)) (lam A (sort 1) (lam a (El (mkU A)) a)))
(def main Nat (from Nat (to Nat 7)))
"#;
    assert_rejected_with(
        &run_dynamic("u_type_in_type", small),
        &[
            "[K0017]",
            "Error registering inductive 'U'",
            "UniverseLevelTooSmall",
            "constructor mkU field 0 (argument 0) has a type in universe level Succ(Succ(Zero)), which is above inductive level Succ(Zero)",
        ],
    );
    let large = r#"
(inductive U2 (sort 2) (ctor mkU2 (pi A (sort 1) U2)))
(def El (pi u U2 (sort 1)) (lam u U2 (match u (sort 1) (case (mkU2 A) A))))
(def to (pi A (sort 1) (pi a A (El (mkU2 A)))) (lam A (sort 1) (lam a A a)))
(def from (pi A (sort 1) (pi a (El (mkU2 A)) A)) (lam A (sort 1) (lam a (El (mkU2 A)) a)))
(def main Nat (from Nat (to Nat 7)))
"#;
    assert_output_lines(&compile("u_large", large, "dynamic"), &["Result: Nat(7)"]);
    assert_output_lines(&compile("u_large", large, "typed"), &["Result: 7"]);
    // Indices are not constrained: a family indexed by a type lives in (sort 1).
    let indexed = r#"
(inductive T (pi A (sort 1) (sort 1)) (ctor mkT (T Nat)))
(def size (pi t (T Nat) Nat) (lam t (T Nat) (match t Nat (case (mkT) (succ zero)))))
(def main Nat (size mkT))
"#;
    assert_output_lines(
        &compile("type_index", indexed, "dynamic"),
        &["Result: Nat(1)"],
    );
}

/// X_verify's `comp_retract.lrl` used the prelude's `Comp`, whose `bind` stores the types `A`
/// and `B` (fields, not parameters), to make `(sort 1)` a retract of `Comp Nat`, which lived in
/// `(sort 1)`. `Comp` is now declared in `(sort 2)`, so the same program states that `(sort 1)`
/// is a retract of a type in `(sort 2)` - a harmless large elimination (like `Σ A : Type, A` in
/// `Type 1`) - and is still accepted; what the paradox needs, a code of every small type IN the
/// small universe, is no longer available: `Comp Nat` is not a `(sort 1)` type and cannot be
/// stored in a `(sort 1)` inductive. Partial definitions returning `Comp` work as before with
/// both backends.
#[test]
fn comp_lives_in_sort_two() {
    let retract = r#"
(def ElC (pi c (Comp Nat) (sort 1))
  (lam c (Comp Nat) (match c (sort 1) (case (ret A) A) (case (bind A B m n) A))))
(def code (pi A (sort 1) (Comp Nat)) (lam A (sort 1) (bind A Nat (ret A) (ret Nat))))
(def to (pi A (sort 1) (pi a A (ElC (code A)))) (lam A (sort 1) (lam a A a)))
(def main Nat (to Nat 7))
"#;
    assert_output_lines(
        &compile("comp_retract", retract, "dynamic"),
        &["Result: Nat(7)"],
    );
    let as_small_type = r#"
(def CT (sort 1) (Comp Nat))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("comp_small_type", as_small_type),
        &["[F0214]", "Unification failed: Type 1 vs Type"],
    );
    let stored = r#"
(inductive Hide (sort 1) (ctor hide (pi c (Comp Nat) Hide)))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("comp_stored", stored),
        &[
            "[K0017]",
            "Error registering inductive 'Hide'",
            "constructor hide field 0 (argument 0) has a type in universe level Succ(Succ(Zero))",
        ],
    );
    let partial = r#"
(partial countdown (pi n Nat (Comp Nat))
  (fix go (pi n Nat (Comp Nat))
    (lam n Nat
      (match n (Comp Nat)
        (case (zero) (ret Nat))
        (case (succ m ih) (bind Nat Nat (ret Nat) (go m)))))))
(partial main (Comp Nat) (countdown (succ (succ zero))))
"#;
    assert_output_lines(
        &compile("comp_partial", partial, "dynamic"),
        &["Result: Comp(Unit, Unit, Comp(Unit), Comp(Unit, Unit, Comp(Unit), Comp(Unit)))"],
    );
    assert_output_lines(
        &compile("comp_partial", partial, "typed"),
        &["Result: bind"],
    );
}

// -----------------------------------------------------------------------------------------------
// Y2 verification (soundness lens) F1 and the same function: strict positivity
// -----------------------------------------------------------------------------------------------

/// Y2_verify_soundness F1: the field `(let X (sort 0) Bad (pi x X False))` is `Bad -> False`,
/// but positivity checked the let's value at the current polarity and its body with `X` as a
/// plain variable, so `Bad` was accepted and `boom` was a closed, axiom-free proof of False
/// (exit 0, no diagnostics). Lets used positively still work, and a let-hidden recursive field
/// is a recursive argument (the match binds its `ih`; before, `ih` was unbound).
#[test]
fn let_hidden_negative_occurrence_is_rejected() {
    let negative = r#"
(inductive Bad (sort 0) (ctor mk (pi f (let X (sort 0) Bad (pi x X False)) Bad)))
(def unroll (pi b Bad (pi c Bad False)) (lam b Bad (match b (pi c Bad False) (case (mk f) f))))
(def omega (pi b Bad False) (lam b Bad (unroll b b)))
(def boom False (omega (mk omega)))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("let_negative", negative),
        &[
            "[K0015]",
            "Error registering inductive 'Bad'",
            "NonPositiveOccurrence(\"Bad\", \"mk\", 0)",
        ],
    );
    let nested = r#"
(inductive T (sort 1) (ctor leaf T) (ctor node (pi cs (let X (sort 1) T (List X)) T)))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("let_nested", nested),
        &["[K0016]", "Nested inductive occurrence of 'T'"],
    );
    let positive = r#"
(inductive L (sort 1) (ctor lnil L) (ctor lcons (pi h (let X (sort 1) Nat X) (pi t (let Y (sort 1) L Y) L))))
(def len (pi l L Nat) (lam l L (match l Nat (case (lnil) zero) (case (lcons h t ih) (succ ih)))))
(def main Nat (len (lcons zero (lcons zero (lcons zero lnil)))))
"#;
    assert_output_lines(
        &compile("let_positive", positive, "dynamic"),
        &["Result: Nat(3)"],
    );
    assert_output_lines(&compile("let_positive", positive, "typed"), &["Result: 3"]);
}

/// Positivity flipped the polarity at every arrow, so an occurrence under two arrows counted as
/// positive. `intro : ((A -> Prop) -> Prop) -> A` was accepted, and with the impredicative Prop
/// this program (the Coquand-Paulin paradox: `f P := intro (fun Q => P = Q)` is injective, then
/// the diagonal predicate `W x := exists P, f P = x /\ ~ P x`) was a closed, axiom-free proof of
/// False (exit 0). Strict positivity rejects any occurrence in the domain of an arrow; a
/// strictly positive infinitary field (`Nat -> Tr`) is still accepted.
#[test]
fn non_strictly_positive_inductive_is_rejected() {
    let paradox = r#"
(inductive A (sort 1) (ctor intro (pi g (pi p (pi a A (sort 0)) (sort 0)) A)))
(def cong (pi X (sort 1) (pi Y (sort 1) (pi k (pi #[once] x X Y)
            (pi x X (pi y X (pi e (Eq X x y) (Eq Y (k x) (k y))))))))
  (lam X (sort 1) (lam Y (sort 1) (lam k (pi #[once] x X Y) (lam x X (lam y X (lam e (Eq X x y)
    (match e (motive (lam b X (lam q (Eq X x b) (Eq Y (k x) (k b)))))
      (case (refl) (refl Y (k x)))))))))))
(def symm (pi X (sort 1) (pi x X (pi y X (pi e (Eq X x y) (Eq X y x)))))
  (lam X (sort 1) (lam x X (lam y X (lam e (Eq X x y)
    (match e (motive (lam b X (lam q (Eq X x b) (Eq X b x))))
      (case (refl) (refl X x))))))))
(def cast (pi P (sort 0) (pi Q (sort 0) (pi e (Eq (sort 0) P Q) (pi h P Q))))
  (lam P (sort 0) (lam Q (sort 0) (lam e (Eq (sort 0) P Q) (lam h P
    (match e (motive (lam b (sort 0) (lam q (Eq (sort 0) P b) b)))
      (case (refl) h)))))))
(def out (pi x A (pi p (pi a A (sort 0)) (sort 0)))
  (lam x A (match x (pi p (pi a A (sort 0)) (sort 0)) (case (intro g) g))))
(def sing (pi P (pi a A (sort 0)) (pi Q (pi a A (sort 0)) (sort 0)))
  (lam P (pi a A (sort 0)) (lam Q (pi a A (sort 0)) (Eq (pi a A (sort 0)) P Q))))
(def f (pi P (pi a A (sort 0)) A) (lam P (pi a A (sort 0)) (intro (sing P))))
(def f_inj (pi P (pi a A (sort 0)) (pi Q (pi a A (sort 0))
             (pi e (Eq A (f P) (f Q)) (Eq (pi a A (sort 0)) P Q))))
  (lam P (pi a A (sort 0)) (lam Q (pi a A (sort 0)) (lam e (Eq A (f P) (f Q))
    (symm (pi a A (sort 0)) Q P
      (cast (Eq (pi a A (sort 0)) P P) (Eq (pi a A (sort 0)) Q P)
            (cong (pi p (pi a A (sort 0)) (sort 0)) (sort 0)
                  (lam k (pi p (pi a A (sort 0)) (sort 0)) (k P)) (sing P) (sing Q)
                  (cong A (pi p (pi a A (sort 0)) (sort 0)) out (f P) (f Q) e))
            (refl (pi a A (sort 0)) P)))))))
(inductive W (pi x A (sort 0))
  (ctor w (pi x A (pi P (pi a A (sort 0)) (pi e (Eq A (f P) x) (pi n (pi h (P x) False) (W x)))))))
(def P0 (pi x A (sort 0)) (lam x A (W x)))
(def x0 A (f P0))
(def not_P0x0 (pi h (W x0) False)
  (lam h (W x0)
    (match h False
      (case (w P e n)
        ((cast (pi z (P x0) False) (pi z (P0 x0) False)
           (cong (pi a A (sort 0)) (sort 0) (lam Q (pi a A (sort 0)) (pi z (Q x0) False)) P P0 (f_inj P P0 e))
           n)
         h)))))
(def P0x0 (W x0) (w x0 P0 (refl A x0) not_P0x0))
(def boom False (not_P0x0 P0x0))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("coquand_paulin", paradox),
        &[
            "[K0015]",
            "Error registering inductive 'A'",
            "NonPositiveOccurrence(\"A\", \"intro\", 0)",
        ],
    );
    let double_negation = r#"
(inductive Bad (sort 0) (ctor mk (pi f (pi g (pi h Bad False) False) Bad)))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("double_negation", double_negation),
        &["[K0015]", "NonPositiveOccurrence(\"Bad\", \"mk\", 0)"],
    );
    let infinitary = r#"
(inductive Tr (sort 1) (ctor lf Tr) (ctor nd (pi k (pi n Nat Tr) Tr)))
(def isnode (pi t Tr Nat) (lam t Tr (match t Nat (case (lf) zero) (case (nd k) (succ zero)))))
(def main Nat (isnode (nd (lam n Nat lf))))
"#;
    assert_output_lines(
        &compile("infinitary", infinitary, "dynamic"),
        &["Result: Nat(1)"],
    );
}

/// Y2_recheck z04: the inductive being declared occurred in the index of a constructor's result
/// type (`base : T (T Tru -> False)`) and the declaration was accepted (exit 0); Lean 4 and Coq
/// reject it. An index that does not mention the inductive is still accepted.
#[test]
fn inductive_in_a_constructor_result_index_is_rejected() {
    let bad = r#"
(inductive Tru (sort 0) (ctor tt Tru))
(inductive T (pi P (sort 0) (sort 0))
  (ctor base (T (pi x (T Tru) False))))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("result_index", bad),
        &[
            "[K0015]",
            "Error registering inductive 'T'",
            "InductiveInCtorResultArg { ind: \"T\", ctor: \"base\", arg: 0 }",
        ],
    );
    let good = r#"
(inductive Tru (sort 0) (ctor tt Tru))
(inductive T (pi P (sort 0) (sort 0))
  (ctor base (T (pi x Tru False))))
(def main Nat zero)
"#;
    assert_accepted(&run_dynamic("result_index_ok", good));
}

/// Y2_recheck z05b: in `(inductive T (pi n Nat (sort 1)) (ctor mk (pi n Nat (T n))))` the
/// kernel infers `n` as a uniform parameter (`mk` returns `T` applied to its own first binder),
/// so `mk` has no field; the case `(case (mk n) n)` bound a variable the elaborator dropped, and
/// the body failed with `Unbound variable: n_g4` (the desugarer's name). The error now names the
/// case and the binder. A case that binds no variable is accepted, and a surplus binder that the
/// body does not use is still ignored.
#[test]
fn case_binding_a_parameter_reports_the_case() {
    let bad = r#"
(inductive T (pi n Nat (sort 1)) (ctor mk (pi n Nat (T n))))
(def f (pi t (T zero) Nat) (lam t (T zero) (match t Nat (case (mk n) n))))
(def main Nat (f (mk zero)))
"#;
    let run = run_dynamic("case_param", bad);
    assert_rejected_with(
        &run,
        &[
            "[F0223]",
            "Case mk in match on T binds 1 variable(s), but the constructor provides 0",
            "'n' is not bound",
        ],
    );
    assert!(
        !run.combined().contains("n_g"),
        "the message must not show the desugarer's name:\n{}",
        run.combined()
    );
    let no_binder = r#"
(inductive T (pi n Nat (sort 1)) (ctor mk (pi n Nat (T n))))
(def f (pi t (T (succ zero)) Nat) (lam t (T (succ zero)) (match t Nat (case (mk) (succ zero)))))
(def main Nat (f (mk (succ zero))))
"#;
    assert_output_lines(
        &compile("case_param_ok", no_binder, "dynamic"),
        &["Result: Nat(1)"],
    );
    let unused_surplus = r#"
(def g (pi b Bool Nat) (lam b Bool (match b Nat (case (true x) zero) (case (false) (succ zero)))))
(def main Nat (g false))
"#;
    assert_output_lines(
        &compile("case_surplus_unused", unused_surplus, "dynamic"),
        &["Result: Nat(1)"],
    );
}

/// Y2_verify_soundness F2: after a `copy` inductive failed its Copy derivation (`K0029`), its
/// zero-constructor placeholder stayed in the kernel environment: `(rec CF)` was accepted and a
/// corrected `(inductive CF ...)` failed with "Cannot redefine inductive 'CF': prelude is
/// frozen". Now the failed declaration leaves nothing behind.
#[test]
fn failed_copy_inductive_leaves_no_placeholder() {
    let leftover = r#"
(inductive copy CF (sort 1) (ctor cf (pi f (pi n Nat Nat) CF)))
(def elim_cf (pi c CF Nat) (lam c CF ((rec CF) (lam x CF Nat) c)))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("copy_leftover", leftover),
        &[
            "[K0029]",
            "CopyDeriveFailure",
            "Elaboration error (Type) in 'elim_cf': Unbound variable: CF",
        ],
    );
    let retry = r#"
(inductive copy CF (sort 1) (ctor cf (pi f (pi n Nat Nat) CF)))
(inductive CF (sort 1) (ctor cf2 (pi n Nat CF)))
(def get (pi c CF Nat) (lam c CF (match c Nat (case (cf2 n) n))))
(def main Nat (get (cf2 (succ (succ zero)))))
"#;
    let run = run_dynamic("copy_retry", retry);
    assert_rejected_with(&run, &["[K0029]", "CopyDeriveFailure"]);
    let errors = run
        .combined()
        .lines()
        .filter(|line| line.trim_start().starts_with("Error"))
        .count();
    assert!(
        errors == 1 && !run.combined().contains("Cannot redefine inductive"),
        "only the failed copy declaration may be reported;\nstdout:\n{}\nstderr:\n{}",
        run.stdout,
        run.stderr
    );
}

// -----------------------------------------------------------------------------------------------
// Y2 verification: large inductives through the backends
// -----------------------------------------------------------------------------------------------

/// Y2_verify_review problem 2 (pre-existing, reachable in (sort 1) since the universe rule no
/// longer constrains parameters): a field `x : F zero` for a type-family PARAMETER `F` has a
/// stuck type in the inductive's layout, so MIR typing saw the field place at a non-Copy type,
/// while lowering copied it because `K zero` (= Nat) is Copy: `[M300] ... Copy of non-Copy
/// place ... Opaque("app")` with both backends. The field is now moved out of the scrutinee
/// (docs/spec/mir/typing.md, "Fields of a stuck layout type"); the typed backend rejects the
/// program with TB010 (a partially known type) and `auto` falls back to the dynamic backend.
#[test]
fn type_family_parameter_field_is_read_at_run_time() {
    let family = r#"
(inductive Fam (pi F (pi n Nat (sort 1)) (sort 1)) (ctor mkf (pi F (pi n Nat (sort 1)) (pi x (F zero) (Fam F)))))
(def K (pi n Nat (sort 1)) (lam n Nat Nat))
(def get (pi p (Fam K) Nat) (lam p (Fam K) (match p Nat (case (mkf x) x))))
(def main Nat (get (mkf K (succ (succ (succ zero))))))
"#;
    let run = run_dynamic("param_family", family);
    assert_accepted(&run);
    assert_output_lines(
        &compile("param_family", family, "dynamic"),
        &["Result: Nat(3)"],
    );
    assert_rejected_with(&run_typed("param_family", family), &["[TB010]"]);
    assert_output_lines(
        &compile("param_family", family, "auto"),
        &["Result: Nat(3)"],
    );
}

/// Y2_verify_soundness F3 (pre-existing): an existential package (a type field and a value of
/// it) lives in (sort 2) under the universe rule. The typed backend lays the value field out as
/// `()` and rustc rejects its output (`E0308`; docs/spec/codegen/typed-backend.md, "Existential
/// fields (not supported)"); the dynamic backend runs it, and `auto` falls back to it.
#[test]
fn existential_package_runs_on_the_dynamic_backend() {
    let package = r#"
(inductive Pkg (sort 2) (ctor pkg (pi A (sort 1) (pi x A (pi f (pi a A Nat) Pkg)))))
(def use (pi p Pkg Nat) (lam p Pkg (match p Nat (case (pkg A x f) (f x)))))
(def main Nat (use (pkg Bool true (lam b Bool (match b Nat (case (true) (succ (succ (succ zero)))) (case (false) zero))))))
"#;
    assert_output_lines(
        &compile("existential", package, "dynamic"),
        &["Result: Nat(3)"],
    );
    let auto = compile("existential", package, "auto");
    let auto_text = auto.combined();
    assert!(
        auto.success
            && (auto_text
                .lines()
                .any(|line| line.trim() == "Result: Nat(3)")
                || auto_text.lines().any(|line| line.trim() == "Result: 3")),
        "expected the auto backend to compute 3;\nstdout:\n{}\nstderr:\n{}",
        auto.stdout,
        auto.stderr
    );
}

// -----------------------------------------------------------------------------------------------
// R4_editor #5: proof-typed closures are erased in MIR
// -----------------------------------------------------------------------------------------------

/// R4's probe: a token captured by a closure whose type is a proposition, then consumed. The
/// closure is an erased proof for the kernel (never built at run time, never called), so the
/// token is consumed exactly once. MIR used to lower the closure as a value that moved the token
/// (`M100 ... use of moved value`).
#[test]
fn proof_typed_closure_does_not_capture() {
    let source = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def burn (pi t Tok Nat) (lam t Tok (match t Nat (case (mk_tok n) (print_nat n)))))
(inductive Tru (sort 0) (ctor triv Tru))
(def f2 (pi k Tok Nat)
  (lam k Tok
    (let g (pi #[once] u Nat Tru) (lam #[once] u Nat (let n Nat (burn k) triv))
      (let a Tru (g zero) (burn k)))))
(def main Nat (f2 (mk_tok (succ (succ (succ zero))))))
"#;
    let run = run_typed("proof_closure_typed", source);
    assert_output_lines(&run, &["3", "Result: 3"]);
    assert_eq!(count_lines(&run, "3"), 1, "burn must run exactly once");
    let compiled = compile("proof_closure_dynamic", source, "dynamic");
    assert_output_lines(&compiled, &["3", "Result: Nat(3)"]);
    assert_eq!(count_lines(&compiled, "3"), 1, "burn must run exactly once");
}

/// Proof-typed closures (curried), a proof function COMPUTED by an application that would
/// consume the token, and a proof-function parameter, each passed twice: all duplicable, none
/// evaluated. Each was rejected by MIR with `M100`.
#[test]
fn proof_functions_are_copy_and_not_evaluated() {
    let curried = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def burn (pi t Tok Nat) (lam t Tok (match t Nat (case (mk_tok n) (print_nat n)))))
(inductive Tru (sort 0) (ctor triv Tru))
(def use2 (pi g (pi #[once] u Nat (pi #[once] v Nat Tru)) (pi h (pi #[once] u Nat (pi #[once] v Nat Tru)) Nat))
  (lam g (pi #[once] u Nat (pi #[once] v Nat Tru)) (lam h (pi #[once] u Nat (pi #[once] v Nat Tru))
    (let a Tru (g zero zero) (let b Tru (h zero zero) zero)))))
(def f (pi k Tok Nat)
  (lam k Tok
    (let g (pi #[once] u Nat (pi #[once] v Nat Tru)) (lam #[once] u Nat (lam #[once] v Nat (let n Nat (burn k) triv)))
      (let x Nat (use2 g g) (burn k)))))
(def main Nat (f (mk_tok (succ (succ zero)))))
"#;
    let run = run_typed("proof_curried", curried);
    assert_output_lines(&run, &["2", "Result: 2"]);
    assert_eq!(count_lines(&run, "2"), 1, "burn must run exactly once");

    let computed = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def burn (pi t Tok Nat) (lam t Tok (match t Nat (case (mk_tok n) (print_nat n)))))
(inductive Tru (sort 0) (ctor triv Tru))
(def mk (pi t Tok (pi u Nat Tru)) (lam t Tok (let n Nat (burn t) (lam u Nat triv))))
(def use2 (pi g (pi #[once] u Nat Tru) (pi h (pi #[once] u Nat Tru) Nat))
  (lam g (pi #[once] u Nat Tru) (lam h (pi #[once] u Nat Tru)
    (let a Tru (g zero) (let b Tru (h zero) zero)))))
(def f (pi k Tok Nat)
  (lam k Tok
    (let g (pi u Nat Tru) (mk k)
      (let x Nat (use2 g g) (burn k)))))
(def main Nat (f (mk_tok (succ (succ (succ (succ zero)))))))
"#;
    let run = run_typed("proof_computed", computed);
    assert_output_lines(&run, &["4", "Result: 4"]);
    assert_eq!(count_lines(&run, "4"), 1, "burn must run exactly once");
    assert_output_lines(
        &compile("proof_computed_dynamic", computed, "dynamic"),
        &["4", "Result: Nat(4)"],
    );

    let parameter = r#"
(inductive Tru (sort 0) (ctor triv Tru))
(def use2 (pi g (pi #[once] u Nat Tru) (pi h (pi #[once] u Nat Tru) Nat))
  (lam g (pi #[once] u Nat Tru) (lam h (pi #[once] u Nat Tru)
    (let a Tru (g zero) (let b Tru (h zero) (succ zero))))))
(def dup2 (pi g (pi #[once] u Nat Tru) Nat)
  (lam g (pi #[once] u Nat Tru) (use2 g g)))
(def main Nat (dup2 (lam #[once] u Nat triv)))
"#;
    assert_output_lines(&run_typed("proof_param", parameter), &["Result: 1"]);
    assert_output_lines(
        &compile("proof_param_dynamic", parameter, "dynamic"),
        &["Result: Nat(1)"],
    );
}

/// Proof-typed closures are built without captures, so (1) a body that just returns a captured
/// proof must not read the uncaptured variable (it is erased), and (2) in a generic function
/// (`cong`), a closure's type parameters that occur only inside a proposition (erased to `()`)
/// are not generic parameters of the Rust closure (rustc `E0283` "type annotations needed" when
/// the typed backend declared them).
#[test]
fn capture_free_proof_closures_compile_with_both_backends() {
    let returns_captured_proof = r#"
(inductive Holds (pi A (sort 1) (pi a A (sort 0)))
  (ctor holds (pi A (sort 1) (pi a A (pi w A (Holds A a))))))
(def k (pi A (sort 1) (pi a A (pi h (Holds A a) (pi u Nat (Holds A a)))))
  (lam A (sort 1) (lam a A (lam h (Holds A a) (lam u Nat h)))))
(def main Nat (let p (Holds Nat 2) (k Nat 2 (holds Nat 2 3) 4) 7))
"#;
    assert_output_lines(
        &run_typed("proof_returns_capture", returns_captured_proof),
        &["Result: 7"],
    );
    assert_output_lines(
        &compile(
            "proof_returns_capture_dyn",
            returns_captured_proof,
            "dynamic",
        ),
        &["Result: Nat(7)"],
    );
    let generic_cong = r#"
(def cong
  (pi A (sort 1) (pi B (sort 1) (pi f (pi x A B)
    (pi x A (pi y A (pi e (Eq A x y) (Eq B (f x) (f y))))))))
  (lam A (sort 1) (lam B (sort 1) (lam f (pi x A B)
    (lam x A (lam y A (lam e (Eq A x y)
      ((rec Eq) A x
        (lam y2 A (lam e2 (Eq A x y2) (Eq B (f x) (f y2))))
        (refl B (f x))
        y e))))))))
(def main Nat (let p (Eq Nat 1 1) (cong Nat Nat (lam n Nat n) 1 1 (refl Nat 1)) 5))
"#;
    assert_output_lines(&run_typed("generic_cong", generic_cong), &["Result: 5"]);
    assert_output_lines(
        &compile("generic_cong_dyn", generic_cong, "dynamic"),
        &["Result: Nat(5)"],
    );
}

// -----------------------------------------------------------------------------------------------
// R3_formal #23: nested captures of a mutable reference
// -----------------------------------------------------------------------------------------------

/// A variable that a closure holds through a borrowed capture, re-captured by a nested closure,
/// was borrowed as the capture local itself (`&mut &mut Tok`), so the nested body saw it at the
/// wrong type (`M300 MIR typing error ... Assignment type mismatch`). With three levels, closure
/// bodies also reused region numbers of their captured types (spurious `M206`/`M200`).
#[test]
fn nested_closures_reborrow_a_captured_mutable_reference() {
    let two_levels = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def poke (pi r (Ref #[r] Mut Tok) Nat) (lam r (Ref #[r] Mut Tok) (succ zero)))
(def f (pi t Tok Nat) (lam t Tok (let m (Ref #[r] Mut Tok) (&mut t)
  (let g (pi #[mut] u Nat Nat)
         (lam #[mut] u Nat (let h (pi #[mut] v Nat Nat) (lam #[mut] v Nat (poke m)) (h zero)))
    (add (g zero) (poke m))))))
(def main Nat (f (mk_tok 2)))
"#;
    assert_output_lines(&run_typed("nested_mut2", two_levels), &["Result: 2"]);
    assert_output_lines(
        &compile("nested_mut2_dynamic", two_levels, "dynamic"),
        &["Result: Nat(2)"],
    );
    let three_levels = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def poke (pi r (Ref #[r] Mut Tok) Nat) (lam r (Ref #[r] Mut Tok) (succ zero)))
(def f (pi t Tok Nat) (lam t Tok (let m (Ref #[r] Mut Tok) (&mut t)
  (let g (pi #[mut] u Nat Nat)
         (lam #[mut] u Nat
           (let h (pi #[mut] v Nat Nat)
                  (lam #[mut] v Nat (let k (pi #[mut] w Nat Nat) (lam #[mut] w Nat (poke m)) (k zero)))
             (add (h zero) (h zero))))
    (add (g zero) (poke m))))))
(def main Nat (f (mk_tok 2)))
"#;
    assert_output_lines(&run_typed("nested_mut3", three_levels), &["Result: 3"]);
    assert_output_lines(
        &compile("nested_mut3_dynamic", three_levels, "dynamic"),
        &["Result: Nat(3)"],
    );
}

/// The program of R3's report (made non-curried): an FnMut closure reborrowing a captured `&mut`
/// in the succ case of a match on Nat. Its lowering errors (`M300`, `M206`, `M200`) are fixed; it
/// is still rejected by MIR for two documented reasons (`M100`, `M203`; see
/// `case_studies/tools/stage_matrix/gaps/g7_fnmut_minor_reborrow.lrl`), which this test does not
/// pin down.
#[test]
fn fnmut_reborrow_in_a_recursive_case_has_no_lowering_errors() {
    let source = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi n Nat Tok)))
(def poke (pi r (Ref #[r] Mut Tok) Nat) (lam r (Ref #[r] Mut Tok) (succ zero)))
(def f (pi n Nat (pi t Tok Nat)) (lam n Nat (lam t Tok (let m (Ref #[r] Mut Tok) (&mut t)
  (match n Nat
    (case (zero) zero)
    (case (succ p ih) (let g (pi #[mut] u Nat Nat) (lam #[mut] u Nat (poke m)) (add (g 0) ih))))))))
"#;
    let text = run_dynamic("fnmut_minor", source).combined();
    for code in ["[M300]", "[M206]", "[M200]", "[K0"] {
        assert!(!text.contains(code), "unexpected {}:\n{}", code, text);
    }
}

// -----------------------------------------------------------------------------------------------
// R1_claims_vs_code #7: lifetime elision once per signature
// -----------------------------------------------------------------------------------------------

/// The elision rule (an unlabelled reference result needs exactly one input lifetime) applies to
/// the complete signature, not to each curried suffix: a reference argument followed by a value
/// argument used to be rejected (`F0208`) because the suffix `(pi n Nat (Ref Shared Nat))` has no
/// input reference.
#[test]
fn lifetime_elision_is_checked_once_per_signature() {
    for (name, source) in [
        (
            "elide_ref_then_nat",
            "(def pick1 (pi a (Ref Shared Nat) (pi n Nat (Ref Shared Nat))) (lam a (Ref Shared Nat) (lam n Nat a)))\n",
        ),
        (
            "elide_label_then_nat",
            "(def pick3 (pi a (Ref #[a] Shared Nat) (pi n Nat (Ref Shared Nat))) (lam a (Ref #[a] Shared Nat) (lam n Nat a)))\n",
        ),
        (
            "elide_nat_then_ref",
            "(def pick2 (pi n Nat (pi a (Ref Shared Nat) (Ref Shared Nat))) (lam n Nat (lam a (Ref Shared Nat) a)))\n",
        ),
    ] {
        assert_accepted(&run_dynamic(name, source));
    }
    // A local function with such a signature, applied to a borrow.
    let local_use = r#"
(def use1 (pi x Nat Nat) (lam x Nat
  (let pick1 (pi a (Ref Shared Nat) (pi n Nat (Ref Shared Nat))) (lam a (Ref Shared Nat) (lam n Nat a))
    (let r (Ref #[r] Shared Nat) (& x) (let s (Ref #[r] Shared Nat) (pick1 r zero) zero)))))
(def main Nat (use1 (succ zero)))
"#;
    assert_output_lines(
        &compile("elide_local_use", local_use, "dynamic"),
        &["Result: Nat(0)"],
    );
    // Still ambiguous: two input references (anywhere in the chain), or none (here in the
    // signature of a function-typed argument, which is a signature of its own).
    for (name, source) in [
        (
            "elide_two_refs",
            "(def pick (pi a (Ref Shared Nat) (pi n Nat (pi b (Ref Shared Nat) (Ref Shared Nat))))\n  (lam a (Ref Shared Nat) (lam n Nat (lam b (Ref Shared Nat) a))))\n",
        ),
        (
            "elide_no_ref",
            "(def bad (pi f (pi n Nat (Ref Shared Nat)) Nat) (lam f (pi n Nat (Ref Shared Nat)) zero))\n",
        ),
    ] {
        assert_rejected_with(
            &run_dynamic(name, source),
            &["[F0208]", "Ambiguous lifetime in return type"],
        );
    }
}

// -----------------------------------------------------------------------------------------------
// K_repair (H_inductives #1 / H_universes_elim #1): a constructor field that follows a recursive
// field, and whose type depends on an earlier field, must keep its declared type through the
// recursor and `match`. The buggy recursor demanded the wrong type, accepting ill-typed bodies
// and rejecting well-typed ones; from it a closed proof of `False` could be built.

/// Program whose `node` case uses the dependent field at its declared type; well-typed, accepted.
const DEP_FIELD_WELL_TYPED: &str = r#"
(inductive Tag (pi n Nat (sort 1)) (ctor tag (pi n Nat (Tag n))))
(inductive T (sort 1)
  (ctor leaf T)
  (ctor node (pi r T (pi n Nat (pi v (Tag n) T)))))
(def getn (pi n Nat (pi v (Tag n) Nat)) (lam n Nat (lam v (Tag n) n)))
(def size (pi t T Nat)
  (lam t T
    (match t Nat
      (case (leaf) zero)
      (case (node r ih n v) (succ (getn n v))))))
(def main Nat (size (node leaf (succ zero) (tag (succ zero)))))
"#;

/// Same type, but the `node` case uses the dependent field at the type of a different field
/// (`getn ih v` instead of `getn n v`); ill-typed, rejected.
const DEP_FIELD_ILL_TYPED: &str = r#"
(inductive Tag (pi n Nat (sort 1)) (ctor tag (pi n Nat (Tag n))))
(inductive T (sort 1)
  (ctor leaf T)
  (ctor node (pi r T (pi n Nat (pi v (Tag n) T)))))
(def getn (pi n Nat (pi v (Tag n) Nat)) (lam n Nat (lam v (Tag n) n)))
(def size (pi t T Nat)
  (lam t T
    (match t Nat
      (case (leaf) zero)
      (case (node r ih n v) (succ (getn ih v))))))
(def main Nat (size (node leaf (succ zero) (tag (succ zero)))))
"#;

#[test]
fn dependent_field_after_recursive_field_is_typed_at_its_declared_type() {
    assert_output_lines(
        &run_typed("dep_field_ok", DEP_FIELD_WELL_TYPED),
        &["Result: 2"],
    );
    assert_rejected_with(
        &run_dynamic("dep_field_bad", DEP_FIELD_ILL_TYPED),
        &["[F0214]"],
    );
}

/// The exploit the recursor bug enabled: a closed proof of `False` (and ex falso) with no axioms.
/// It must be rejected; the recursor no longer gives the constructor field `c : TagEq b d` the
/// type `TagEq a b`, so `C` (or `zero_is_one`) fails to elaborate.
const FALSE_FROM_RECURSOR: &str = r#"
(inductive TagEq (pi x Nat (pi y Nat (sort 1)))
  (ctor tagrefl (pi n Nat (TagEq n n))))
(inductive T (sort 1)
  (ctor leaf T)
  (ctor node (pi r T (pi a Nat (pi b Nat (pi d Nat (pi c (TagEq b d) T)))))))
(def tag_to_eq (pi x Nat (pi y Nat (pi t (TagEq x y) (Eq Nat x y))))
  (lam x Nat (lam y Nat (lam t (TagEq x y)
    ((rec TagEq) x (lam y2 Nat (lam t2 (TagEq x y2) (Eq Nat x y2))) (refl Nat x) y t)))))
(def C (pi t T (sort 0))
  (lam t T ((rec T) (lam t2 T (sort 0))
     (Eq Nat zero zero)
     (lam r T (lam ih (sort 0) (lam a Nat (lam b Nat (lam d Nat (lam c (TagEq a b) (Eq Nat a b)))))))
     t)))
(def zero_is_one (Eq Nat zero (succ zero))
  ((rec T) C
     (refl Nat zero)
     (lam r T (lam ih (C r) (lam a Nat (lam b Nat (lam d Nat (lam c (TagEq a b) (tag_to_eq a b c)))))))
     (node leaf zero (succ zero) (succ zero) (tagrefl (succ zero)))))
(def is_zero (pi n Nat (sort 0))
  (lam n Nat ((rec Nat) (lam k Nat (sort 0)) (Eq Nat zero zero) (lam m Nat (lam ih (sort 0) False)) n)))
(def boom False
  ((rec Eq) Nat zero (lam b Nat (lam e (Eq Nat zero b) (is_zero b))) (refl Nat zero) (succ zero) zero_is_one))
(def main Nat zero)
"#;

#[test]
fn recursor_bug_cannot_prove_false() {
    assert_rejected_with(
        &run_dynamic("false_from_recursor", FALSE_FROM_RECURSOR),
        &["[F0214]"],
    );
}

// -----------------------------------------------------------------------------------------------
// K_repair (H_universes_elim #3): a family whose index telescope is dependent can be eliminated.

const DEP_INDEX_FAMILY: &str = r#"
(inductive D (pi A (sort 1) (pi x A (sort 1)))
  (ctor dmk (D Nat zero)))
(def use_d (pi d (D Nat zero) Nat)
  (lam d (D Nat zero) ((rec D) (lam A (sort 1) (lam x A (lam e (D A x) Nat))) (succ zero) Nat zero d)))
(def main Nat (use_d dmk))
"#;

#[test]
fn dependent_index_family_can_be_eliminated() {
    assert_output_lines(
        &run_typed("dep_index_family", DEP_INDEX_FAMILY),
        &["Result: 1"],
    );
}

// -----------------------------------------------------------------------------------------------
// K_repair (H_inductives #2): redeclaring an inductive (only possible under --allow-redefine) as
// `affine` must drop the Copy instance derived for the previous declaration, so an affine value
// cannot be used twice.

const REDEFINE_AFFINE: &str = r#"
(inductive Box (sort 1) (ctor mk (pi n Nat Box)))
(inductive (affine) Box (sort 1) (ctor mk (pi n Nat Box)))
(def unbox (pi b Box Nat) (lam b Box (match b Nat (case (mk n) n))))
(def twice (pi b Box Nat) (lam b Box (add (unbox b) (unbox b))))
(def main Nat (twice (mk (succ zero))))
"#;

#[test]
fn redefining_an_inductive_as_affine_drops_its_copy_instance() {
    let run = run_cli(
        "redefine_affine",
        REDEFINE_AFFINE,
        &["--allow-redefine", "run", "{file}"],
    );
    assert_rejected_with(&run, &["[K0021]", "UseAfterMove", "twice"]);
}

// -----------------------------------------------------------------------------------------------
// K_repair round 2 (verifier-confirmed findings on fixpoints, conversion and redefinition).

/// T-Fix lifts the annotation over the recursive binder (kernel and elaborator): the fixpoint
/// below returned `ret B` at type `Nat -> Comp A` and was accepted (`Result: ret`), while the
/// well-typed version returning `ret A` was rejected with `A_g3 vs B_g4`.
#[test]
fn fixpoint_body_is_checked_against_the_lifted_annotation() {
    let ill_typed = r#"
(partial cast (pi A (sort 1) (pi B (sort 1) (pi n Nat (Comp A))))
  (lam A (sort 1) (lam B (sort 1)
    (fix go (pi n Nat (Comp A)) (lam n Nat (ret B))))))
(partial main (Comp Nat) (ret Nat))
"#;
    assert_rejected_with(
        &run_dynamic("fix_lift_bad", ill_typed),
        &["[F0214]", "in 'cast'", "Unification failed"],
    );
    let well_typed = r#"
(partial ok (pi A (sort 1) (pi B (sort 1) (pi n Nat (Comp A))))
  (lam A (sort 1) (lam B (sort 1)
    (fix go (pi n Nat (Comp A)) (lam n Nat (ret A))))))
(partial main (Comp Nat) (ret Nat))
"#;
    assert_accepted(&run_dynamic("fix_lift_ok", well_typed));
}

/// A fixpoint may not return a proof (K0055): the looping `go` "proved" `Eq Nat (succ zero) zero`;
/// proofs are erased, so transport along it made compiled code use `true` as a `Nat` (the typed
/// binary panicked, the dynamic one took the `zero` branch).
#[test]
fn fixpoint_returning_a_proof_is_rejected() {
    let source = r#"
(def transport
  (pi {A (sort 1)} (pi P (pi a A (sort 1)) (pi {x A} (pi {y A}
    (pi e (Eq A x y) (pi px (P x) (P y)))))))
  (lam {A} (sort 1) (lam P (pi a A (sort 1)) (lam {x} A (lam {y} A
    (lam e (Eq A x y) (lam px (P x)
      (match e (motive (lam b A (lam w (Eq A x b) (P b))))
        (case (refl) px)))))))))
(def F (pi n Nat (sort 1))
  (lam n Nat (match n (sort 1) (case (zero) Nat) (case (succ m ih) Bool))))
(partial castuse (pi e (Eq Nat (succ zero) zero) (Comp Nat))
  (lam e (Eq Nat (succ zero) zero)
    (match (transport F e true) (Comp Nat)
      (case (zero) (ret Nat))
      (case (succ m ih) (bind Nat Nat (ret Nat) (ret Nat))))))
(partial main (Comp Nat)
  (castuse ((fix go (pi n Nat (Eq Nat (succ zero) zero)) (lam n Nat (go n))) zero)))
"#;
    assert_rejected_with(
        &run_dynamic("fix_proof", source),
        &["[K0055]", "FixProofCodomain"],
    );
    assert_rejected_with(
        &compile("fix_proof_typed", source, "typed"),
        &["[K0055]", "FixProofCodomain"],
    );
}

/// Type checking never unfolds a fixpoint (K0049), also when it exposes a Pi for an application:
/// `zero` was accepted at the domain `T zero` of a type family defined by `fix`, and a stuck
/// fixpoint application in an inferred type made the checker unfold it until the stack overflowed
/// (abort, exit 134, no diagnostic).
#[test]
fn fixpoint_in_a_type_is_reported_not_unfolded() {
    let typed_by_unfolding = r#"
(partial pd2 (pi n Nat (Comp Nat))
  (lam n Nat
    ((lam F (pi m Nat (sort 1)) (lam x (F zero) (ret Nat)))
     (fix T (pi m Nat (sort 1)) (lam m Nat Nat))
     zero)))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_dynamic("fix_tapp", typed_by_unfolding),
        &["[K0049]", "in 'pd2'"],
    );
    let stuck_in_type = r#"
(partial pd (pi n Nat (Comp Nat))
  (lam n Nat
    ((lam f (pi x Nat Nat) (lam p (Eq Nat (f n) (f n)) (ret Nat)))
     (fix g (pi x Nat Nat) (lam x Nat (match x Nat (case (zero) zero) (case (succ k ih) (g k)))))
     (refl Nat ((fix g (pi x Nat Nat) (lam x Nat (match x Nat (case (zero) zero) (case (succ k ih) (g k))))) n)))))
(def main Nat zero)
"#;
    let run = run_dynamic("fix_stuck_type", stuck_in_type);
    assert_rejected_with(&run, &["[K0049]", "in 'pd'"]);
    assert!(
        !run.combined().contains("overflow"),
        "no stack overflow:\n{}",
        run.combined()
    );
}

/// A top-level expression may not contain `fix` (C0008), as no declaration other than `partial`
/// may: a looping fixpoint in an expression was unfolded without bound when the expression was
/// evaluated for display (stack overflow, exit 134).
#[test]
fn top_level_expression_may_not_contain_fix() {
    let source = r#"
((fix go (pi n Nat Nat) (lam n Nat (go n))) zero)
(def main Nat zero)
"#;
    let run = run_dynamic("fix_expr", source);
    assert_rejected_with(
        &run,
        &["[C0008]", "fix is only allowed in partial definitions"],
    );
    assert!(!run.combined().contains("Eval:"), "{}", run.combined());
}

/// Under `--allow-redefine`, a name that other definitions refer to can no longer be redefined
/// (K0054): `p : Eq Nat zero c` checked with `c := zero` proved `Eq Nat zero (succ zero)` after
/// `c := succ zero`, and with it `False`; a value of an inductive redeclared empty inhabited it.
#[test]
fn redefining_a_referenced_name_is_refused() {
    let stale_proof = r#"
(def c Nat zero)
(def p (Eq Nat zero c) (refl Nat zero))
(def c Nat (succ zero))
(def q (Eq Nat zero (succ zero)) p)
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_cli(
            "redef_value",
            stale_proof,
            &["--allow-redefine", "run", "{file}"],
        ),
        &["[K0054]", "RedefinitionWithDependents", "\"p\""],
    );
    let stale_value = r#"
(inductive B (sort 0) (ctor mk B))
(def x B mk)
(inductive B (sort 0))
(def bad False ((rec B) (lam y B False) x))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_cli(
            "redef_ind",
            stale_value,
            &["--allow-redefine", "run", "{file}"],
        ),
        &["[K0054]", "Error registering inductive 'B'", "\"x\""],
    );
}

/// A self-referential total definition (possible under `--allow-redefine`: the new body names the
/// old definition) is unfolded only when its decreasing argument is a constructor: the stuck call
/// `myadd n zero` in `t1`'s type had an infinite normal form (stack overflow, exit 134).
#[test]
fn self_referential_redefinition_has_finite_normal_forms() {
    let source = r#"
(def myadd (pi n Nat (pi m Nat Nat)) (lam n Nat (lam m Nat m)))
(def myadd (pi n Nat (pi m Nat Nat))
  (lam n Nat
    (lam m Nat
      (match n Nat
        (case (zero) m)
        (case (succ k ih) (succ (myadd k m)))))))
(def t1 (pi n Nat (Eq Nat (myadd n zero) (myadd n zero)))
  (lam n Nat (refl Nat (myadd n zero))))
(def main Nat (myadd (succ (succ zero)) (succ zero)))
"#;
    assert_output_lines(
        &run_cli(
            "selfref_redef",
            source,
            &["--allow-redefine", "run", "{file}", "--backend", "typed"],
        ),
        &["Result: 3"],
    );
}

/// The definitional-equality budget counts β steps: 2^16 iterations of the identity on Church
/// numerals (no δ step inside the loop) were decided with `--defeq-fuel 1000` (only δ, ι and
/// fixpoint unfolding were charged).
#[test]
fn defeq_budget_counts_beta_steps() {
    let source = r#"
(def C (sort 2) (pi X (sort 1) (pi f (pi x X X) (pi x X X))))
(def two C (lam X (sort 1) (lam f (pi x X X) (lam x X (f (f x))))))
(def t (Eq Nat
          ((lam pow (pi m C (pi n C C)) ((pow two (pow two (pow two two))) Nat (lam k Nat k) zero))
           (lam m C (lam n C (lam X (sort 1) (n (pi x X X) (m X))))))
          zero)
  (refl Nat zero))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_cli(
            "beta_fuel",
            source,
            &["--defeq-fuel", "1000", "run", "{file}"],
        ),
        &["[K0048]", "fuel exhausted", "in 't'"],
    );
}

/// The termination checker accepted any application of a constant named `proj` to a smaller term
/// as smaller, by name alone. With `--allow-redefine`, a total definition may refer to itself, so
/// `f (succ m) := f (proj m)` (with `proj k := succ k`) passed the check and proved False.
#[test]
fn termination_check_does_not_trust_a_constant_named_proj() {
    let source = r#"
(def D (pi n Nat (sort 0))
  (lam n Nat (match n (sort 0) (case (zero) (Eq Nat zero zero)) (case (succ m ih) False))))
(def proj (pi k Nat Nat) (lam k Nat (succ k)))
(axiom f (pi n Nat (D n)))
(def f (pi n Nat (D n))
  (lam n Nat
    (match n (motive (lam k Nat (D k)))
      (case (zero) (refl Nat zero))
      (case (succ m ih) (f (proj m))))))
(def boom False (f (succ zero)))
(def main Nat zero)
"#;
    assert_rejected_with(
        &run_cli("proj_redef", source, &["--allow-redefine", "run", "{file}"]),
        &["[K0019]", "NonSmallerArgument"],
    );
}
