//! Regression tests for compiler bugs found while writing the case studies under
//! `case_studies/` (vectors, protocol channel, ownership corpus, comparison programs, stage
//! matrix). Each test names the minimal reproduction it was derived from and checks the fixed
//! behaviour end to end through the real CLI, run from the repository root.

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
        "lrl_case_study_regr_{}_{}_{}",
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

/// W_A_vectors_6: a type argument that is a type APPLICATION (`List Nat`) was lowered as a call
/// of the erased type constructor and the compiled program panicked at run time in both
/// backends (`Expected Func` / "attempted to execute erased function literal").
#[test]
fn type_application_passed_as_argument_is_erased() {
    let source = r#"
(def k (pi A (sort 1) (pi x Nat Nat)) (lam A (sort 1) (lam x Nat x)))
(def T (pi n Nat (sort 1)) (lam n Nat (match n (sort 1) (case (zero) Bool) (case (succ j ih) Nat))))
(def main Nat (add (k (List Nat) 5) (add (k (Pair Nat Bool) 1) (k (T 3) 1))))
"#;
    assert_output_lines(&run_typed("type_app_typed", source), &["Result: 7"]);
    assert_output_lines(
        &compile("type_app_dynamic", source, "dynamic"),
        &["Result: Nat(7)"],
    );
}

/// W_D_lrl_compare_6: unary `Nat` literals make deep terms; a literal of 300 overflowed the
/// compiler's main-thread stack (abort, exit status 134). The compiler now runs on a thread with
/// a large stack.
#[test]
fn large_nat_literal_does_not_overflow_the_compiler_stack() {
    let source = "(def main Nat (print_nat 1000))\n";
    let run = run_dynamic("large_literal_dynamic", source);
    assert_accepted(&run);
    assert_output_lines(
        &run_typed("large_literal_typed", source),
        &["1000", "Result: 1000"],
    );
}

/// W_B_protocol_1 / W_D_lrl_compare_4: a Copy field (`List Nat`) read out of a value of an
/// `affine` inductive was rejected by MIR (`M300` "Copy of non-Copy place" and `M101`), because
/// MIR treated every inductive-typed projection of a non-Copy value as non-Copy. MIR now decides
/// Copy-ness of inductives with the kernel's Copy instances. The affine field is still moved.
#[test]
fn copy_field_of_an_affine_value_can_be_read() {
    let source = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi id Nat Tok)))
(inductive (affine) Rec2 (sort 1)
  (ctor mk_rec2 (pi log (List Nat) (pi other (List Nat) (pi tok Tok Rec2)))))
(def sum (pi l (List Nat) Nat)
  (lam l (List Nat) (match l Nat (case (nil) zero) (case (cons h t ih) (add h ih)))))
(def burn (pi t Tok Nat) (lam t Tok (match t Nat (case (mk_tok i) i))))
(def total (pi r Rec2 Nat)
  (lam r Rec2 (match r Nat (case (mk_rec2 log other tok) (add (sum log) (add (sum other) (burn tok)))))))
(def main Nat (total (mk_rec2 (cons 1 (cons 2 nil)) (cons 3 nil) (mk_tok 4))))
"#;
    assert_accepted(&run_dynamic("affine_copy_field_run", source));
    assert_output_lines(
        &run_typed("affine_copy_field_typed", source),
        &["Result: 10"],
    );
    assert_output_lines(
        &compile("affine_copy_field_dynamic", source, "dynamic"),
        &["Result: Nat(10)"],
    );
}

/// W_A_vectors_1 / W_D_lrl_compare_3: an implicit argument under a binder of a definition's
/// TYPE was not substituted before the kernel computed the type's sort ("Unresolved
/// metavariable ?0", K0047).
#[test]
fn implicit_arguments_in_definition_types_are_inferred() {
    let source = r#"
(def idn (pi {A (sort 1)} (pi x A A)) (lam {A} (sort 1) (lam x A x)))
(def bad (pi n Nat (Eq Nat (idn n) n)) (lam n Nat (refl Nat n)))
(def u3 (pi l (List Nat) (Eq (List Nat) (cons 1 l) (cons 1 l)))
  (lam l (List Nat) (refl (List Nat) (cons 1 l))))
(def main Nat (idn 4))
"#;
    assert_accepted(&run_dynamic("implicit_in_type", source));
    assert_output_lines(&run_typed("implicit_in_type_typed", source), &["Result: 4"]);
}

/// W_D_lrl_compare_2: a `match` on an application whose implicit arguments are inferred
/// (`(cons 1 nil)`) failed with K0047.
#[test]
fn match_on_an_application_with_inferred_implicit_arguments() {
    let source = r#"
(def t5 Nat (match (cons 1 nil) Nat (case (nil) zero) (case (cons h t ih) h)))
(def t6 Nat (match (cons 4 (cons 5 nil)) Nat (case (nil) zero) (case (cons h t ih) (add h ih))))
(def main Nat (add t5 t6))
"#;
    assert_output_lines(&run_typed("match_app_scrutinee", source), &["Result: 10"]);
}

/// W_A_vectors_2 / W_D_lrl_compare_1: a constraint postponed before the arguments solved the
/// implicit arguments (`pred ?n =?= m`, `add ?n ?n =?= 2`) was retried without substituting
/// the solution inside the terms, and stayed unsolved (F0217).
#[test]
fn postponed_constraints_see_solved_implicit_arguments() {
    let source = r#"
(def pred (pi n Nat Nat) (lam n Nat (match n Nat (case (zero) zero) (case (succ k ih) k))))
(def lem (pi {n Nat} (pi e (Eq Nat n n) (Eq Nat (pred n) (pred n))))
  (lam {n} Nat (lam e (Eq Nat n n) (refl Nat (pred n)))))
(def use_inferred (pi m Nat (Eq Nat m m)) (lam m Nat (lem (refl Nat (succ m)))))
(inductive B (pi n Nat (sort 1)) (ctor mk (pi {n Nat} (pi v Nat (B n)))))
(def dbl (pi {n Nat} (pi b (B n) (B (add n n))))
  (lam {n} Nat (lam b (B n) (match b (B (add n n)) (case (mk v) (mk (add v v)))))))
(def one (B 1) (mk 3))
(def two (B 2) (dbl one))
(def main Nat (match two Nat (case (mk v) v)))
"#;
    assert_output_lines(&run_typed("postponed_typed", source), &["Result: 6"]);
    assert_output_lines(
        &compile("postponed_dynamic", source, "dynamic"),
        &["Result: Nat(6)"],
    );
    // The same application at a wrong index is still a type error.
    let wrong = source.replace("(def two (B 2) (dbl one))", "(def two (B 3) (dbl one))");
    assert_rejected_with(&run_dynamic("postponed_wrong", &wrong), &["'two'"]);
}

/// W_A_vectors_3: a lambda whose body still contained a solved but unsubstituted implicit
/// argument was classified FnOnce (a capture used only inside a proof counted as moved) and
/// rejected against an `Fn` type (F0206).
#[test]
fn closure_kind_with_inferred_implicit_arguments_in_proofs() {
    let source = r#"
(def idn (pi {A (sort 1)} (pi x A A)) (lam {A} (sort 1) (lam x A x)))
(def cap_inferred (pi {A (sort 1)} (pi x A (pi y A (Eq A (idn {A} x) (idn {A} x)))))
  (lam {A} (sort 1) (lam x A (lam y A (refl A (idn x))))))
"#;
    assert_accepted(&run_dynamic("closure_kind_metas", source));
}

/// Found while re-running case study A's probes: `min1 ?k =?= succ zero` (a definition applied
/// to an unsolved implicit argument against a constructor) was reported as a definitive
/// unification failure (F0214) before the expected type fixed `?k`; it is now postponed.
/// `vtail` through a split of the vector then elaborates with every implicit argument inferred.
#[test]
fn stuck_definition_applications_are_postponed() {
    let source = r#"
(inductive Vec (pi A (sort 1) (pi n Nat (sort 1)))
  (ctor vnil (pi {A (sort 1)} (Vec A zero)))
  (ctor vcons (pi {A (sort 1)} (pi {n Nat} (pi h A (pi t (Vec A n) (Vec A (succ n))))))))
(def pred (pi n Nat Nat) (lam n Nat (match n Nat (case (zero) zero) (case (succ k ih) k))))
(def min1 (pi n Nat Nat) (lam n Nat (match n Nat (case (zero) zero) (case (succ k ih) 1))))
(def vappend (pi {A (sort 1)} (pi {n Nat} (pi {m Nat}
               (pi xs (Vec A n) (pi #[once] ys (Vec A m) (Vec A (add n m)))))))
  (lam {A} (sort 1) (lam {n} Nat (lam {m} Nat (lam xs (Vec A n) (lam #[once] ys (Vec A m)
    (match xs (motive (lam k Nat (lam w (Vec A k) (Vec A (add k m)))))
      (case (vnil) ys)
      (case (vcons h t ih) (vcons h ih)))))))))
(inductive VSplit (pi A (sort 1) (pi k Nat (sort 1)))
  (ctor vsplit_mk (pi {A (sort 1)} (pi {k Nat}
    (pi hd (Vec A (min1 k)) (pi tl (Vec A (pred k)) (VSplit A k)))))))
(def vjoin (pi {A (sort 1)} (pi {k Nat} (pi #[once] s (VSplit A k) (Vec A k))))
  (lam {A} (sort 1) (lam {k} Nat (lam #[once] s (VSplit A k)
    ((match k (motive (lam j Nat (pi #[once] p (VSplit A j) (Vec A j))))
       (case (zero) (lam #[once] p (VSplit A zero) vnil))
       (case (succ j ih) (lam #[once] p (VSplit A (succ j))
          (match p (Vec A (succ j)) (case (vsplit_mk hd tl) (vappend hd tl))))))
     s)))))
(def vsplit (pi {A (sort 1)} (pi {n Nat} (pi v (Vec A n) (VSplit A n))))
  (lam {A} (sort 1) (lam {n} Nat (lam v (Vec A n)
    (match v (motive (lam k Nat (lam w (Vec A k) (VSplit A k))))
      (case (vnil) (vsplit_mk vnil vnil))
      (case (vcons h t ih) (vsplit_mk (vcons h vnil) (vjoin ih))))))))
(def vtail (pi {A (sort 1)} (pi {n Nat} (pi v (Vec A (succ n)) (Vec A n))))
  (lam {A} (sort 1) (lam {n} Nat (lam v (Vec A (succ n))
    (match (vsplit v) (Vec A n) (case (vsplit_mk hd tl) tl))))))
(def vsum (pi {n Nat} (pi v (Vec Nat n) Nat))
  (lam {n} Nat (lam v (Vec Nat n)
    (match v Nat (case (vnil) zero) (case (vcons h t ih) (add h ih))))))
(def main Nat (vsum (vtail (vcons 1 (vcons 2 (vcons 3 vnil))))))
"#;
    assert_output_lines(&run_typed("vtail_split_typed", source), &["Result: 5"]);
    assert_output_lines(
        &compile("vtail_split_dynamic", source, "dynamic"),
        &["Result: Nat(5)"],
    );
}

/// W_A_vectors_8: a generic function whose type binders are `#[once]` (as the prelude's
/// `pair_fst`/`pair_snd`) could not be called with the typed backend (rustc E0283): copy
/// propagation replaced the local holding the generic function by the constant at the call,
/// leaving the local without any use from which rustc could infer its type arguments.
#[test]
fn generic_function_with_once_type_binders_runs_with_the_typed_backend() {
    let source = r#"
(def myfst (pi #[once] A (sort 1) (pi #[once] B (sort 1) (pi #[once] p (Pair A B) A)))
  (lam #[once] A (sort 1) (lam #[once] B (sort 1) (lam #[once] p (Pair A B) (match p A (case (mk_pair a b) a))))))
(def main Nat (add (myfst Nat Nat (mk_pair 5 6))
  (add (pair_fst Nat Nat (mk_pair 1 2)) (pair_snd (List Nat) Nat (mk_pair (cons 1 nil) 3)))))
"#;
    assert_output_lines(
        &run_typed("once_type_binders_typed", source),
        &["Result: 9"],
    );
    assert_output_lines(
        &compile("once_type_binders_dynamic", source, "dynamic"),
        &["Result: Nat(9)"],
    );
}

/// W_C_corpus_3: a macro parameter was substituted for every symbol of its name in a
/// quasiquoted template, also where it was not unquoted; a parameter named `ctor` replaced the
/// keyword `ctor` of the generated declaration (F0102). Only unquoted occurrences are replaced.
#[test]
fn quasiquoted_template_keeps_keywords_named_like_parameters() {
    let source = r#"
(defmacro defchan (name ctor) `(inductive ,name (sort 1) (ctor ,ctor (pi id Nat ,name))))
(defchan Chan mk_chan)
(def get (pi c Chan Nat) (lam c Chan (match c Nat (case (mk_chan id) id))))
(def main Nat (get (mk_chan 3)))
"#;
    assert_output_lines(&run_typed("defchan_ctor_param", source), &["Result: 3"]);
}

/// W_C_corpus_2: a macro boundary violation produced through a quasiquoted template was
/// reported twice (`F0104` from the pending diagnostic and again as a declaration parsing
/// error) and named the built-in `quasiquote` instead of the user macro.
#[test]
fn macro_boundary_violation_is_reported_once_under_the_macro_name() {
    let source = r#"
(defmacro postulate (name ty) `(axiom ,name ,ty))
(postulate zero_is_one (Eq Nat zero (succ zero)))
"#;
    let run = run_dynamic("boundary_once", source);
    let text = run.combined();
    assert!(!run.success, "expected rejection:\n{}", text);
    let headlines: Vec<&str> = text
        .lines()
        .filter(|line| line.trim_start().starts_with("Error: [F0104]"))
        .collect();
    assert_eq!(headlines.len(), 1, "expected one F0104 error:\n{}", text);
    assert!(
        headlines[0].contains("Macro expansion for 'postulate'"),
        "expected the user macro's name:\n{}",
        text
    );
}

/// W_C_corpus_1 / W_C_corpus_6: `F0209` (implicit non-Copy binder consumed) named the binder
/// by its de Bruijn index and had no source span; `F0214` (unification failure) had no source
/// span either, so neither showed the offending code nor a macro call-site label.
#[test]
fn implicit_binder_and_unification_errors_have_spans() {
    let implicit = r#"
(inductive (affine) Tok (sort 1) (ctor mk_tok (pi id Nat Tok)))
(def burn (pi t Tok Nat) (lam t Tok zero))
(def bad (pi {t Tok} Nat) (lam {t} Tok (burn t)))
"#;
    let run = run_dynamic("f0209_span", implicit);
    assert_rejected_with(
        &run,
        &[
            "[F0209]",
            "consuming position: variable 't'",
            "(lam {t} Tok (burn t))",
        ],
    );

    let unification = r#"
(inductive St (sort 1) (ctor opened St) (ctor closed St))
(inductive (affine) Door (pi s St (sort 1)) (ctor mk_open (Door opened)) (ctor mk_closed (Door closed)))
(def close (pi d (Door opened) (Door closed)) (lam d (Door opened) mk_closed))
(defmacro close-twice (d) (close (close d)))
(def bad (Door closed) (close-twice mk_open))
"#;
    let run = run_dynamic("f0214_span", unification);
    assert_rejected_with(
        &run,
        &[
            "[F0214]",
            "Unification failed: St.closed vs St.opened",
            "in code produced by macro 'close-twice'",
        ],
    );
}

/// Found while removing case study A's workarounds: an explicit `(motive M)` whose body has
/// inferred implicit arguments (`(idn k)`) was passed to the kernel with unsubstituted
/// metavariables (K0047 "Unresolved metavariable").
#[test]
fn explicit_motive_with_inferred_implicit_arguments() {
    let source = r#"
(def idn (pi {A (sort 1)} (pi x A A)) (lam {A} (sort 1) (lam x A x)))
(def idn_nat (pi n Nat (Eq Nat (idn {Nat} n) n))
  (lam n Nat (match n (motive (lam k Nat (Eq Nat (idn k) k)))
    (case (zero) (refl Nat zero))
    (case (succ k ih) (refl Nat (succ k))))))
(def main Nat (idn 2))
"#;
    assert_output_lines(&run_typed("motive_implicit", source), &["Result: 2"]);
}

/// Found while removing case study A's workarounds: `zero =?= succ ?n` (different
/// constructors) was postponed and reported as an unsolved constraint without a span (F0217);
/// it is now a unification failure at the offending argument (F0214).
#[test]
fn constructor_clash_under_a_metavariable_fails_at_the_argument() {
    let source = r#"
(inductive Unit (sort 1) (ctor unit Unit))
(inductive Vec (pi A (sort 1) (pi n Nat (sort 1)))
  (ctor vnil (pi {A (sort 1)} (Vec A zero)))
  (ctor vcons (pi {A (sort 1)} (pi {n Nat} (pi h A (pi t (Vec A n) (Vec A (succ n))))))))
(def vhead (pi {A (sort 1)} (pi {n Nat} (pi v (Vec A (succ n)) A)))
  (lam {A} (sort 1) (lam {n} Nat (lam v (Vec A (succ n))
    (match v (motive (lam k Nat (lam w (Vec A k)
                       (match k (sort 1) (case (zero) Unit) (case (succ k1 ih) A)))))
      (case (vnil) unit)
      (case (vcons h t ih) h))))))
(def head_of_empty Nat (vhead (vnil {Nat})))
"#;
    assert_rejected_with(
        &run_dynamic("ctor_clash", source),
        &[
            "[F0214]",
            "Unification failed: Nat.zero vs (Nat.succ",
            "(vhead (vnil {Nat}))",
        ],
    );
}
