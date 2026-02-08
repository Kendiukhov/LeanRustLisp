use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use insta::assert_snapshot;
use kernel::checker::Env;

fn run_pipeline_with_options(
    source: &str,
    allow_reserved: bool,
    require_axiom_tags: bool,
    allow_axioms: bool,
) -> (String, bool, bool) {
    run_pipeline_with_options_full(
        source,
        allow_reserved,
        require_axiom_tags,
        allow_axioms,
        false,
    )
}

fn run_pipeline_with_options_full(
    source: &str,
    allow_reserved: bool,
    require_axiom_tags: bool,
    allow_axioms: bool,
    panic_free: bool,
) -> (String, bool, bool) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions {
        collect_artifacts: false,
        require_axiom_tags,
        allow_axioms,
        panic_free,
        ..Default::default()
    };

    let allow_reserved_prev = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(allow_reserved);
    let result = process_code(
        source,
        "pipeline_negative",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );
    env.set_allow_reserved_primitives(allow_reserved_prev);

    let mut out = String::new();
    let is_err = result.is_err();
    let has_errors = diagnostics.has_errors();

    out.push_str(&format!("Status: {}\n", if is_err { "Err" } else { "Ok" }));
    if let Err(err) = &result {
        out.push_str(&format!("DriverError: {:?}\n", err));
    }

    if diagnostics.diagnostics.is_empty() {
        out.push_str("Diagnostics: none\n");
    } else {
        out.push_str("Diagnostics:\n");
        for diag in &diagnostics.diagnostics {
            out.push_str(&format!("- {}: {}\n", diag.level, diag.message_with_code()));
        }
    }

    (out, has_errors, is_err)
}

fn run_pipeline(source: &str) -> (String, bool, bool) {
    run_pipeline_with_options(source, true, false, false)
}

fn run_pipeline_without_reserved(source: &str) -> (String, bool, bool) {
    run_pipeline_with_options(source, false, false, false)
}

fn run_pipeline_strict_axiom_tags(source: &str) -> (String, bool, bool) {
    run_pipeline_with_options(source, true, true, false)
}

fn run_pipeline_with_reserved(source: &str) -> (String, bool, bool) {
    run_pipeline_with_options(source, true, false, false)
}

fn run_pipeline_panic_free_allow_axioms(source: &str) -> (String, bool, bool) {
    run_pipeline_with_options_full(source, true, false, true, true)
}

#[test]
fn pipeline_negative_type_mismatch() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def bad Nat (lam x Nat x))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for type mismatch");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_parse_error() {
    let source = "(def oops"; // missing closing paren

    let (output, has_errors, is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for parse error");
    assert!(is_err, "Parse errors should return DriverError");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_kernel_recheck_bad_fix() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def bad_fix Nat
          (fix f Nat zero))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_without_reserved(source);
    assert!(
        has_errors,
        "Expected kernel re-check diagnostics for bad fixpoint"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_kernel_recheck_expr_fix_in_type() {
    let source = r#"
        (fix f (sort 0) f)
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected kernel re-check diagnostics for top-level expression"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_fix_in_total_def() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def loop (pi n Nat Nat)
          (fix loop (pi n Nat Nat)
            (lam n Nat (loop n))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for fix in total def");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_match_non_inductive_scrutinee() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def bad (pi n Nat Nat)
          (lam n Nat
            (match Nat Nat
              (case (zero) zero)
              (case (succ k ih) zero))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for non-inductive scrutinee"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_match_motive_not_sort() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def bad (pi n Nat Nat)
          (lam n Nat
            (match n zero
              (case (zero) zero)
              (case (succ k ih) zero))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for non-Sort motive");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_strict_axiom_tags_rejects_untagged() {
    let source = r#"
        (axiom my_axiom (sort 0))
    "#;

    let (output, has_errors, is_err) = run_pipeline_strict_axiom_tags(source);
    assert!(has_errors, "Expected diagnostics for untagged axiom");
    assert!(!is_err, "Expected diagnostics, not a parse error");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_strict_axiom_tags_accepts_tagged() {
    let source = r#"
        (axiom classical my_axiom (sort 0))
    "#;

    let (output, has_errors, is_err) = run_pipeline_strict_axiom_tags(source);
    assert!(!has_errors, "Expected no diagnostics for tagged axiom");
    assert!(!is_err, "Tagged axiom should not cause a parse error");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_macro_boundary_deny_blocks_smuggled_axiom() {
    let source = r#"
        (defmacro smuggle_axiom () (quasiquote (axiom classical bad (sort 0))))
        (smuggle_axiom)
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let result = process_code(
        source,
        "pipeline_negative",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(
        result.is_err(),
        "Expected macro boundary denial to abort processing"
    );
    assert!(
        diagnostics.has_errors(),
        "Expected diagnostics for macro boundary denial"
    );
    assert!(
        env.get_definition("bad").is_none(),
        "Smuggled axiom should not be present in env"
    );
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.message.contains("macro boundary")),
        "Expected macro boundary diagnostic"
    );
}

#[test]
fn pipeline_negative_macro_boundary_deny_blocks_direct_quasiquote_axiom() {
    let source = r#"
        (quasiquote (axiom classical bad (sort 0)))
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let result = process_code(
        source,
        "pipeline_negative",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(
        result.is_err(),
        "Expected direct quasiquote smuggling to abort processing"
    );
    assert!(
        diagnostics.has_errors(),
        "Expected diagnostics for direct quasiquote smuggling"
    );
    assert!(
        env.get_definition("bad").is_none(),
        "Direct quasiquote smuggled axiom should not be present in env"
    );
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.message.contains("axiom classical")),
        "Expected direct quasiquote diagnostic to mention axiom classical"
    );
}

#[test]
fn pipeline_negative_macro_boundary_deny_blocks_direct_quasiquote_import_classical() {
    let source = r#"
        (quasiquote (import classical))
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let result = process_code(
        source,
        "pipeline_negative",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(
        result.is_err(),
        "Expected direct quasiquote import smuggling to abort processing"
    );
    assert!(
        diagnostics.has_errors(),
        "Expected diagnostics for direct quasiquote import smuggling"
    );
    assert!(
        env.get_definition("classical_choice").is_none(),
        "Direct quasiquote import classical should not mutate env"
    );
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.message.contains("import classical")),
        "Expected direct quasiquote diagnostic to mention import classical"
    );
}

#[test]
fn pipeline_negative_match_missing_case() {
    let source = r#"
        (inductive copy Bool Type
          (true Bool)
          (false Bool))

        (def bad (pi b Bool Nat)
          (lam b Bool
            (match b Nat
              (case (true) zero))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for non-exhaustive match");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_match_duplicate_case() {
    let source = r#"
        (inductive copy Bool Type
          (true Bool)
          (false Bool))

        (def bad (pi b Bool Nat)
          (lam b Bool
            (match b Nat
              (case (true) zero)
              (case (true) (succ zero))
              (case (false) zero))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for duplicate match case");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_reserved_primitive_shadowing() {
    let source = r#"
        (def borrow_mut (sort 1) (sort 0))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for reserved primitive shadowing"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_reserved_primitive_inductive() {
    let source = r#"
        (inductive borrow_shared Type
          (mk borrow_shared))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for reserved primitive inductive name"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_eval_in_type() {
    let source = r#"
        (axiom Dyn (sort 0))
        (axiom EvalCap (sort 0))
        (axiom unsafe eval (pi code Dyn (pi cap EvalCap Dyn)))
        (axiom dyn_code Dyn)
        (axiom dyn_cap EvalCap)

        (noncomputable bad (eval dyn_code dyn_cap) dyn_code)
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(has_errors, "Expected diagnostics for eval in type position");
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_unsafe_borrow_in_total() {
    let source = r#"
        (axiom Nat (sort 1))
        (axiom unsafe unsafe_borrow (pi {A (sort 1)} (pi x A A)))

        (noncomputable bad (pi x Nat Nat)
          (lam x Nat
            (unsafe_borrow x)))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for unsafe borrow in total def"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_unsafe_index_in_total() {
    let source = r#"
        (axiom Nat (sort 1))
        (axiom unsafe unsafe_index (pi {A (sort 1)} (pi v A (pi i Nat A))))

        (noncomputable bad (pi v Nat (pi i Nat Nat))
          (lam v Nat
            (lam i Nat
              (unsafe_index v i))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for unsafe indexing in total def"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_unsafe_axiom_in_type() {
    let source = r#"
        (axiom unsafe BadType (sort 1))

        (noncomputable bad (pi x BadType BadType)
          (lam x BadType x))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for unsafe axiom in type position"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_copy_instance_requires_unsafe() {
    let source = r#"
        (inductive Box (pi A Type Type)
          (mk_box (pi {A Type} (pi x A (Box A)))))

        (instance copy (pi A Type (Box A)))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for non-unsafe Copy instance"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_unsafe_copy_instance_interior_mutable() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive (may_panic_on_borrow_violation) RefCell (pi T Type Type)
          (mk_refcell (pi {T Type} (pi x T (RefCell T)))))

        (unsafe instance copy (pi T Type (RefCell T)))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for unsafe Copy instance on interior-mutable type"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_refcell_requires_unsafe() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive Foo Type
          (ctor mk_foo Foo))

        (inductive (interior_mutable may_panic_on_borrow_violation) RefCell (pi T Type Type)
          (ctor mk_refcell (pi {T Type} (pi x T (RefCell T)))))

        (def uses_refcell (pi x (RefCell Foo) Foo)
          (lam x (RefCell Foo) mk_foo))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for RefCell in safe definition"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_refcell_requires_allow_axioms() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive Foo Type
          (ctor mk_foo Foo))

        (inductive (interior_mutable may_panic_on_borrow_violation) RefCell (pi T Type Type)
          (ctor mk_refcell (pi {T Type} (pi x T (RefCell T)))))

        (noncomputable uses_refcell (pi x (RefCell Foo) Foo)
          (lam x (RefCell Foo) mk_foo))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for RefCell without --allow-axioms"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_refcell_gate_rolls_back_failed_definition() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive Foo Type
          (ctor mk_foo Foo))

        (inductive (interior_mutable may_panic_on_borrow_violation) RefCell (pi T Type Type)
          (ctor mk_refcell (pi {T Type} (pi x T (RefCell T)))))

        (noncomputable uses_refcell (pi x (RefCell Foo) Foo)
          (lam x (RefCell Foo) mk_foo))

        (noncomputable transitive (pi x (RefCell Foo) Foo)
          (lam x (RefCell Foo) (uses_refcell x)))
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let allow_reserved_prev = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let result = process_code(
        source,
        "pipeline_negative",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );
    env.set_allow_reserved_primitives(allow_reserved_prev);

    assert!(
        result.is_ok(),
        "Expected processing to continue with diagnostics"
    );
    assert!(
        diagnostics.has_errors(),
        "Expected interior mutability diagnostics"
    );
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.message_with_code().contains("[C0005]")),
        "Expected [C0005] interior mutability gate diagnostic"
    );
    assert!(
        env.get_definition("uses_refcell").is_none(),
        "Failed gated definition should be rolled back from env"
    );
    assert!(
        env.get_definition("transitive").is_none(),
        "Dependent definition should fail after rollback"
    );
}

#[test]
fn pipeline_negative_panic_free_rejects_runtime_checks() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive Foo Type
          (ctor mk_foo Foo))

        (inductive (interior_mutable may_panic_on_borrow_violation) RefCell (pi T Type Type)
          (ctor mk_refcell (pi {T Type} (pi x T (RefCell T)))))

        (noncomputable uses_refcell (pi x (RefCell Foo) (RefCell Foo))
          (lam x (RefCell Foo) x))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_panic_free_allow_axioms(source);
    assert!(
        has_errors,
        "Expected diagnostics when panic-free profile encounters runtime checks"
    );
    assert!(
        output.contains("[C0006] Panic-free profile violation in uses_refcell"),
        "Expected panic-free runtime-check diagnostic, got:\n{}",
        output
    );
}

#[test]
fn pipeline_negative_mutex_requires_unsafe() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive Foo Type
          (ctor mk_foo Foo))

        (inductive (interior_mutable concurrency_primitive) Mutex (pi T Type Type)
          (ctor mk_mutex (pi {T Type} (pi x T (Mutex T)))))

        (def uses_mutex (pi x (Mutex Foo) Foo)
          (lam x (Mutex Foo) mk_foo))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for Mutex in safe definition"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_atomic_requires_unsafe() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive Foo Type
          (ctor mk_foo Foo))

        (inductive (interior_mutable concurrency_primitive atomic_primitive) Atomic (pi T Type Type)
          (ctor mk_atomic (pi {T Type} (pi x T (Atomic T)))))

        (def uses_atomic (pi x (Atomic Foo) Foo)
          (lam x (Atomic Foo) mk_foo))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for Atomic in safe definition"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_function_kind_annotation_too_small() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat))

        (axiom Res (sort 1))

        (noncomputable bad_kind
          (pi r Res (pi #[fn] _ Nat Res))
          (lam r Res
            (lam #[fn] _ Nat r)))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for function kind annotation too small"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_implicit_arg_capture_requires_fnonce() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (inductive (may_panic_on_borrow_violation) LinBox (pi A Type Type)
          (mk_lin_box (pi {A Type} (pi x A (LinBox A)))))

        (axiom consume_imp (pi {b (LinBox Nat)} (LinBox Nat)))

        (noncomputable make
          (pi b (LinBox Nat) (pi #[fn] _ Nat (LinBox Nat)))
          (lam b (LinBox Nat)
            (lam #[fn] _ Nat (consume_imp {b}))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for implicit-arg capture requiring FnOnce"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_fnonce_called_twice() {
    let source = r#"
        (inductive copy Nat Type
          (zero Nat))

        (inductive Box (pi A Type Type)
          (mk_box (pi {A Type} (pi x A (Box A)))))

        (def make_once
          (pi b (Box Nat) (pi #[once] _ Nat (Box Nat)))
          (lam b (Box Nat)
            (lam _ Nat b)))

        (def dup_fnonce (pi b (Box Nat) (Box Nat))
          (lam b (Box Nat)
            (let f (pi #[once] _ Nat (Box Nat)) (make_once b)
              (let first (Box Nat) (f zero)
                (f zero)))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline(source);
    assert!(
        has_errors,
        "Expected diagnostics for FnOnce closure called twice"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_borrow_escape_through_call() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (zero Nat)
          (succ (pi n Nat Nat)))

        (axiom Shared (sort 1))
        (axiom Mut (sort 1))
        (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
        (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))
        (axiom borrow_mut (pi {A (sort 1)} (pi x A (Ref #[r] Mut A))))

        (noncomputable id_ref (pi r (Ref #[r] Shared Nat) (Ref #[r] Shared Nat))
          (lam r (Ref #[r] Shared Nat) r))

        (noncomputable bad_escape (pi x Nat (Ref #[r] Shared Nat))
          (lam x Nat
            (let r (Ref #[r] Shared Nat) (& x)
              (id_ref r))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for borrow escape through function call"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_borrow_error_rolls_back_failed_definition() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (zero Nat)
          (succ (pi n Nat Nat)))

        (axiom Shared (sort 1))
        (axiom Mut (sort 1))
        (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
        (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))
        (axiom borrow_mut (pi {A (sort 1)} (pi x A (Ref #[r] Mut A))))

        (noncomputable id_ref (pi r (Ref #[r] Shared Nat) (Ref #[r] Shared Nat))
          (lam r (Ref #[r] Shared Nat) r))

        (noncomputable bad_escape (pi x Nat (Ref #[r] Shared Nat))
          (lam x Nat
            (let r (Ref #[r] Shared Nat) (& x)
              (id_ref r))))

        (noncomputable transitive_escape (pi x Nat (Ref #[r] Shared Nat))
          (lam x Nat (bad_escape x)))
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let allow_reserved_prev = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let result = process_code(
        source,
        "pipeline_negative",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );
    env.set_allow_reserved_primitives(allow_reserved_prev);

    assert!(
        result.is_ok(),
        "Expected processing to continue with diagnostics"
    );
    assert!(diagnostics.has_errors(), "Expected borrow diagnostics");
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.message.contains("Borrow error in bad_escape")),
        "Expected borrow checker diagnostic for bad_escape"
    );
    assert!(
        env.get_definition("bad_escape").is_none(),
        "Borrow-check failure should roll back bad_escape"
    );
    assert!(
        env.get_definition("transitive_escape").is_none(),
        "Dependent definition should fail after rollback"
    );
}

#[test]
fn pipeline_negative_labeled_lifetime_tied_through_polymorphic_call() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (zero Nat)
          (succ (pi n Nat Nat)))

        (axiom Shared (sort 1))
        (axiom Mut (sort 1))
        (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
        (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))
        (axiom borrow_mut (pi {A (sort 1)} (pi x A (Ref #[r] Mut A))))

        (noncomputable use_shared (pi r (Ref #[r] Shared Nat) Nat)
          (lam r (Ref #[r] Shared Nat) zero))

        (noncomputable use_mut (pi r (Ref #[r] Mut Nat) Nat)
          (lam r (Ref #[r] Mut Nat) zero))

        (noncomputable choose_left
          (pi A Type
            (pi a (Ref #[r] Shared A)
              (pi b (Ref #[r] Shared A)
                (Ref #[r] Shared A))))
          (lam A Type
            (lam a (Ref #[r] Shared A)
              (lam b (Ref #[r] Shared A) a))))

        (noncomputable bad_overlap (pi x Nat (pi y Nat Nat))
          (lam x Nat
            (lam y Nat
              (let r1 (Ref #[r] Shared Nat) (& x)
                (let r2 (Ref #[r] Shared Nat) (& y)
                  (let r (Ref #[r] Shared Nat) (choose_left Nat r1 r2)
                    (let m (Ref #[r] Mut Nat) (&mut x)
                      (let ignored Nat (use_mut m)
                        (use_shared r)))))))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        !has_errors,
        "Expected no diagnostics: polymorphic Ref type parameters should specialize through labels"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_lifetime_label_mismatch_defeq() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (zero Nat)
          (succ (pi n Nat Nat)))

        (axiom Shared (sort 1))
        (axiom Mut (sort 1))
        (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))

        (noncomputable coerce
          (pi a (Ref #[a] Shared Nat)
            (Ref #[b] Shared Nat))
          (lam a (Ref #[a] Shared Nat) a))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for lifetime label mismatch in defeq"
    );
    assert_snapshot!(output);
}

#[test]
fn pipeline_negative_labeled_lifetime_through_closure() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (zero Nat)
          (succ (pi n Nat Nat)))

        (axiom Shared (sort 1))
        (axiom Mut (sort 1))
        (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
        (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))
        (axiom borrow_mut (pi {A (sort 1)} (pi x A (Ref #[r] Mut A))))

        (noncomputable use_shared (pi r (Ref #[r] Shared Nat) Nat)
          (lam r (Ref #[r] Shared Nat) zero))

        (noncomputable make_selector
          (pi a (Ref #[r] Shared Nat)
            (pi _ Nat (Ref #[r] Shared Nat)))
          (lam a (Ref #[r] Shared Nat)
            (lam _ Nat a)))

        (noncomputable bad_closure_overlap (pi x Nat (pi y Nat Nat))
          (lam x Nat
            (lam y Nat
              (let r1 (Ref #[r] Shared Nat) (& x)
                (let f (pi _ Nat (Ref #[r] Shared Nat)) (make_selector r1)
                  (let out (Ref #[r] Shared Nat) (f zero)
                    (let m (Ref #[r] Mut Nat) (&mut x)
                      (use_shared out)))))))))
    "#;

    let (output, has_errors, _is_err) = run_pipeline_with_reserved(source);
    assert!(
        has_errors,
        "Expected diagnostics for labeled lifetime through closure"
    );
    let _ = output;
}
