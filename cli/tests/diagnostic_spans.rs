use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::{Diagnostic, DiagnosticCollector, Level};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;

const BORROW_SURFACE_PRELUDE: &str = r#"
    (inductive copy Nat (sort 1)
      (zero Nat)
      (succ (pi n Nat Nat)))

    (axiom Shared (sort 1))
    (axiom Mut (sort 1))
    (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
    (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))
    (axiom borrow_mut (pi {A (sort 1)} (pi x A (Ref #[r] Mut A))))
"#;

fn line_col_for(source: &str, needle: &str) -> (usize, usize) {
    let start = source
        .find(needle)
        .unwrap_or_else(|| panic!("missing needle in source: {}", needle));
    let prefix = &source[..start];
    let line = prefix.chars().filter(|ch| *ch == '\n').count() + 1;
    let col = prefix
        .rsplit('\n')
        .next()
        .map(|segment| segment.chars().count())
        .unwrap_or(0);
    (line, col)
}

fn first_error_with_code_prefix<'a>(
    diagnostics: &'a DiagnosticCollector,
    prefix: &str,
) -> Option<&'a Diagnostic> {
    diagnostics.diagnostics.iter().find(|diag| {
        diag.level == Level::Error && diag.code.is_some_and(|code| code.starts_with(prefix))
    })
}

fn diagnostic_summary(diagnostics: &DiagnosticCollector) -> String {
    diagnostics
        .diagnostics
        .iter()
        .map(|diag| {
            let code = diag.code.unwrap_or("NO_CODE");
            let span = diag
                .span
                .map(|s| format!("{}:{}", s.line, s.col))
                .unwrap_or_else(|| "none".to_string());
            format!("{} [{}] {}", code, span, diag.message)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn load_borrow_prelude(env: &mut Env, expander: &mut Expander, options: &PipelineOptions) {
    let mut diagnostics = DiagnosticCollector::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
    process_code(
        BORROW_SURFACE_PRELUDE,
        "prelude",
        env,
        expander,
        options,
        &mut diagnostics,
    )
    .expect("prelude processing failed");
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    env.set_allow_reserved_primitives(allow_reserved);
    assert!(
        !diagnostics.has_errors(),
        "prelude diagnostics contained errors"
    );
}

#[test]
fn macro_expansion_error_preserves_callsite_span() {
    let source = r#"(inductive copy Foo Type
  (mk_foo Foo))
(defmacro bad_foo () (quasiquote missing_symbol))
(def bad Foo (bad_foo))
"#;
    let expected = line_col_for(source, "(bad_foo)");

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    let result = process_code(
        source,
        "macro_span_test",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected source to parse and elaborate");
    let diag = first_error_with_code_prefix(&diagnostics, "F0200").unwrap_or_else(|| {
        panic!(
            "expected an unbound-variable diagnostic from macro expansion:\n{}",
            diagnostic_summary(&diagnostics)
        )
    });
    let span = diag.span.unwrap_or_else(|| {
        panic!(
            "expected macro-expanded diagnostic to have a source span:\n{}",
            diagnostic_summary(&diagnostics)
        )
    });
    assert_eq!((span.line, span.col), expected);
}

#[test]
fn ownership_error_reports_source_span() {
    let source = r#"
        (inductive copy Val Type
          (v0 Val))

        (inductive Box (pi A Type Type)
          (mk_box (pi {A Type} (pi x A (Box A)))))

        (def make_once
          (pi b (Box Val) (pi #[once] _ Val (Box Val)))
          (lam b (Box Val)
            (lam _ Val b)))

        (def dup_fnonce (pi b (Box Val) (Box Val))
          (lam b (Box Val)
            (let f (pi #[once] _ Val (Box Val)) (make_once b)
              (let first (Box Val) (f v0)
                (f v0)))))
"#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    let result = process_code(
        source,
        "ownership_span_test",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected source to parse");
    let diag = diagnostics
        .diagnostics
        .iter()
        .find(|diag| {
            if diag.level != Level::Error {
                return false;
            }
            if diag
                .code
                .is_some_and(|code| code == "K0021" || code == "K0034")
            {
                return true;
            }
            diag.message.contains("OwnershipError")
                || diag.message.contains("capture")
                || diag.message.contains("Capture")
        })
        .unwrap_or_else(|| {
            panic!(
                "expected ownership/capture diagnostic:\n{}",
                diagnostic_summary(&diagnostics)
            )
        });
    assert!(
        diag.span.is_some(),
        "ownership diagnostics should include source spans"
    );
}

#[test]
fn borrow_error_reports_source_span() {
    let source = r#"(noncomputable use_shared (pi r (Ref #[r] Shared Nat) Nat)
  (lam r (Ref #[r] Shared Nat) zero))

(noncomputable borrow_then_mutate (pi x Nat Nat)
  (lam x Nat
    (let r (Ref #[r] Shared Nat) (& x)
      (let m (Ref #[r] Mut Nat) (&mut x)
        (use_shared r)))))
"#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    load_borrow_prelude(&mut env, &mut expander, &options);

    let result = process_code(
        source,
        "borrow_span_test",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected source to parse");
    let diag = first_error_with_code_prefix(&diagnostics, "M2").unwrap_or_else(|| {
        panic!(
            "expected a borrow diagnostic:\n{}",
            diagnostic_summary(&diagnostics)
        )
    });
    assert!(
        diag.span.is_some(),
        "borrow diagnostics should include source spans"
    );
}

#[test]
fn ambiguous_constructor_reports_deterministic_candidates_with_span() {
    let source = r#"
        (inductive copy Foo Type
          (mk Foo))

        (inductive copy Bar Type
          (mk Bar))

        (def use_mk Foo mk)
    "#;

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    let result = process_code(
        source,
        "ambiguous_ctor_span_test",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    assert!(result.is_ok(), "expected source to parse");
    let diag = first_error_with_code_prefix(&diagnostics, "F0202").unwrap_or_else(|| {
        panic!(
            "expected ambiguous-constructor diagnostic:\n{}",
            diagnostic_summary(&diagnostics)
        )
    });

    assert!(
        diag.span.is_some(),
        "ambiguous constructor diagnostics should include source spans"
    );
    let bar_idx = diag
        .message
        .find("Bar.mk")
        .unwrap_or_else(|| panic!("expected Bar.mk in diagnostic message: {}", diag.message));
    let foo_idx = diag
        .message
        .find("Foo.mk")
        .unwrap_or_else(|| panic!("expected Foo.mk in diagnostic message: {}", diag.message));
    assert!(
        bar_idx < foo_idx,
        "constructor candidates should have deterministic ordering in diagnostics: {}",
        diag.message
    );
}
