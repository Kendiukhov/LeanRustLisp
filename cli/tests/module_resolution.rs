use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::ast::Term;
use kernel::checker::Env;

fn process_source(
    env: &mut Env,
    expander: &mut Expander,
    source: &str,
    filename: &str,
) -> DiagnosticCollector {
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();
    let result = process_code(source, filename, env, expander, &options, &mut diagnostics);
    assert!(
        result.is_ok(),
        "process_code returned DriverError for {}: {:?}",
        filename,
        result.err()
    );
    diagnostics
}

fn assert_no_errors(diagnostics: &DiagnosticCollector, context: &str) {
    let errors: Vec<_> = diagnostics
        .diagnostics
        .iter()
        .filter(|diag| diag.level == Level::Error)
        .map(|diag| diag.message_with_code())
        .collect();
    assert!(
        errors.is_empty(),
        "unexpected errors in {}: {:?}",
        context,
        errors
    );
}

#[test]
fn aliased_imports_resolve_deterministically() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    let alpha_diags = process_source(
        &mut env,
        &mut expander,
        "(module Alpha)\n(def id (sort 1) (sort 0))",
        "alpha_module",
    );
    assert_no_errors(&alpha_diags, "alpha module");

    let beta_diags = process_source(
        &mut env,
        &mut expander,
        "(module Beta)\n(def id (sort 1) (sort 0))",
        "beta_module",
    );
    assert_no_errors(&beta_diags, "beta module");

    let main_diags = process_source(
        &mut env,
        &mut expander,
        "(module Main)\n(import Alpha as A)\n(import Beta as B)\n(def use_a (sort 1) A.id)\n(def use_b (sort 1) B.id)",
        "main_module",
    );
    assert_no_errors(&main_diags, "main module");

    let use_a = env
        .get_definition("Main.use_a")
        .and_then(|def| def.value.as_ref())
        .expect("missing Main.use_a value");
    assert!(
        matches!(&**use_a, Term::Const(name, _) if name == "Alpha.id"),
        "expected Main.use_a to resolve to Alpha.id, got {:?}",
        use_a
    );

    let use_b = env
        .get_definition("Main.use_b")
        .and_then(|def| def.value.as_ref())
        .expect("missing Main.use_b value");
    assert!(
        matches!(&**use_b, Term::Const(name, _) if name == "Beta.id"),
        "expected Main.use_b to resolve to Beta.id, got {:?}",
        use_b
    );
}

#[test]
fn open_requires_unique_target() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    assert_no_errors(
        &process_source(
            &mut env,
            &mut expander,
            "(module std.list)\n(def id (sort 1) (sort 0))",
            "std_list_module",
        ),
        "std.list module",
    );
    assert_no_errors(
        &process_source(
            &mut env,
            &mut expander,
            "(module app.list)\n(def id (sort 1) (sort 0))",
            "app_list_module",
        ),
        "app.list module",
    );

    let diagnostics = process_source(
        &mut env,
        &mut expander,
        "(module Main)\n(import std.list)\n(import app.list)\n(open list)\n(def bad (sort 1) id)",
        "main_open_ambiguous",
    );

    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|diag| diag.level == Level::Error
                && diag.message.contains("open target 'list' is ambiguous")),
        "expected ambiguous open diagnostic, got {:?}",
        diagnostics
            .diagnostics
            .iter()
            .map(|diag| diag.message_with_code())
            .collect::<Vec<_>>()
    );
}

#[test]
fn qualified_alias_with_multiple_modules_is_error() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    assert_no_errors(
        &process_source(
            &mut env,
            &mut expander,
            "(module std.list)\n(def id (sort 1) (sort 0))",
            "std_list_module",
        ),
        "std.list module",
    );
    assert_no_errors(
        &process_source(
            &mut env,
            &mut expander,
            "(module app.list)\n(def id (sort 1) (sort 0))",
            "app_list_module",
        ),
        "app.list module",
    );

    let diagnostics = process_source(
        &mut env,
        &mut expander,
        "(module Main)\n(import std.list as L)\n(import app.list as L)\n(def bad (sort 1) L.id)",
        "main_qualified_alias_ambiguous",
    );

    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|diag| diag.level == Level::Error && diag.code == Some("F0222")),
        "expected ambiguous-name diagnostic F0222, got {:?}",
        diagnostics
            .diagnostics
            .iter()
            .map(|diag| diag.message_with_code())
            .collect::<Vec<_>>()
    );
}

#[test]
fn ambiguous_unqualified_name_after_open_is_error() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    assert_no_errors(
        &process_source(
            &mut env,
            &mut expander,
            "(module Alpha)\n(def id (sort 1) (sort 0))",
            "alpha_module",
        ),
        "alpha module",
    );
    assert_no_errors(
        &process_source(
            &mut env,
            &mut expander,
            "(module Beta)\n(def id (sort 1) (sort 0))",
            "beta_module",
        ),
        "beta module",
    );

    let diagnostics = process_source(
        &mut env,
        &mut expander,
        "(module Main)\n(import Alpha as A)\n(import Beta as B)\n(open A)\n(open B)\n(def bad (sort 1) id)",
        "main_ambiguous_name",
    );

    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|diag| diag.level == Level::Error && diag.code == Some("F0222")),
        "expected ambiguous-name diagnostic F0222, got {:?}",
        diagnostics
            .diagnostics
            .iter()
            .map(|diag| diag.message_with_code())
            .collect::<Vec<_>>()
    );
}

#[test]
fn qualified_names_do_not_resolve_to_local_binders() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    assert_no_errors(
        &process_source(
            &mut env,
            &mut expander,
            "(module Alpha)\n(def id (sort 1) (sort 0))",
            "alpha_module",
        ),
        "alpha module",
    );

    let diagnostics = process_source(
        &mut env,
        &mut expander,
        "(module Main)\n(import Alpha as A)\n(def pick (pi A (sort 0) (sort 1)) (lam A (sort 0) A.id))",
        "main_qualified_vs_local",
    );
    assert_no_errors(&diagnostics, "qualified vs local");

    let pick = env
        .get_definition("Main.pick")
        .and_then(|def| def.value.as_ref())
        .expect("missing Main.pick value");
    let body = match &**pick {
        Term::Lam(_, body, _, _) => body,
        other => panic!("expected lambda value for Main.pick, got {:?}", other),
    };
    assert!(
        matches!(&**body, Term::Const(name, _) if name == "Alpha.id"),
        "expected lambda body to resolve to Alpha.id, got {:?}",
        body
    );
}
