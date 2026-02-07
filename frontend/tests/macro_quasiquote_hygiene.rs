use frontend::desugar::Desugarer;
use frontend::macro_expander::Expander;
use frontend::parser::Parser;
use frontend::surface::{SurfaceTerm, SurfaceTermKind};

fn collect_vars(term: &SurfaceTerm, vars: &mut Vec<String>) {
    match &term.kind {
        SurfaceTermKind::Var(name) => vars.push(name.clone()),
        SurfaceTermKind::Sort(_)
        | SurfaceTermKind::Ind(_)
        | SurfaceTermKind::Ctor(_, _)
        | SurfaceTermKind::Rec(_)
        | SurfaceTermKind::Hole => {}
        SurfaceTermKind::App(fun, arg, _) => {
            collect_vars(fun, vars);
            collect_vars(arg, vars);
        }
        SurfaceTermKind::Index(base, index) => {
            collect_vars(base, vars);
            collect_vars(index, vars);
        }
        SurfaceTermKind::Lam(_, _, _, ty, body) | SurfaceTermKind::Pi(_, _, _, ty, body) => {
            collect_vars(ty, vars);
            collect_vars(body, vars);
        }
        SurfaceTermKind::Let(_, ty, val, body) => {
            collect_vars(ty, vars);
            collect_vars(val, vars);
            collect_vars(body, vars);
        }
        SurfaceTermKind::Fix(_, ty, body) => {
            collect_vars(ty, vars);
            collect_vars(body, vars);
        }
        SurfaceTermKind::Match(scrutinee, ret_ty, cases) => {
            collect_vars(scrutinee, vars);
            collect_vars(ret_ty, vars);
            for (_, _, body) in cases {
                collect_vars(body, vars);
            }
        }
        SurfaceTermKind::Eval(code, cap) => {
            collect_vars(code, vars);
            collect_vars(cap, vars);
        }
    }
}

#[test]
fn test_quasiquote_hygiene_capture() {
    let input = "
    (defmacro mk (x) `(cons ,x nil))
    (lam cons Nat (mk cons))
    ";
    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");

    let mut expander = Expander::new();
    let mut desugarer = Desugarer::new();
    let mut last_term = None;
    for syntax in syntax_list {
        if let Some(expanded) = expander.expand(syntax).expect("Failed to expand") {
            let term = desugarer.desugar(expanded).expect("Failed to desugar");
            last_term = Some(term);
        }
    }

    let term = last_term.expect("Expected expanded term");
    let mut vars = Vec::new();
    collect_vars(&term, &mut vars);

    assert!(
        vars.iter().any(|v| v == "cons"),
        "Expected macro-introduced cons to remain global, vars: {:?}",
        vars
    );
    assert!(
        vars.iter().any(|v| v.starts_with("cons_g")),
        "Expected use-site cons to be renamed, vars: {:?}",
        vars
    );
}

#[test]
fn test_macro_hygiene_no_capture_call_site() {
    let input = "
    (defmacro m () x)
    (lam x Nat (m))
    ";
    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");

    let mut expander = Expander::new();
    let mut desugarer = Desugarer::new();
    let mut last_term = None;
    for syntax in syntax_list {
        if let Some(expanded) = expander.expand(syntax).expect("Failed to expand") {
            let term = desugarer.desugar(expanded).expect("Failed to desugar");
            last_term = Some(term);
        }
    }

    let term = last_term.expect("Expected expanded term");
    match term.kind {
        SurfaceTermKind::Lam(binder_name, _, _, _, body) => match body.kind {
            SurfaceTermKind::Var(var_name) => {
                assert!(binder_name.starts_with("x_g"));
                assert_eq!(var_name, "x");
                assert_ne!(var_name, binder_name);
            }
            other => panic!("Expected Var body, got {:?}", other),
        },
        other => panic!("Expected Lam term, got {:?}", other),
    }
}
