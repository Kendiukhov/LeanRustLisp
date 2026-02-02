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
        SurfaceTermKind::Lam(_, _, ty, body) | SurfaceTermKind::Pi(_, _, ty, body) => {
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
    let mut last_term = None;
    for syntax in syntax_list {
        match expander.expand(syntax).expect("Failed to expand") {
            Some(term) => last_term = Some(term),
            None => {}
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
