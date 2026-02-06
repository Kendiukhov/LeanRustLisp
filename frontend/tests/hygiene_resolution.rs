use frontend::desugar::Desugarer;
use frontend::surface::{ScopeId, Span, SurfaceTermKind, Syntax, SyntaxKind};

fn mk_span() -> Span {
    Span {
        start: 0,
        end: 0,
        line: 1,
        col: 1,
    }
}

fn sym(name: &str, scopes: Vec<ScopeId>) -> Syntax {
    Syntax {
        kind: SyntaxKind::Symbol(name.to_string()),
        span: mk_span(),
        scopes,
    }
}

#[test]
fn test_hygiene_capture_with_superset_scopes() {
    let lam = Syntax {
        kind: SyntaxKind::List(vec![
            sym("lam", vec![]),
            sym("x", vec![ScopeId(0)]),
            sym("Nat", vec![]),
            sym("x", vec![ScopeId(0), ScopeId(1)]),
        ]),
        span: mk_span(),
        scopes: vec![],
    };

    let mut desugarer = Desugarer::new();
    let term = desugarer.desugar(lam).expect("Failed to desugar");

    match term.kind {
        SurfaceTermKind::Lam(binder_name, _, _, _, body) => match body.kind {
            SurfaceTermKind::Var(var_name) => {
                assert!(binder_name.starts_with("x_g"));
                assert_eq!(var_name, binder_name);
            }
            other => panic!("Expected Var body, got {:?}", other),
        },
        other => panic!("Expected Lam term, got {:?}", other),
    }
}

#[test]
fn test_hygiene_scope_set_ordering() {
    let lam = Syntax {
        kind: SyntaxKind::List(vec![
            sym("lam", vec![]),
            sym("x", vec![ScopeId(1), ScopeId(0)]),
            sym("Nat", vec![]),
            sym("x", vec![ScopeId(0), ScopeId(1)]),
        ]),
        span: mk_span(),
        scopes: vec![],
    };

    let mut desugarer = Desugarer::new();
    let term = desugarer.desugar(lam).expect("Failed to desugar");

    match term.kind {
        SurfaceTermKind::Lam(binder_name, _, _, _, body) => match body.kind {
            SurfaceTermKind::Var(var_name) => {
                assert!(binder_name.starts_with("x_g"));
                assert_eq!(var_name, binder_name);
            }
            other => panic!("Expected Var body, got {:?}", other),
        },
        other => panic!("Expected Lam term, got {:?}", other),
    }
}
