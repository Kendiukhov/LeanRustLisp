use frontend::macro_expander::Expander;
use frontend::parser::Parser;
use frontend::surface::{Span, SurfaceTerm, SurfaceTermKind, Syntax, SyntaxKind};

fn parse_single(input: &str) -> Syntax {
    let mut parser = Parser::new(input);
    let mut nodes = parser.parse().expect("Failed to parse");
    assert_eq!(nodes.len(), 1, "Expected a single top-level form");
    nodes.remove(0)
}

fn expand_single(input: &str) -> SurfaceTerm {
    let mut parser = Parser::new(input);
    let nodes = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();

    let mut terms = Vec::new();
    for syntax in nodes {
        if let Some(term) = expander.expand(syntax).expect("Failed to expand") {
            terms.push(term);
        }
    }

    assert_eq!(terms.len(), 1, "Expected a single expanded term");
    terms.remove(0)
}

fn extract_quasiquote_body_span(syntax: &Syntax) -> Span {
    match &syntax.kind {
        SyntaxKind::List(list) if list.len() == 2 => {
            match &list[0].kind {
                SyntaxKind::Symbol(s) if s == "quasiquote" => list[1].span,
                _ => panic!("Expected (quasiquote <body>)"),
            }
        }
        _ => panic!("Expected a quasiquote form"),
    }
}

fn find_syntax_symbol_span(syntax: &Syntax, name: &str) -> Option<Span> {
    match &syntax.kind {
        SyntaxKind::Symbol(s) if s == name => Some(syntax.span),
        SyntaxKind::List(list) | SyntaxKind::BracedList(list) => list
            .iter()
            .find_map(|item| find_syntax_symbol_span(item, name)),
        _ => None,
    }
}

fn collect_var_spans(term: &SurfaceTerm, name: &str, out: &mut Vec<Span>) {
    match &term.kind {
        SurfaceTermKind::Var(var) if var == name => out.push(term.span),
        SurfaceTermKind::App(fun, arg, _) => {
            collect_var_spans(fun, name, out);
            collect_var_spans(arg, name, out);
        }
        SurfaceTermKind::Lam(_, _, ty, body)
        | SurfaceTermKind::Pi(_, _, ty, body) => {
            collect_var_spans(ty, name, out);
            collect_var_spans(body, name, out);
        }
        SurfaceTermKind::Let(_, ty, val, body) => {
            collect_var_spans(ty, name, out);
            collect_var_spans(val, name, out);
            collect_var_spans(body, name, out);
        }
        SurfaceTermKind::Fix(_, ty, body) => {
            collect_var_spans(ty, name, out);
            collect_var_spans(body, name, out);
        }
        SurfaceTermKind::Match(scrutinee, ret_ty, cases) => {
            collect_var_spans(scrutinee, name, out);
            collect_var_spans(ret_ty, name, out);
            for (_, _, case_body) in cases {
                collect_var_spans(case_body, name, out);
            }
        }
        _ => {}
    }
}

#[test]
fn test_quasiquote_generated_cons_spans_from_list() {
    let input = "(quasiquote (1 2 3))";
    let syntax = parse_single(input);
    let list_span = extract_quasiquote_body_span(&syntax);
    let term = expand_single(input);

    let mut cons_spans = Vec::new();
    collect_var_spans(&term, "cons", &mut cons_spans);
    assert!(!cons_spans.is_empty(), "Expected cons nodes in expansion");
    for span in cons_spans {
        assert_eq!(span, list_span, "cons span should match quasiquote list span");
    }

    let mut nil_spans = Vec::new();
    collect_var_spans(&term, "nil", &mut nil_spans);
    assert_eq!(nil_spans.len(), 1, "Expected a single nil node");
    assert_eq!(nil_spans[0], list_span, "nil span should match quasiquote list span");
}

#[test]
fn test_unquote_preserves_span() {
    let input = "(quasiquote (1 (unquote qq_x) 3))";
    let syntax = parse_single(input);
    let expected = find_syntax_symbol_span(&syntax, "qq_x")
        .expect("Expected to find qq_x in syntax tree");
    let list_span = extract_quasiquote_body_span(&syntax);
    let term = expand_single(input);

    let mut spans = Vec::new();
    collect_var_spans(&term, "qq_x", &mut spans);
    assert_eq!(spans.len(), 1, "Expected one qq_x occurrence");
    assert_eq!(spans[0], expected, "Unquoted symbol should preserve span");

    let mut cons_spans = Vec::new();
    collect_var_spans(&term, "cons", &mut cons_spans);
    assert!(!cons_spans.is_empty(), "Expected cons nodes in expansion");
    for span in cons_spans {
        assert_eq!(span, list_span, "cons span should match quasiquote list span");
    }
}

#[test]
fn test_unquote_splicing_preserves_span() {
    let input = "(quasiquote (0 (unquote-splicing qq_list) 3))";
    let syntax = parse_single(input);
    let expected = find_syntax_symbol_span(&syntax, "qq_list")
        .expect("Expected to find qq_list in syntax tree");
    let list_span = extract_quasiquote_body_span(&syntax);
    let term = expand_single(input);

    let mut spans = Vec::new();
    collect_var_spans(&term, "qq_list", &mut spans);
    assert_eq!(spans.len(), 1, "Expected one qq_list occurrence");
    assert_eq!(spans[0], expected, "Unquote-splicing should preserve span");

    let mut append_spans = Vec::new();
    collect_var_spans(&term, "append", &mut append_spans);
    assert!(!append_spans.is_empty(), "Expected append nodes in expansion");
    for span in append_spans {
        assert_eq!(span, list_span, "append span should match quasiquote list span");
    }
}
