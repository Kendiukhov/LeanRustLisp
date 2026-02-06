use frontend::desugar::Desugarer;
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
    let mut desugarer = Desugarer::new();

    let mut terms = Vec::new();
    for syntax in nodes {
        if let Some(expanded) = expander.expand(syntax).expect("Failed to expand") {
            let term = desugarer.desugar(expanded).expect("Failed to desugar");
            terms.push(term);
        }
    }

    assert_eq!(terms.len(), 1, "Expected a single expanded term");
    terms.remove(0)
}

fn extract_quasiquote_body_span(syntax: &Syntax) -> Span {
    match &syntax.kind {
        SyntaxKind::List(list) if list.len() == 2 => match &list[0].kind {
            SyntaxKind::Symbol(s) if s == "quasiquote" => list[1].span,
            _ => panic!("Expected (quasiquote <body>)"),
        },
        _ => panic!("Expected a quasiquote form"),
    }
}

fn find_syntax_symbol_span(syntax: &Syntax, name: &str) -> Option<Span> {
    match &syntax.kind {
        SyntaxKind::Symbol(s) if s == name => Some(syntax.span),
        SyntaxKind::List(list) | SyntaxKind::BracedList(list) => list
            .iter()
            .find_map(|item| find_syntax_symbol_span(item, name)),
        SyntaxKind::Index(base, index) => {
            find_syntax_symbol_span(base, name).or_else(|| find_syntax_symbol_span(index, name))
        }
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
        SurfaceTermKind::Index(base, index) => {
            collect_var_spans(base, name, out);
            collect_var_spans(index, name, out);
        }
        SurfaceTermKind::Lam(_, _, _, ty, body) | SurfaceTermKind::Pi(_, _, _, ty, body) => {
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
        SurfaceTermKind::Eval(code, cap) => {
            collect_var_spans(code, name, out);
            collect_var_spans(cap, name, out);
        }
        _ => {}
    }
}

fn collect_app_spans(term: &SurfaceTerm, expected_span: Span, out: &mut Vec<Span>) {
    let mut current = term;
    loop {
        match &current.kind {
            SurfaceTermKind::App(fun, _, _) if current.span == expected_span => {
                out.push(current.span);
                current = fun;
            }
            _ => break,
        }
    }
}

fn collect_lam_spans(term: &SurfaceTerm, out: &mut Vec<Span>) {
    match &term.kind {
        SurfaceTermKind::Lam(_, _, _, ty, body) => {
            out.push(term.span);
            collect_lam_spans(ty, out);
            collect_lam_spans(body, out);
        }
        SurfaceTermKind::App(fun, arg, _) => {
            collect_lam_spans(fun, out);
            collect_lam_spans(arg, out);
        }
        SurfaceTermKind::Index(base, index) => {
            collect_lam_spans(base, out);
            collect_lam_spans(index, out);
        }
        SurfaceTermKind::Pi(_, _, _, ty, body) => {
            collect_lam_spans(ty, out);
            collect_lam_spans(body, out);
        }
        SurfaceTermKind::Let(_, ty, val, body) => {
            collect_lam_spans(ty, out);
            collect_lam_spans(val, out);
            collect_lam_spans(body, out);
        }
        SurfaceTermKind::Fix(_, ty, body) => {
            collect_lam_spans(ty, out);
            collect_lam_spans(body, out);
        }
        SurfaceTermKind::Match(scrutinee, ret_ty, cases) => {
            collect_lam_spans(scrutinee, out);
            collect_lam_spans(ret_ty, out);
            for (_, _, case_body) in cases {
                collect_lam_spans(case_body, out);
            }
        }
        SurfaceTermKind::Eval(code, cap) => {
            collect_lam_spans(code, out);
            collect_lam_spans(cap, out);
        }
        _ => {}
    }
}

#[test]
fn test_quasiquote_generated_app_spans_from_list() {
    let input = "(quasiquote (1 2 3))";
    let syntax = parse_single(input);
    let list_span = extract_quasiquote_body_span(&syntax);
    let term = expand_single(input);

    let mut app_spans = Vec::new();
    collect_app_spans(&term, list_span, &mut app_spans);
    assert!(
        !app_spans.is_empty(),
        "Expected application nodes in expansion"
    );
    for span in app_spans {
        assert_eq!(
            span, list_span,
            "application span should match quasiquote list span"
        );
    }
}

#[test]
fn test_unquote_preserves_span() {
    let input = "(quasiquote (1 (unquote qq_x) 3))";
    let syntax = parse_single(input);
    let expected =
        find_syntax_symbol_span(&syntax, "qq_x").expect("Expected to find qq_x in syntax tree");
    let list_span = extract_quasiquote_body_span(&syntax);
    let term = expand_single(input);

    let mut spans = Vec::new();
    collect_var_spans(&term, "qq_x", &mut spans);
    assert_eq!(spans.len(), 1, "Expected one qq_x occurrence");
    assert_eq!(spans[0], expected, "Unquoted symbol should preserve span");

    let mut app_spans = Vec::new();
    collect_app_spans(&term, list_span, &mut app_spans);
    assert!(
        !app_spans.is_empty(),
        "Expected application nodes in expansion"
    );
    for span in app_spans {
        assert_eq!(
            span, list_span,
            "application span should match quasiquote list span"
        );
    }
}

#[test]
fn test_unquote_splicing_preserves_span() {
    let input = "(quasiquote (0 (unquote-splicing (quasiquote (qq_a qq_b))) 3))";
    let syntax = parse_single(input);
    let expected_a =
        find_syntax_symbol_span(&syntax, "qq_a").expect("Expected to find qq_a in syntax tree");
    let expected_b =
        find_syntax_symbol_span(&syntax, "qq_b").expect("Expected to find qq_b in syntax tree");
    let list_span = extract_quasiquote_body_span(&syntax);
    let term = expand_single(input);

    let mut spans_a = Vec::new();
    collect_var_spans(&term, "qq_a", &mut spans_a);
    assert_eq!(spans_a.len(), 1, "Expected one qq_a occurrence");
    assert_eq!(
        spans_a[0], expected_a,
        "Spliced qq_a span should be preserved"
    );

    let mut spans_b = Vec::new();
    collect_var_spans(&term, "qq_b", &mut spans_b);
    assert_eq!(spans_b.len(), 1, "Expected one qq_b occurrence");
    assert_eq!(
        spans_b[0], expected_b,
        "Spliced qq_b span should be preserved"
    );

    let mut app_spans = Vec::new();
    collect_app_spans(&term, list_span, &mut app_spans);
    assert!(
        !app_spans.is_empty(),
        "Expected application nodes in expansion"
    );
    for span in app_spans {
        assert_eq!(
            span, list_span,
            "application span should match quasiquote list span"
        );
    }
}

#[test]
fn test_macro_call_site_span_remap() {
    let macro_def = "(defmacro mk (x) (lam y Nat x))";
    let call = "(mk z)";

    let mut expander = Expander::new();
    let mut parser = Parser::new(macro_def);
    let macro_nodes = parser.parse().expect("Failed to parse macro definition");
    for node in macro_nodes {
        let _ = expander
            .expand_all_macros(node)
            .expect("Failed to define macro");
    }

    let mut parser = Parser::new(call);
    let mut call_nodes = parser.parse().expect("Failed to parse macro call");
    let call_syntax = call_nodes.remove(0);
    let call_span = call_syntax.span;
    let arg_span =
        find_syntax_symbol_span(&call_syntax, "z").expect("Expected to find z in call syntax");

    let expanded = expander
        .expand(call_syntax)
        .expect("Failed to expand macro")
        .expect("Expected expansion result");
    let mut desugarer = Desugarer::new();
    let term = desugarer.desugar(expanded).expect("Failed to desugar");

    let mut lam_spans = Vec::new();
    collect_lam_spans(&term, &mut lam_spans);
    assert_eq!(lam_spans.len(), 1, "Expected a single lam node");
    assert_eq!(
        lam_spans[0], call_span,
        "Macro-introduced lam span should match macro call site"
    );

    let mut z_spans = Vec::new();
    collect_var_spans(&term, "z", &mut z_spans);
    assert_eq!(z_spans.len(), 1, "Expected a single z occurrence");
    assert_eq!(
        z_spans[0], arg_span,
        "Macro argument span should be preserved"
    );
}

#[test]
fn test_macro_quasiquote_unquote_preserves_span() {
    let macro_def = "(defmacro wrap (x) (quasiquote (1 (unquote x) 3)))";
    let call = "(wrap qq_x)";

    let mut expander = Expander::new();
    let mut parser = Parser::new(macro_def);
    let macro_nodes = parser.parse().expect("Failed to parse macro definition");
    for node in macro_nodes {
        let _ = expander
            .expand_all_macros(node)
            .expect("Failed to define macro");
    }

    let mut parser = Parser::new(call);
    let mut call_nodes = parser.parse().expect("Failed to parse macro call");
    let call_syntax = call_nodes.remove(0);
    let call_span = call_syntax.span;
    let arg_span = find_syntax_symbol_span(&call_syntax, "qq_x")
        .expect("Expected to find qq_x in call syntax");

    let expanded = expander
        .expand(call_syntax)
        .expect("Failed to expand macro")
        .expect("Expected expansion result");
    let mut desugarer = Desugarer::new();
    let term = desugarer.desugar(expanded).expect("Failed to desugar");

    let mut qq_spans = Vec::new();
    collect_var_spans(&term, "qq_x", &mut qq_spans);
    assert_eq!(qq_spans.len(), 1, "Expected a single qq_x occurrence");
    assert_eq!(
        qq_spans[0], arg_span,
        "Unquoted macro argument span should be preserved"
    );

    let mut app_spans = Vec::new();
    collect_app_spans(&term, call_span, &mut app_spans);
    assert!(
        !app_spans.is_empty(),
        "Expected application nodes in expansion"
    );
    for span in app_spans {
        assert_eq!(
            span, call_span,
            "application span should match macro call site"
        );
    }
}

#[test]
fn test_macro_quasiquote_unquote_splicing_preserves_span() {
    let macro_def = "(defmacro wrap (xs) (quasiquote (0 (unquote-splicing xs) 3)))";
    let call = "(wrap (quasiquote (qq_a qq_b)))";

    let mut expander = Expander::new();
    let mut parser = Parser::new(macro_def);
    let macro_nodes = parser.parse().expect("Failed to parse macro definition");
    for node in macro_nodes {
        let _ = expander
            .expand_all_macros(node)
            .expect("Failed to define macro");
    }

    let mut parser = Parser::new(call);
    let mut call_nodes = parser.parse().expect("Failed to parse macro call");
    let call_syntax = call_nodes.remove(0);
    let call_span = call_syntax.span;
    let arg_span_a = find_syntax_symbol_span(&call_syntax, "qq_a")
        .expect("Expected to find qq_a in call syntax");
    let arg_span_b = find_syntax_symbol_span(&call_syntax, "qq_b")
        .expect("Expected to find qq_b in call syntax");

    let expanded = expander
        .expand(call_syntax)
        .expect("Failed to expand macro")
        .expect("Expected expansion result");
    let mut desugarer = Desugarer::new();
    let term = desugarer.desugar(expanded).expect("Failed to desugar");

    let mut spans_a = Vec::new();
    collect_var_spans(&term, "qq_a", &mut spans_a);
    assert_eq!(spans_a.len(), 1, "Expected a single qq_a occurrence");
    assert_eq!(
        spans_a[0], arg_span_a,
        "Spliced qq_a span should be preserved"
    );

    let mut spans_b = Vec::new();
    collect_var_spans(&term, "qq_b", &mut spans_b);
    assert_eq!(spans_b.len(), 1, "Expected a single qq_b occurrence");
    assert_eq!(
        spans_b[0], arg_span_b,
        "Spliced qq_b span should be preserved"
    );

    let mut app_spans = Vec::new();
    collect_app_spans(&term, call_span, &mut app_spans);
    assert!(
        !app_spans.is_empty(),
        "Expected application nodes in expansion"
    );
    for span in app_spans {
        assert_eq!(
            span, call_span,
            "application span should match macro call site"
        );
    }
}
