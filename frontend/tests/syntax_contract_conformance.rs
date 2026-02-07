use frontend::declaration_parser::DeclarationParser;
use frontend::macro_expander::Expander;
use frontend::parser::Parser;
use frontend::surface::{Declaration, SurfaceTerm, SurfaceTermKind, Syntax, SyntaxKind};

fn parse_syntax(source: &str) -> Vec<Syntax> {
    let mut parser = Parser::new(source);
    parser.parse().expect("parser should succeed")
}

fn parse_declarations(source: &str) -> Result<Vec<Declaration>, String> {
    let syntax = parse_syntax(source);
    let mut expander = Expander::new();
    let mut decl_parser = DeclarationParser::new(&mut expander);
    decl_parser.parse(syntax).map_err(|err| err.to_string())
}

fn decode_nat(term: &SurfaceTerm) -> Option<usize> {
    let mut value = 0usize;
    let mut current = term;
    loop {
        match &current.kind {
            SurfaceTermKind::Ctor(name, idx) if name == "Nat" && *idx == 0 => return Some(value),
            SurfaceTermKind::App(fun, arg, true) => match &fun.kind {
                SurfaceTermKind::Ctor(name, idx) if name == "Nat" && *idx == 1 => {
                    value += 1;
                    current = arg.as_ref();
                }
                _ => return None,
            },
            _ => return None,
        }
    }
}

fn decode_nat_list(term: &SurfaceTerm) -> Option<Vec<usize>> {
    let mut items = Vec::new();
    let mut current = term;
    loop {
        match &current.kind {
            SurfaceTermKind::Ctor(name, idx) if name == "List" && *idx == 0 => return Some(items),
            SurfaceTermKind::App(cons_head, tail, true) => match &cons_head.kind {
                SurfaceTermKind::App(cons_ctor, head, true) => match &cons_ctor.kind {
                    SurfaceTermKind::Ctor(name, idx) if name == "List" && *idx == 1 => {
                        items.push(decode_nat(head.as_ref())?);
                        current = tail.as_ref();
                    }
                    _ => return None,
                },
                _ => return None,
            },
            _ => return None,
        }
    }
}

#[test]
fn parser_enforces_numeric_and_symbol_rules() {
    let nodes = parse_syntax("-1 42");
    assert_eq!(nodes.len(), 2);
    assert!(matches!(&nodes[0].kind, SyntaxKind::Symbol(s) if s == "-1"));
    assert!(matches!(nodes[1].kind, SyntaxKind::Int(42)));
}

#[test]
fn parser_keeps_unknown_string_escapes() {
    let nodes = parse_syntax("\"a\\q\"");
    assert_eq!(nodes.len(), 1);
    assert!(matches!(&nodes[0].kind, SyntaxKind::String(s) if s == "a\\q"));
}

#[test]
fn parser_expands_quote_tokens() {
    let nodes = parse_syntax("'x `y ,z ,@w");
    assert_eq!(nodes.len(), 4);
    let expected_heads = ["quote", "quasiquote", "unquote", "unquote-splicing"];
    for (node, expected) in nodes.iter().zip(expected_heads) {
        match &node.kind {
            SyntaxKind::List(items) => {
                assert_eq!(items.len(), 2);
                assert!(matches!(&items[0].kind, SyntaxKind::Symbol(head) if head == expected));
            }
            other => panic!("expected quote expansion list, got {:?}", other),
        }
    }
}

#[test]
fn parser_parses_hole_token() {
    let nodes = parse_syntax("_");
    assert_eq!(nodes.len(), 1);
    assert!(matches!(nodes[0].kind, SyntaxKind::Hole));
}

#[test]
fn parser_indexes_left_to_right() {
    let nodes = parse_syntax("a[b][c]");
    assert_eq!(nodes.len(), 1);
    match &nodes[0].kind {
        SyntaxKind::Index(base, right) => {
            assert!(matches!(&right.kind, SyntaxKind::Symbol(s) if s == "c"));
            match &base.kind {
                SyntaxKind::Index(left_base, left_right) => {
                    assert!(matches!(&left_base.kind, SyntaxKind::Symbol(s) if s == "a"));
                    assert!(matches!(&left_right.kind, SyntaxKind::Symbol(s) if s == "b"));
                }
                other => panic!("expected nested left index, got {:?}", other),
            }
        }
        other => panic!("expected index syntax, got {:?}", other),
    }
}

#[test]
fn parser_skips_line_comments() {
    let nodes = parse_syntax("; comment\nx ; trailing\ny");
    assert_eq!(nodes.len(), 2);
    assert!(matches!(&nodes[0].kind, SyntaxKind::Symbol(s) if s == "x"));
    assert!(matches!(&nodes[1].kind, SyntaxKind::Symbol(s) if s == "y"));
}

#[test]
fn declaration_parser_accepts_module_import_open_forms() {
    let decls = parse_declarations(
        "(module Main)\n(import std.list as L)\n(import std.list)\n(import classical)\n(open L)",
    )
    .expect("declarations should parse");
    assert!(matches!(decls[0], Declaration::Module { .. }));
    assert!(matches!(
        decls[1],
        Declaration::ImportModule {
            ref module,
            alias: Some(ref alias)
        } if module == "std.list" && alias == "L"
    ));
    assert!(matches!(
        decls[2],
        Declaration::ImportModule {
            ref module,
            alias: None
        } if module == "std.list"
    ));
    assert!(matches!(decls[3], Declaration::ImportClassical));
    assert!(matches!(
        decls[4],
        Declaration::OpenModule { ref target } if target == "L"
    ));
}

#[test]
fn declaration_parser_rejects_invalid_import_shape() {
    let err = parse_declarations("(import std.list from L)").expect_err("import form must fail");
    assert!(err.contains("Expected '(import <module> as <alias>)'"));
}

#[test]
fn desugar_app_requires_exact_arity() {
    assert!(parse_declarations("(app f)").is_err());
    assert!(parse_declarations("(app f x y)").is_err());
}

#[test]
fn desugar_app_marks_braced_argument_implicit() {
    let decls = parse_declarations("(app f {x})").expect("app expression should parse");
    match &decls[0] {
        Declaration::Expr(term) => match term.kind {
            SurfaceTermKind::App(_, _, is_explicit) => assert!(!is_explicit),
            ref other => panic!("expected app term, got {:?}", other),
        },
        other => panic!("expected expression declaration, got {:?}", other),
    }
}

#[test]
fn desugar_match_requires_at_least_one_case() {
    assert!(parse_declarations("(match x (sort 0))").is_err());
}

#[test]
fn def_rejects_fix_outside_partial() {
    assert!(parse_declarations("(def bad (sort 1) (fix f (sort 1) f))").is_err());
}

#[test]
fn partial_allows_fix() {
    let decls = parse_declarations("(partial loop (sort 1) (fix f (sort 1) f))")
        .expect("partial with fix should parse");
    assert!(matches!(
        decls[0],
        Declaration::Def {
            totality: kernel::ast::Totality::Partial,
            ..
        }
    ));
}

#[test]
fn eval_requires_two_arguments() {
    assert!(parse_declarations("(eval code)").is_err());
}

#[test]
fn sort_requires_integer_literal() {
    assert!(parse_declarations("(sort lvl)").is_err());
}

#[test]
fn lam_rejects_non_symbol_binders() {
    assert!(parse_declarations("(lam (x y) (sort 0) x)").is_err());
}

#[test]
fn string_literals_desugar_to_list_nat_codes() {
    let decls = parse_declarations("\"Az\"").expect("string expression should parse");
    let term = match &decls[0] {
        Declaration::Expr(term) => term,
        other => panic!("expected expression declaration, got {:?}", other),
    };
    let codes = decode_nat_list(term).expect("expected List Nat encoding");
    assert_eq!(codes, vec![65, 122]);
}

#[test]
fn quote_defaults_unknown_syntax_to_hole() {
    let decls = parse_declarations("(quote {x})").expect("quote expression should parse");
    let term = match &decls[0] {
        Declaration::Expr(term) => term,
        other => panic!("expected expression declaration, got {:?}", other),
    };
    assert!(matches!(term.kind, SurfaceTermKind::Hole));
}
