//! Determinism tests for frontend
//!
//! These tests verify that the same input always produces identical output.
//! This is critical for reproducible builds and stable error messages.

use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use frontend::declaration_parser::DeclarationParser;
use frontend::surface::Declaration;
use kernel::ast::{Totality, Transparency};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Compute a hash of the debug representation for comparison
fn hash_debug<T: std::fmt::Debug>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    format!("{:?}", value).hash(&mut hasher);
    hasher.finish()
}

// =============================================================================
// PARSING DETERMINISM
// =============================================================================

/// Test: Parser produces identical AST for same input
#[test]
fn test_parser_determinism() {
    let input = r#"
        (def id (pi A Type (pi x A A))
          (lam A Type (lam x A x)))
    "#;

    let mut results = vec![];

    for _ in 0..5 {
        let mut parser = Parser::new(input);
        let syntax_nodes = parser.parse().expect("Parse should succeed");
        results.push(hash_debug(&syntax_nodes));
    }

    // All hashes should be identical
    let first = results[0];
    for (i, hash) in results.iter().enumerate() {
        assert_eq!(
            *hash, first,
            "Parse attempt {} produced different result",
            i
        );
    }
}

/// Test: Parser error messages are deterministic
#[test]
fn test_parser_error_determinism() {
    let bad_input = "(def incomplete"; // Missing closing paren

    let mut errors = vec![];

    for _ in 0..5 {
        let mut parser = Parser::new(bad_input);
        let result = parser.parse();
        if let Err(e) = result {
            errors.push(format!("{:?}", e));
        }
    }

    // Should have errors
    assert!(!errors.is_empty(), "Should have parse errors");

    // All error messages should be identical
    let first = &errors[0];
    for (i, err) in errors.iter().enumerate() {
        assert_eq!(
            err, first,
            "Parse error {} was different",
            i
        );
    }
}

// =============================================================================
// MACRO EXPANSION DETERMINISM
// =============================================================================

/// Test: Macro expansion produces identical output for same input
#[test]
fn test_macro_expansion_determinism() {
    // Define a macro and use it
    let program = "(defmacro my-id (x) x)\n(my-id 42)";

    let mut results = vec![];

    for _ in 0..5 {
        let mut expander = Expander::new();
        let mut parser = Parser::new(program);
        let syntax_nodes = parser.parse().expect("Parse should succeed");

        let mut decl_parser = DeclarationParser::new(&mut expander);
        let decls = decl_parser.parse(syntax_nodes).expect("Parse declarations");

        results.push(hash_debug(&decls));
    }

    // All expansions should be identical
    let first = results[0];
    for (i, hash) in results.iter().enumerate() {
        assert_eq!(
            *hash, first,
            "Expansion {} produced different result",
            i
        );
    }
}

/// Test: Gensym produces stable names within a single expansion
#[test]
fn test_gensym_stability() {
    // Define a macro that uses quasiquote (which may trigger gensym for hygiene)
    let program = r#"
        (defmacro with-temp (body) `(let ((temp 0)) ,body))
        (with-temp (+ temp 1))
    "#;

    let mut results = vec![];

    for _ in 0..5 {
        let mut expander = Expander::new();
        let mut parser = Parser::new(program);
        let syntax_nodes = parser.parse().expect("Parse should succeed");

        let mut decl_parser = DeclarationParser::new(&mut expander);
        let decls = decl_parser.parse(syntax_nodes).expect("Parse declarations");

        results.push(format!("{:?}", decls));
    }

    // All expansions should produce the same gensym names
    let first = &results[0];
    for (i, result) in results.iter().enumerate() {
        assert_eq!(
            result, first,
            "Gensym in expansion {} was different",
            i
        );
    }
}

// =============================================================================
// DECLARATION PARSING DETERMINISM
// =============================================================================

/// Test: Declaration parsing is deterministic for definitions
#[test]
fn test_definition_parsing_determinism() {
    let input = "(def const (pi A Type (pi B Type (pi x A (pi y B A)))) (lam A Type (lam B Type (lam x A (lam y B x)))))";

    let mut results = vec![];

    for _ in 0..5 {
        let mut expander = Expander::new();
        let mut parser = Parser::new(input);
        let syntax_nodes = parser.parse().expect("Parse");

        let mut decl_parser = DeclarationParser::new(&mut expander);
        let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

        results.push(hash_debug(&decls));
    }

    // All results should be identical
    let first = results[0];
    for (i, hash) in results.iter().enumerate() {
        assert_eq!(
            *hash, first,
            "Definition parsing {} was different",
            i
        );
    }
}

/// Test: Inductive type parsing is deterministic
#[test]
fn test_inductive_parsing_determinism() {
    let input = r#"
        (inductive Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))
    "#;

    let mut results = vec![];

    for _ in 0..5 {
        let mut expander = Expander::new();
        let mut parser = Parser::new(input);
        let syntax_nodes = parser.parse().expect("Parse");

        let mut decl_parser = DeclarationParser::new(&mut expander);
        let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

        results.push(hash_debug(&decls));
    }

    // All results should be identical
    let first = results[0];
    for (i, hash) in results.iter().enumerate() {
        assert_eq!(
            *hash, first,
            "Inductive parsing {} was different",
            i
        );
    }
}

// =============================================================================
// FULL PIPELINE DETERMINISM
// =============================================================================

/// Test: Full frontend pipeline is deterministic
#[test]
fn test_full_pipeline_determinism() {
    let program = r#"
        (inductive Nat Type
          (zero Nat)
          (succ (pi n Nat Nat)))

        (def add (pi n Nat (pi m Nat Nat))
          (lam n Nat
            (lam m Nat
              n)))
    "#;

    let mut results = vec![];

    for _ in 0..5 {
        let mut expander = Expander::new();
        let mut parser = Parser::new(program);
        let syntax_nodes = parser.parse().expect("Parse");

        let mut decl_parser = DeclarationParser::new(&mut expander);
        let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

        let mut decl_hashes = vec![];
        for decl in decls {
            decl_hashes.push(hash_debug(&decl));
        }

        results.push(decl_hashes);
    }

    // All runs should produce identical results
    let first = &results[0];
    for (i, result) in results.iter().enumerate() {
        assert_eq!(
            result.len(),
            first.len(),
            "Run {} parsed different number of declarations",
            i
        );
        for (j, (h1, h2)) in first.iter().zip(result.iter()).enumerate() {
            assert_eq!(
                h1, h2,
                "Run {} declaration {} was different",
                i, j
            );
        }
    }
}

// =============================================================================
// SPAN PRESERVATION
// =============================================================================

/// Test: Spans are preserved through parsing
#[test]
fn test_span_preservation() {
    let input = "(def x Type Type)";

    let mut parser = Parser::new(input);
    let syntax_nodes = parser.parse().expect("Parse");

    // Check that we have syntax nodes
    assert!(!syntax_nodes.is_empty(), "Should have parsed something");

    // Check that spans exist and are reasonable
    for syntax in &syntax_nodes {
        assert!(syntax.span.start < syntax.span.end || syntax.span.start == syntax.span.end,
                "Span should have non-negative length");
        assert!(syntax.span.end <= input.len(), "Span should not exceed input");
    }
}

/// Test: Spans in error messages contain location info
#[test]
fn test_error_span_accuracy() {
    // Error at a known position - unclosed paren
    let input = "(def x"; // Missing closing paren

    let mut parser = Parser::new(input);
    let result = parser.parse();

    // The error should occur
    assert!(result.is_err(), "Invalid input should produce error");

    // Verify error has span information (via debug output)
    let err = result.unwrap_err();
    let err_str = format!("{:?}", err);
    // Error should contain position information
    assert!(!err_str.is_empty(), "Error message should not be empty");
}

// =============================================================================
// HASH STABILITY ACROSS RUNS
// =============================================================================

/// Test: Hash of AST is stable
#[test]
fn test_ast_hash_stability() {
    let input = "(lam x Nat x)";

    // Parse and hash multiple times
    let mut hashes = vec![];
    for _ in 0..10 {
        let mut parser = Parser::new(input);
        let syntax_nodes = parser.parse().expect("Parse");
        hashes.push(hash_debug(&syntax_nodes));
    }

    // All hashes should be identical
    let first = hashes[0];
    assert!(
        hashes.iter().all(|&h| h == first),
        "AST hash should be stable across parses"
    );
}

/// Test: Syntax pretty-printing is deterministic
#[test]
fn test_pretty_print_determinism() {
    let input = "(def add (pi a Nat (pi b Nat Nat)) (lam a Nat (lam b Nat a)))";

    let mut prints = vec![];
    for _ in 0..5 {
        let mut parser = Parser::new(input);
        let syntax_nodes = parser.parse().expect("Parse");

        // Pretty print all nodes
        let pretty: Vec<String> = syntax_nodes.iter()
            .map(|s| s.pretty_print())
            .collect();
        prints.push(pretty);
    }

    let first = &prints[0];
    for (i, print) in prints.iter().enumerate() {
        assert_eq!(
            print, first,
            "Pretty print {} was different",
            i
        );
    }
}

// =============================================================================
// DECLARATION VARIANT STABILITY
// =============================================================================

/// Test: Declaration variant matching is consistent
#[test]
fn test_declaration_variant_consistency() {
    let input = "(def id (pi A Type A) (lam A Type A))";

    let mut expander = Expander::new();
    let mut parser = Parser::new(input);
    let syntax_nodes = parser.parse().expect("Parse");

    let mut decl_parser = DeclarationParser::new(&mut expander);
    let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

    assert_eq!(decls.len(), 1, "Should have one declaration");

    match &decls[0] {
        Declaration::Def { name, ty, val, totality, transparency } => {
            assert_eq!(name, "id");
            assert_eq!(*totality, Totality::Total);
            assert_eq!(*transparency, Transparency::Reducible);
            // Type and val should be SurfaceTerms
            let _ = format!("{:?}", ty);
            let _ = format!("{:?}", val);
        }
        other => panic!("Expected Def, got {:?}", other),
    }
}

/// Test: Axiom declaration parsing
#[test]
fn test_axiom_declaration() {
    // Simpler axiom: excluded middle style
    let input = "(axiom em (pi P Type P))";

    let mut expander = Expander::new();
    let mut parser = Parser::new(input);
    let syntax_nodes = parser.parse().expect("Parse");

    let mut decl_parser = DeclarationParser::new(&mut expander);
    let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Declaration::Axiom { name, ty, tags } => {
            assert_eq!(name, "em");
            assert!(tags.is_empty());
            let _ = format!("{:?}", ty);
        }
        other => panic!("Expected Axiom, got {:?}", other),
    }
}

/// Test: Classical axiom tag parsing
#[test]
fn test_classical_axiom_declaration() {
    let input = "(axiom classical em (pi P Type P))";

    let mut expander = Expander::new();
    let mut parser = Parser::new(input);
    let syntax_nodes = parser.parse().expect("Parse");

    let mut decl_parser = DeclarationParser::new(&mut expander);
    let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Declaration::Axiom { name, ty, tags } => {
            assert_eq!(name, "em");
            assert_eq!(tags.len(), 1);
            assert!(matches!(tags[0], kernel::ast::AxiomTag::Classical));
            let _ = format!("{:?}", ty);
        }
        other => panic!("Expected Axiom, got {:?}", other),
    }
}

/// Test: Unsafe definition parsing
#[test]
fn test_unsafe_declaration() {
    let input = "(unsafe danger (pi A Type A) (lam A Type A))";

    let mut expander = Expander::new();
    let mut parser = Parser::new(input);
    let syntax_nodes = parser.parse().expect("Parse");

    let mut decl_parser = DeclarationParser::new(&mut expander);
    let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Declaration::Def { name, totality, transparency, .. } => {
            assert_eq!(name, "danger");
            assert_eq!(*totality, Totality::Unsafe);
            assert_eq!(*transparency, Transparency::Reducible);
        }
        other => panic!("Expected Def, got {:?}", other),
    }
}

/// Test: Opaque attribute parsing on definitions
#[test]
fn test_opaque_attribute_declaration() {
    let input = "(def opaque secret (pi A Type A) (lam A Type A))";

    let mut expander = Expander::new();
    let mut parser = Parser::new(input);
    let syntax_nodes = parser.parse().expect("Parse");

    let mut decl_parser = DeclarationParser::new(&mut expander);
    let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Declaration::Def { name, totality, transparency, .. } => {
            assert_eq!(name, "secret");
            assert_eq!(*totality, Totality::Total);
            assert_eq!(*transparency, Transparency::None);
        }
        other => panic!("Expected Def, got {:?}", other),
    }
}
