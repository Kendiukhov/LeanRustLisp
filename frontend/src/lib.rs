pub mod parser;
pub mod elaborator;
pub mod surface;
pub mod macro_expander;
pub mod declaration_parser;
pub mod diagnostics;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;
    use crate::macro_expander::Expander;
    use crate::surface::ScopeId;

    #[test]
    fn test_parse_simple() {
        let input = "(lam x (sort 0) x)";
        let mut parser = Parser::new(input);
        let syntax = parser.parse().expect("Failed to parse");
        println!("Syntax: {:?}", syntax);
        assert_eq!(syntax.len(), 1);
    }

    #[test]
    fn test_expand_lam() {
         let input = "(lam x (sort 0) x)";
         let mut parser = Parser::new(input);
         let syntax = parser.parse().expect("Failed to parse");

         let mut expander = Expander::new();
         let term = expander.expand(syntax[0].clone()).expect("Failed to expand").unwrap();
         println!("Expanded: {:?}", term);

         match &term.kind {
             surface::SurfaceTermKind::Lam(n, _, _, _) => {
                 assert!(n.starts_with("x_g"), "Expected name starting with x_g, got {}", n);
             }
             _ => panic!("Expected Lam"),
         }
    }

    #[test]
    fn test_hygiene_scope_creation() {
        let mut expander = Expander::new();

        // Each call to new_scope should produce unique IDs
        let scope1 = expander.new_scope();
        let scope2 = expander.new_scope();
        let scope3 = expander.new_scope();

        assert_ne!(scope1, scope2);
        assert_ne!(scope2, scope3);
        assert_ne!(scope1, scope3);
    }

    #[test]
    fn test_hygiene_scopes_compatible() {
        // Reference with more scopes can see definitions with fewer scopes
        let ref_scopes = vec![ScopeId(0), ScopeId(1), ScopeId(2)];
        let def_scopes = vec![ScopeId(0), ScopeId(1)];
        assert!(Expander::scopes_compatible(&ref_scopes, &def_scopes));

        // Reference with fewer scopes cannot see definitions with more scopes
        let ref_scopes2 = vec![ScopeId(0)];
        let def_scopes2 = vec![ScopeId(0), ScopeId(1)];
        assert!(!Expander::scopes_compatible(&ref_scopes2, &def_scopes2));

        // Empty scopes are compatible with empty scopes
        let empty: Vec<ScopeId> = vec![];
        assert!(Expander::scopes_compatible(&empty, &empty));

        // Any scopes are compatible with empty definition scopes
        let some_scopes = vec![ScopeId(0), ScopeId(1)];
        assert!(Expander::scopes_compatible(&some_scopes, &empty));
    }

    #[test]
    fn test_macro_expansion_adds_scope() {
        // Define a simple macro: (defmacro id (x) x)
        let input = "(defmacro id (x) x)";
        let mut parser = Parser::new(input);
        let syntax = parser.parse().expect("Failed to parse");

        let mut expander = Expander::new();
        // This registers the macro but returns None
        let _ = expander.expand_all_macros(syntax[0].clone()).expect("Failed to expand");

        // Now use the macro: (id y)
        let use_input = "(id y)";
        let mut parser2 = Parser::new(use_input);
        let use_syntax = parser2.parse().expect("Failed to parse");

        let expanded = expander.expand_all_macros(use_syntax[0].clone())
            .expect("Failed to expand")
            .expect("Expected expanded syntax");

        // The result should be 'y' - an argument, so it keeps original scopes (none)
        if let surface::SyntaxKind::Symbol(s) = &expanded.kind {
            assert_eq!(s, "y");
            // Argument 'y' should NOT have a macro scope (it came from the use site)
            // It should have its original scopes (empty in this case)
        } else {
            panic!("Expected symbol, got {:?}", expanded.kind);
        }
    }

    #[test]
    fn test_macro_introduced_syntax_gets_scope() {
        // Define a macro that introduces its own syntax: (defmacro const-zero () zero)
        let input = "(defmacro const-zero () zero)";
        let mut parser = Parser::new(input);
        let syntax = parser.parse().expect("Failed to parse");

        let mut expander = Expander::new();
        let _ = expander.expand_all_macros(syntax[0].clone()).expect("Failed to expand");

        // Use the macro: (const-zero)
        let use_input = "(const-zero)";
        let mut parser2 = Parser::new(use_input);
        let use_syntax = parser2.parse().expect("Failed to parse");

        let expanded = expander.expand_all_macros(use_syntax[0].clone())
            .expect("Failed to expand")
            .expect("Expected expanded syntax");

        // The result should be 'zero' with a macro scope
        if let surface::SyntaxKind::Symbol(s) = &expanded.kind {
            assert_eq!(s, "zero");
            // Macro-introduced 'zero' SHOULD have a macro scope
            assert!(!expanded.scopes.is_empty(), "Macro-introduced symbol should have a scope");
        } else {
            panic!("Expected symbol, got {:?}", expanded.kind);
        }
    }

    #[test]
    #[test]
    fn test_add_remove_scope() {
        let syntax = surface::Syntax {
            kind: surface::SyntaxKind::Symbol("test".to_string()),
            span: surface::Span { start: 0, end: 4, line: 1, col: 1 },
            scopes: vec![ScopeId(0)],
        };

        // Add a scope
        let with_scope = Expander::add_scope(&syntax, ScopeId(1));
        assert!(with_scope.scopes.contains(&ScopeId(0)));
        assert!(with_scope.scopes.contains(&ScopeId(1)));
        assert_eq!(with_scope.scopes.len(), 2);

        // Adding same scope again should not duplicate
        let with_same = Expander::add_scope(&with_scope, ScopeId(1));
        assert_eq!(with_same.scopes.len(), 2);

        // Remove a scope
        let without_scope = Expander::remove_scope(&with_scope, ScopeId(1));
        assert!(without_scope.scopes.contains(&ScopeId(0)));
        assert!(!without_scope.scopes.contains(&ScopeId(1)));
        assert_eq!(without_scope.scopes.len(), 1);
    }
}
