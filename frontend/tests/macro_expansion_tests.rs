use frontend::desugar::Desugarer;
use frontend::diagnostics::Level;
use frontend::macro_expander::{Expander, ExpansionError, MacroBoundaryPolicy};
use frontend::parser::Parser;
use insta::assert_debug_snapshot;

fn expand(input: &str) -> String {
    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();
    let mut desugarer = Desugarer::new();

    let mut results = String::new();
    for syntax in syntax_list {
        match expander.expand(syntax) {
            Ok(Some(expanded)) => match desugarer.desugar(expanded) {
                Ok(term) => results.push_str(&format!("{:?}\n", term)),
                Err(e) => results.push_str(&format!("Error: {}\n", e)),
            },
            Ok(None) => {
                // Macro definition
                results.push_str("Macro defined\n");
            }
            Err(e) => {
                results.push_str(&format!("Error: {}\n", e));
            }
        }
    }
    results
}

#[test]
fn test_simple_macro() {
    let input = "
    (defmacro id (x) x)
    (id 42)
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_macro_hygiene_basic() {
    let input = "
    (defmacro m (body) (lam x Nat body))
    (def y Nat 10)
    (m y)
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_quasiquote_basic() {
    let input = "
    (quasiquote (1 2 3))
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_unquote() {
    let input = "
    (def x Nat 10)
    (quasiquote (1 (unquote x) 3))
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_unquote_splicing() {
    let input = "
    (quasiquote (0 (unquote-splicing (quasiquote (1 2))) 3))
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_nested_quasiquote() {
    let input = "
    (quasiquote (quasiquote (unquote 1)))
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_macro_recursive_expansion() {
    let input = "
    (defmacro m1 () 1)
    (defmacro m2 () (m1))
    (m2)
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_macro_expansion_budget_exhaustion() {
    let input = "
    (defmacro loop (x) (loop (quote x)))
    (loop x)
    ";
    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();
    expander.set_macro_expansion_limits(3, 64);

    let mut expansion_error = None;
    for syntax in syntax_list {
        match expander.expand(syntax) {
            Ok(_) => {}
            Err(err) => {
                expansion_error = Some(err);
                break;
            }
        }
    }

    let expansion_error = expansion_error.expect("Expected expansion limit error");
    match &expansion_error {
        ExpansionError::ExpansionStepLimitExceeded { limit } => assert_eq!(*limit, 3),
        _ => panic!("Expected step limit error, got {:?}", expansion_error),
    }

    let diagnostics = expander.take_pending_diagnostics();
    assert_eq!(diagnostics.len(), 1);
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.code, Some("F0106"));
    assert!(diagnostic
        .message
        .contains("Macro expansion step limit exceeded"));
    assert!(!diagnostic.labels.is_empty());
}

#[test]
fn test_macro_expansion_cycle_detection() {
    let input = "
    (defmacro loop () (loop))
    (loop)
    ";
    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();

    let mut expansion_error = None;
    for syntax in syntax_list {
        match expander.expand(syntax) {
            Ok(_) => {}
            Err(err) => {
                expansion_error = Some(err);
                break;
            }
        }
    }

    let expansion_error = expansion_error.expect("Expected expansion cycle error");
    match &expansion_error {
        ExpansionError::MacroExpansionCycle { cycle } => {
            assert!(cycle.len() >= 2, "Cycle should include repeated macro");
            assert_eq!(cycle[0], "loop");
            assert_eq!(cycle[cycle.len() - 1], "loop");
        }
        _ => panic!(
            "Expected macro expansion cycle error, got {:?}",
            expansion_error
        ),
    }

    let diagnostics = expander.take_pending_diagnostics();
    assert_eq!(diagnostics.len(), 1);
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.code, Some("F0107"));
    assert!(diagnostic
        .message
        .contains("Macro expansion cycle detected"));
    assert!(!diagnostic.labels.is_empty());
}

#[test]
fn test_macro_expansion_memoization_reuses_identical_calls() {
    let input = "
    (defmacro idm (x) x)
    ((idm a) (idm a))
    ";
    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();
    expander.set_macro_expansion_limits(1, 64);

    let mut last_expanded = None;
    for syntax in syntax_list {
        match expander.expand(syntax) {
            Ok(Some(expanded)) => last_expanded = Some(expanded.pretty_print_stable()),
            Ok(None) => {}
            Err(err) => panic!("Expansion should succeed with memoization, got {:?}", err),
        }
    }

    assert_eq!(last_expanded.as_deref(), Some("(a a)"));
}

#[test]
fn test_hygiene_test4() {
    // The regression test case we just fixed
    let input = "
    (def z Nat 7)
    (defmacro m3 () z)
    (lam z Nat (m3))
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_determinism() {
    let input = "
    (defmacro m (x) (let y Nat x y))
    (m 5)
    ";
    let out1 = expand(input);
    let out2 = expand(input);
    assert_eq!(out1, out2);
}

#[test]
fn test_nested_macro_hygiene_torture() {
    let input = "
    (defmacro m1 (val) (let x Nat val x))
    (defmacro m2 (val) (let x Nat val (m1 x)))
    (m2 10)
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_nested_macro_hygiene_outer_inner() {
    let input = "
    (defmacro inner () x)
    (defmacro outer (e) (quasiquote (let x Nat 0 (unquote e))))
    (outer (inner))
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_macro_surface_forms() {
    let input = "
    (defmacro mk_opaque (name ty val) (opaque name ty val))
    (defmacro mk_transparent (name ty val) (transparent name ty val))
    (defmacro mk_eval (code cap) (eval code cap))
    (defmacro mk_import_classical ()
      (import classical))
    (defmacro mk_axiom_classical (name ty) (axiom classical name ty))

    (mk_opaque secret Ty Val)
    (mk_transparent open Ty Val)
    (mk_eval dyn_code dyn_cap)
    (mk_import_classical)
    (mk_axiom_classical choice (sort 0))
    ";
    assert_debug_snapshot!(expand(input));
}

#[test]
fn test_macro_trace_call_stack_spans() {
    let macros = "(defmacro m1 () (m2))\n(defmacro m2 () 1)\n";
    let call = "(m1)";

    let mut expander = Expander::new();
    let mut parser = Parser::new(macros);
    let macro_nodes = parser.parse().expect("Failed to parse macro definitions");
    for node in macro_nodes {
        let _ = expander
            .expand_all_macros(node)
            .expect("Failed to define macro");
    }

    let mut parser = Parser::new(call);
    let mut call_nodes = parser.parse().expect("Failed to parse macro call");
    let call_syntax = call_nodes.remove(0);
    let call_span = call_syntax.span;

    let (_expanded, trace) = expander
        .expand_syntax_with_trace(call_syntax)
        .expect("Failed to expand with trace");

    assert_eq!(trace.len(), 2, "Expected two trace entries");
    assert_eq!(trace[0].name, "m1");
    assert_eq!(trace[0].depth, 0);
    assert_eq!(trace[0].span, call_span);
    assert_eq!(trace[1].name, "m2");
    assert_eq!(trace[1].depth, 1);
    assert_eq!(trace[1].span, call_span);
}

#[test]
fn test_reserved_macro_names_rejected() {
    let input = "
    (defmacro def (x) x)
    (defmacro axiom (x) x)
    (defmacro unsafe (x) x)
    (defmacro partial (x) x)
    (defmacro instance (x) x)
    (defmacro inductive (x) x)
    (defmacro structure (x) x)
    ";

    let output = expand(input);
    assert!(output.contains("'def' is a reserved macro name"));
    assert!(output.contains("'axiom' is a reserved macro name"));
    assert!(output.contains("'unsafe' is a reserved macro name"));
    assert!(output.contains("'partial' is a reserved macro name"));
    assert!(output.contains("'instance' is a reserved macro name"));
    assert!(output.contains("'inductive' is a reserved macro name"));
    assert!(output.contains("'structure' is a reserved macro name"));
}

#[test]
fn test_macro_expansion_warns_on_unsafe_classical() {
    let input = "
    (defmacro mk_unsafe (name ty val) (unsafe name ty val))
    (defmacro mk_classical (name ty) (axiom classical name ty))
    (defmacro mk_import_classical () (import classical))
    (defmacro mk_eval (code cap) (eval code cap))
    (mk_unsafe foo Nat zero)
    (mk_classical choice (sort 0))
    (mk_import_classical)
    (mk_eval dyn_code dyn_cap)
    ";

    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
    let mut diagnostics = Vec::new();

    for syntax in syntax_list {
        let _ = expander.expand(syntax);
        diagnostics.extend(expander.take_pending_diagnostics());
    }

    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Warning && d.message.contains("unsafe")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Warning && d.message.contains("axiom classical")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Warning && d.message.contains("import classical")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Warning && d.message.contains("eval")));
}

#[test]
fn test_macro_expansion_quasiquote_smuggling_warns() {
    let input = "
    (defmacro smuggle_axiom () (quasiquote (axiom classical bad (sort 0))))
    (defmacro smuggle_unsafe () (quasiquote (unsafe foo Nat zero)))
    (defmacro smuggle_import () (quasiquote (import classical)))
    (smuggle_axiom)
    (smuggle_unsafe)
    (smuggle_import)
    ";

    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
    let mut diagnostics = Vec::new();

    for syntax in syntax_list {
        let _ = expander.expand(syntax);
        diagnostics.extend(expander.take_pending_diagnostics());
    }

    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Warning && d.message.contains("axiom classical")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Warning && d.message.contains("unsafe")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Warning && d.message.contains("import classical")));
}

#[test]
fn test_macro_expansion_quasiquote_smuggling_denied() {
    let input = "
    (defmacro smuggle_axiom () (quasiquote (axiom classical bad (sort 0))))
    (defmacro smuggle_unsafe () (quasiquote (unsafe foo Nat zero)))
    (defmacro smuggle_import () (quasiquote (import classical)))
    (smuggle_axiom)
    (smuggle_unsafe)
    (smuggle_import)
    ";

    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = Vec::new();
    let mut denied_hits: Vec<Vec<String>> = Vec::new();

    for syntax in syntax_list {
        match expander.expand(syntax) {
            Err(ExpansionError::MacroBoundaryDenied { hits, .. }) => {
                denied_hits.push(hits);
            }
            Ok(_) => {}
            Err(err) => panic!("Unexpected expansion error: {:?}", err),
        }
        diagnostics.extend(expander.take_pending_diagnostics());
    }

    assert_eq!(denied_hits.len(), 3);
    assert!(denied_hits
        .iter()
        .any(|hits| hits.iter().any(|hit| hit == "axiom classical")));
    assert!(denied_hits
        .iter()
        .any(|hits| hits.iter().any(|hit| hit == "unsafe")));
    assert!(denied_hits
        .iter()
        .any(|hits| hits.iter().any(|hit| hit == "import classical")));

    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error
            && d.message.contains("macro boundary violations are errors")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error && d.message.contains("axiom classical")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error && d.message.contains("unsafe")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error && d.message.contains("import classical")));
}

#[test]
fn test_direct_quasiquote_smuggling_denied() {
    let input = "
    (quasiquote (axiom classical bad (sort 0)))
    (quasiquote (unsafe foo Nat zero))
    (quasiquote (import classical))
    (quasiquote (eval zero))
    ";

    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let mut diagnostics = Vec::new();
    let mut denied_hits: Vec<Vec<String>> = Vec::new();

    for syntax in syntax_list {
        match expander.expand(syntax) {
            Err(ExpansionError::MacroBoundaryDenied { hits, .. }) => {
                denied_hits.push(hits);
            }
            Ok(_) => {}
            Err(err) => panic!("Unexpected expansion error: {:?}", err),
        }
        diagnostics.extend(expander.take_pending_diagnostics());
    }

    assert_eq!(denied_hits.len(), 4);
    assert!(denied_hits
        .iter()
        .any(|hits| hits.iter().any(|hit| hit == "axiom classical")));
    assert!(denied_hits
        .iter()
        .any(|hits| hits.iter().any(|hit| hit == "unsafe")));
    assert!(denied_hits
        .iter()
        .any(|hits| hits.iter().any(|hit| hit == "import classical")));
    assert!(denied_hits
        .iter()
        .any(|hits| hits.iter().any(|hit| hit == "eval")));

    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error
            && d.message.contains("macro boundary violations are errors")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error && d.message.contains("axiom classical")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error && d.message.contains("unsafe")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error && d.message.contains("import classical")));
    assert!(diagnostics
        .iter()
        .any(|d| d.level == Level::Error && d.message.contains("eval")));
}
