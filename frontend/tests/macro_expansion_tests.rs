use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use insta::assert_debug_snapshot;

fn expand(input: &str) -> String {
    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();
    
    let mut results = String::new();
    for syntax in syntax_list {
         match expander.expand(syntax) {
             Ok(Some(term)) => {
                 results.push_str(&format!("{:?}\n", term));
             }
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
    (def l (List Nat) (cons 1 (cons 2 nil)))
    (quasiquote (0 (unquote-splicing l) 3))
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
