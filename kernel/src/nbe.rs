use crate::ast::{Term, Level, BinderInfo};
use crate::checker::Env;
use std::rc::Rc;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Totality;
    use crate::ast::Definition;

    #[test]
    fn test_eval_id() {
        // \x. x
        let id = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);
        let env = Env::new();
        
        let val = eval(&id, &vec![], &env);
        if let Value::Lam(_, _, _) = val {
            // OK
        } else {
            panic!("Expected Lam");
        }
    }

    #[test]
    fn test_beta_reduction() {
        // (\x. x) a
        let id = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);
        let app = Term::app(id, Rc::new(Term::Const("a".to_string(), vec![]))); // a is opaque neutral
        
        let env = Env::new();
        let val = eval(&app, &vec![], &env);
        
        // Should reduce to Neutral(Const("a"))
        match val {
            Value::Neutral(head, spine) => {
                match *head {
                    Neutral::Const(n, _) => assert_eq!(n, "a"),
                    _ => panic!("Expected Const('a') head"),
                }
                assert!(spine.is_empty());
            }
            _ => panic!("Expected Neutral"),
        }
    }

    #[test]
    fn test_delta_reduction() {
        let mut env = Env::new();
        // def one = succ zero
        let one_tm = Term::app(Rc::new(Term::Const("succ".to_string(), vec![])), Rc::new(Term::Const("zero".to_string(), vec![])));
        
        let def = Definition::total("one".to_string(), Term::sort(Level::Zero), one_tm.clone());
        env.add_definition(def).unwrap();
        
        let t = Rc::new(Term::Const("one".to_string(), vec![]));
        let val = eval(&t, &vec![], &env);
        
        // Should evaluate to one_tm (reduced to Neutral App(succ, zero))
        // succ and zero are not defined, so they are neutral consts.
        // App(Neutral(succ), zero)
        
        match val {
            Value::Neutral(head, spine) => {
                 // Head is succ
                 match *head {
                     Neutral::Const(n, _) => assert_eq!(n, "succ"),
                     _ => panic!("Expected succ"),
                 }
                 assert_eq!(spine.len(), 1);
            }
            _ => panic!("Expected Neutral application"),
        }
    }
    
    #[test]
    fn test_defeq_beta() {
        let env = Env::new();
        // (\x. x) y
        let t1 = Term::app(
            Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default),
            Rc::new(Term::Const("y".to_string(), vec![]))
        );
        // y
        let t2 = Rc::new(Term::Const("y".to_string(), vec![]));
        
        assert!(is_def_eq(t1, t2, &env));
    }

    #[test]
    fn test_eta_equality() {
        let env = Env::new();
        // f = \x. f x ?
        // We test (\x. f x) == f
        let f = Rc::new(Term::Const("f".to_string(), vec![]));
        
        let eta = Term::lam(
            Term::sort(Level::Zero), 
            Term::app(f.clone(), Term::var(0)),
            BinderInfo::Default
        );
        assert!(is_def_eq(eta, f, &env), "Eta reduction failed");
    }

    #[test]
    fn test_deep_application() {
        let env = Env::new();
        // (\x. \y. \z. z) a b c -> c
        let mut term = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default); // \z. z
        term = Term::lam(Term::sort(Level::Zero), term, BinderInfo::Default); // \y. \z. z
        term = Term::lam(Term::sort(Level::Zero), term, BinderInfo::Default); // \x. \y. \z. z
        
        let a = Rc::new(Term::Const("a".to_string(), vec![]));
        let b = Rc::new(Term::Const("b".to_string(), vec![]));
        let c = Rc::new(Term::Const("c".to_string(), vec![]));
        
        term = Term::app(term, a);
        term = Term::app(term, b);
        term = Term::app(term, c.clone());
        
        let val = eval(&term, &vec![], &env);
        let quoted = quote(val, 0, &env);
        
        if let Term::Const(n, _) = &*quoted {
            assert_eq!(n, "c");
        } else {
            panic!("Deep application failed: {:?}", quoted);
        }
    }
    
    #[test]
    fn test_vec_indices() {
        let mut env = Env::new();
        // Vec A n
        
        let nat = crate::ast::InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            ty: Term::sort(Level::Zero),
            ctors: vec![
                crate::ast::Constructor { name: "zero".to_string(), ty: Rc::new(Term::Ind("Nat".to_string(), vec![])) },
                crate::ast::Constructor { name: "succ".to_string(), ty: Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Rc::new(Term::Ind("Nat".to_string(), vec![])), BinderInfo::Default) }
            ],
            num_params: 0,
            is_copy: false,
        };
        env.add_inductive(nat).unwrap();
        
        let vec_decl = crate::ast::InductiveDecl {
            name: "Vec".to_string(),
            univ_params: vec![],
            // Pi(A:Type) -> Pi(n:Nat) -> Type
            ty: Term::pi(
                Rc::new(Term::Sort(Level::Zero)), 
                Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Term::sort(Level::Zero), BinderInfo::Default),
                BinderInfo::Default
            ),
            ctors: vec![
                crate::ast::Constructor {
                    name: "nil".to_string(),
                    ty: Term::app(Rc::new(Term::Ind("Vec".to_string(), vec![])), Rc::new(Term::Ctor("Nat".to_string(), 0, vec![])))
                }
            ],
            num_params: 1, // A
            is_copy: false,
        };
        env.add_inductive(vec_decl).unwrap();
        
        let a = Term::sort(Level::Zero);
        let recursor = Rc::new(Term::Rec("Vec".to_string(), vec![]));
        let motive = Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), // index
                    Term::lam(Term::app(Rc::new(Term::Ind("Vec".to_string(), vec![])), Term::var(0)), // val
                    Term::sort(Level::Zero), BinderInfo::Default), BinderInfo::Default);
        
        let base = Rc::new(Term::Const("base".to_string(), vec![])); 
        let zero = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
        let nil = Rc::new(Term::Ctor("Vec".to_string(), 0, vec![])); // nil has params attached in Value::Ctor, but Term::Ctor it is just empty? Term::Ctor does NOT have params?
        // Term::Ctor(name, idx, levels). Params are applied via App. (Checked AST: Term::Ctor doesn't hold args).
        // Wait, Ctor args in Term are just App spines.
        // In Value they are stored.
        // So `nil` term is `Ctor(..., 0, ...)`.
        // But `Vec.nil` takes ONE param (A).
        // So `nil` term application is `App(Ctor(nil), A)`.
        
        let nil_app = Term::app(nil, a.clone());
        
        // rec A P base zero (nil A)
        let app = Term::app(Term::app(Term::app(Term::app(Term::app(recursor, a), motive), base.clone()), zero), nil_app);
        
        let val = eval(&app, &vec![], &env);
        let quoted = quote(val, 0, &env);
        assert!(is_def_eq(quoted, base, &env), "Vec.rec did not reduce to base");
    }
    #[test]
    fn test_shadowing() {
        let env = Env::new();
        // (\x. (\x. x) a) b -> a
        // Var(0) inside inner is inner x.
        // Var(1) inside inner is outer x? No.
        // (\x. (\y. y) a) b -> a.
        // (\x. (\x. x) x) a -> a.
        
        // Inner: \x. x  (Var(0))
        let inner = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);
        // Outer body: app(inner, Var(0)) -> app(\x.x, x)
        let body = Term::app(inner, Term::var(0));
        // Outer: \x. body
        let outer = Term::lam(Term::sort(Level::Zero), body, BinderInfo::Default);
        
        // App(outer, a)
        let a = Rc::new(Term::Const("a".to_string(), vec![]));
        let term = Term::app(outer, a.clone());
        
        // Should reduce to a
        let val = eval(&term, &vec![], &env);
        let quoted = quote(val, 0, &env);
        
        // a is Const("a")
        // Check if quoted == a
        if let Term::Const(n, _) = &*quoted {
            assert_eq!(n, "a");
        } else {
            panic!("Expected Const(a), got {:?}", quoted);
        }
    }
    
    #[test]
    fn test_partial_app_rec() {
         // Test that we can partially apply the result of recursion
         // add one : Nat -> Nat
         // (from previous test setup)
         // We duplicate the setup briefly or reuse?
         // Reuse is hard in unit tests without fixture.
         // Setup minimal Nat again.
         
        let mut env = Env::new();
        let nat_decl = crate::ast::InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            ty: Term::sort(Level::Zero),
            ctors: vec![
                crate::ast::Constructor { name: "zero".to_string(), ty: Rc::new(Term::Ind("Nat".to_string(), vec![])) },
                crate::ast::Constructor { name: "succ".to_string(), ty: Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Rc::new(Term::Ind("Nat".to_string(), vec![])), BinderInfo::Default) }
            ],
            num_params: 0,
            is_copy: false,
        };
        env.add_inductive(nat_decl).unwrap();

        // Constants
        let zero = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
        let succ = |t: Rc<Term>| Term::app(Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])), t);
        let one = succ(zero.clone());

        let motive = Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Rc::new(Term::Ind("Nat".to_string(), vec![])), BinderInfo::Default), BinderInfo::Default);
        let base = Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), Term::var(0), BinderInfo::Default);
        let step = Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), Term::lam(Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Rc::new(Term::Ind("Nat".to_string(), vec![])), BinderInfo::Default), Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), succ(Term::app(Term::var(1), Term::var(0))), BinderInfo::Default), BinderInfo::Default), BinderInfo::Default);

        let recursor = Rc::new(Term::Rec("Nat".to_string(), vec![]));
        let add_one = Term::app(Term::app(Term::app(Term::app(recursor, motive), base), step), one.clone());
        
        // Evaluate add_one
        let val = eval(&add_one, &vec![], &env);
        // Should be a Lambda waiting for m
        match val {
            Value::Lam(_, _, _) | Value::Pi(_, _, _, _) => {}, // OK
             // Actually it might be a closure? Value::Lam
            _ => panic!("Expected function from partial application, got {:?}", val),
        }
        
        // Now apply it to one
        let one_val = eval(&one, &vec![], &env);
        let res = apply(val, one_val, &env);
        let quoted = quote(res, 0, &env);
        
        let two = succ(one.clone());
        assert!(is_def_eq(quoted, two, &env));
    }
    #[test]
    fn test_nat_add_recursion() {
        let mut env = Env::new();
        // Define Nat
        let nat_decl = crate::ast::InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            ty: Term::sort(Level::Zero),
            ctors: vec![
                crate::ast::Constructor {
                    name: "zero".to_string(),
                    ty: Rc::new(Term::Ind("Nat".to_string(), vec![])),
                },
                crate::ast::Constructor {
                    name: "succ".to_string(),
                    ty: Term::pi(
                        Rc::new(Term::Ind("Nat".to_string(), vec![])),
                        Rc::new(Term::Ind("Nat".to_string(), vec![])),
                        BinderInfo::Default
                    ), // Nat -> Nat
                }
            ],
            num_params: 0,
            is_copy: false,
        };
        env.add_inductive(nat_decl).unwrap();

        // Constants
        let zero = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
        let succ = |t: Rc<Term>| Term::app(Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])), t);
        
        // one = succ zero
        let one = succ(zero.clone());
        // two = succ one
        let two = succ(one.clone());

        // add : Nat -> Nat -> Nat
        // add n m = Nat.rec (\_ . Nat -> Nat) (\m. m) (\n ih m. succ (ih m)) n m
        // Motive: \_ . Nat -> Nat
        let motive = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])),
            Term::pi(
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                BinderInfo::Default
            ),
            BinderInfo::Default
        );
        
        // Base: \m. m
        let base = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])),
            Term::var(0),
            BinderInfo::Default
        );
        
        // Step: \n ih m. succ (ih m)
        // Var(0) = m
        // Var(1) = ih
        // Var(2) = n
        let step = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])), // n
            Term::lam(
                Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Rc::new(Term::Ind("Nat".to_string(), vec![])), BinderInfo::Default), // ih: Nat -> Nat
                Term::lam(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])), // m
                    succ(Term::app(Term::var(1), Term::var(0))),
                    BinderInfo::Default
                ),
                BinderInfo::Default
            ),
            BinderInfo::Default
        );

        // Term: add one one
        let recursor = Rc::new(Term::Rec("Nat".to_string(), vec![]));
        // Rec params(0) motive base step major
        let add_one = Term::app(
            Term::app(
                Term::app(
                    Term::app(recursor, motive),
                    base
                ),
                step
            ),
            one.clone()
        );
        
        let result = Term::app(add_one, one.clone());
        
        // Check result == two
        assert!(is_def_eq(result, two, &env));
    }
    #[test]
    fn test_recursion_detection() {
        // Unit test for is_recursive_head logic
        let tree_name = "Tree";
        
        // 1. Direct recursion: Tree
        let direct = Rc::new(Term::Ind(tree_name.to_string(), vec![]));
        assert!(is_recursive_head(&direct, tree_name));
        
        // 2. Indexed recursion: Tree a b
        let indexed = Term::app(Term::app(direct.clone(), Term::var(0)), Term::var(1));
        assert!(is_recursive_head(&indexed, tree_name));
        
        // 3. Nested recursion: List Tree
        // Should be FALSE (handled by map, not primitive rec)
        let list = Rc::new(Term::Ind("List".to_string(), vec![]));
        let nested = Term::app(list, direct.clone());
        assert!(!is_recursive_head(&nested, tree_name), "Nested type (List Tree) should not be marked recursive for primitive Rec");
        
        // 4. Infinitary recursion: Nat -> Tree
        // Should be FALSE (handled by manual args, not standard Rec without indices)
        // (Actually, strictly positive types DO allow this, but our Rec implementation doesn't support the IH for it yet)
        let func = Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), direct.clone(), BinderInfo::Default);
        assert!(!is_recursive_head(&func, tree_name), "Infinitary type (Nat -> Tree) should not be marked recursive for primitive Rec");
    }

    #[test]
    fn test_eq_elimination() {
        let mut env = Env::new();
        
        let eq_decl = crate::ast::InductiveDecl {
            name: "Eq".to_string(),
            univ_params: vec!["u".to_string()],
            ty: Term::pi(
                Rc::new(Term::Sort(Level::Param("u".to_string()))), // A
                Term::pi(
                    Rc::new(Term::Var(0)), // a:A
                    Term::pi(
                        Rc::new(Term::Var(1)), // b:A
                        Term::sort(Level::Param("u".to_string())),
                        BinderInfo::Default
                    ),
                    BinderInfo::Default
                ),
                BinderInfo::Default
            ),
            ctors: vec![
                crate::ast::Constructor {
                    name: "refl".to_string(),
                    ty: Term::app(
                        Term::app(
                            Term::app(Rc::new(Term::Ind("Eq".to_string(), vec![Level::Param("u".to_string())])), Term::var(1)), // Eq A
                            Term::var(0) // a
                        ),
                        Term::var(0) // a (as index)
                    )
                }
            ],
            num_params: 2, // A, a
            is_copy: false,
        };
        env.add_inductive(eq_decl).unwrap();
        
        let u = Level::Zero;
        let recursor = Rc::new(Term::Rec("Eq".to_string(), vec![u.clone()]));
        
        let typ_a = Term::sort(Level::Zero);
        let val_a = Rc::new(Term::Const("a".to_string(), vec![]));
        
        // Motive P: \b. \p. Sort 0
        let motive = Term::lam(
            typ_a.clone(), // b
            Term::lam(
                Term::app(Term::app(Term::app(Rc::new(Term::Ind("Eq".to_string(), vec![u.clone()])), typ_a.clone()), val_a.clone()), Term::var(1)),
                Term::sort(Level::Zero),
                BinderInfo::Default
            ),
            BinderInfo::Default
        );
        
        let base = Rc::new(Term::Const("base".to_string(), vec![]));
        let index_val = val_a.clone();
        
        let refl_term = Rc::new(Term::Ctor("Eq".to_string(), 0, vec![u.clone()]));
        let major = Term::app(Term::app(refl_term, typ_a.clone()), val_a.clone());

        // rec A a P base b major
        let app = Term::app(
            Term::app(
               Term::app(
                   Term::app(
                       Term::app(
                           Term::app(recursor, typ_a.clone()), // A
                           val_a.clone() // a
                       ),
                       motive
                   ),
                   base.clone()
               ),
               index_val // index b (= a)
            ),
            major // major (refl)
        );
        
        let val = eval(&app, &vec![], &env);
        let quoted = quote(val, 0, &env);
        
        assert!(is_def_eq(quoted, base, &env), "J-eliminator (Eq.rec) failed to reduce");
    }

    #[test]
    fn test_universe_levels_nbe() {
        let env = Env::new();
        // Sort u
        let u = Level::Param("u".to_string());
        
        // This fails if Level::Param("u") != Level::Param("u")
        // Eval: Term::Sort(u) -> Value::Sort(u)
        let t = Term::Sort(u.clone());
        let val = eval(&Rc::new(t.clone()), &vec![], &env);
        
        match val {
            Value::Sort(l) => assert_eq!(l, u),
            _ => panic!("Expected Sort u"),
        }
        
        // DefEq: Sort u == Sort u
        assert!(is_def_eq(Rc::new(t.clone()), Rc::new(Term::Sort(u.clone())), &env));
        
        // DefEq: Sort u != Sort v
        let v = Level::Param("v".to_string());
        let t_v = Term::Sort(v);
        assert!(!is_def_eq(Rc::new(t_v), Rc::new(Term::Sort(u)), &env));
    }
    #[test]
    fn test_let_recursion_interaction() {
        let mut env = Env::new();
        // Nat definition (standard)
        let nat_decl = crate::ast::InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            ty: Term::sort(Level::Zero),
            ctors: vec![
                crate::ast::Constructor { name: "zero".to_string(), ty: Rc::new(Term::Ind("Nat".to_string(), vec![])) },
                crate::ast::Constructor { name: "succ".to_string(), ty: Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Rc::new(Term::Ind("Nat".to_string(), vec![])), BinderInfo::Default) }
            ],
            num_params: 0,
            is_copy: false,
        };
        env.add_inductive(nat_decl).unwrap();

        // Helpers
        let zero = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
        let succ = |t: Rc<Term>| Term::app(Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])), t);
        let one = succ(zero.clone());
        let two = succ(one.clone());
        let four = succ(succ(two.clone()));

        // add : Nat -> Nat -> Nat (from test_nat_add_recursion)
        let add = {
            let recursor = Rc::new(Term::Rec("Nat".to_string(), vec![]));
            let motive = Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Rc::new(Term::Ind("Nat".to_string(), vec![])), BinderInfo::Default), BinderInfo::Default);
            let base = Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), Term::var(0), BinderInfo::Default);
            let step = Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), Term::lam(Term::pi(Rc::new(Term::Ind("Nat".to_string(), vec![])), Rc::new(Term::Ind("Nat".to_string(), vec![])), BinderInfo::Default), Term::lam(Rc::new(Term::Ind("Nat".to_string(), vec![])), succ(Term::app(Term::var(1), Term::var(0))), BinderInfo::Default), BinderInfo::Default), BinderInfo::Default);
            
            // \n m. (Rec ... n) m
            Term::lam(
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                Term::lam(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    Term::app(
                        Term::app(
                            Term::app(
                                Term::app(
                                    Term::app(recursor, motive), 
                                    base
                                ), 
                                step
                            ), 
                            Term::var(1) // n (outer arg)
                        ),
                        Term::var(0) // m (inner arg) THIS WAS MISSING
                    ),
                    BinderInfo::Default
                ),
                BinderInfo::Default
            )
        };
        
        // Let x = two in add x x
        // add x x -> add two two -> four
        // Term: Let(x:Nat, two, App(App(add, x), x))
        // In body: x is Var(0).
        // add is lifted? No, add is constructed term.
        
        // We need to apply `add` to `Var(0)` and `Var(0)`.
        // `add` takes 2 args.
        // `add` term defined above is `\n \m ...`.
        // So `App(App(add, Var(0)), Var(0))`
        
        let let_expr = Term::LetE(
            Rc::new(Term::Ind("Nat".to_string(), vec![])), // Type
            two.clone(), // Value
            Term::app(
                 Term::app(add.clone(), Term::var(0)),
                 Term::var(0)
            ) // Body
        );
        
        let val = eval(&Rc::new(let_expr), &vec![], &env);
        let quoted = quote(val, 0, &env);
        
        if !is_def_eq(quoted.clone(), four.clone(), &env) {
            panic!("Let binding + Recursion failed. Expected: {:?}\nGot: {:?}", four, quoted);
        }
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    // Semantic values
    Lam(String, BinderInfo, Closure),
    Pi(String, BinderInfo, Box<Value>, Closure),
    Sort(Level),
    Ind(String, Vec<Level>, Vec<Value>), // Inductive type with applied arguments (e.g., List Nat)
    Ctor(String, usize, Vec<Level>, Vec<Value>), // Constructor with arguments
    Rec(String, Vec<Level>), // Recursor constant

    // Stuck terms (Neutral)
    Neutral(Box<Neutral>, Vec<Value>), // Head + Spine
}

#[derive(Debug, Clone, PartialEq)]
pub enum Neutral {
    Var(usize), // De Bruijn LEVEL (absolute index)
    FreeVar(usize), // Free variable with original de Bruijn INDEX (for open terms)
    Const(String, Vec<Level>), // Opaque constant
    Rec(String, Vec<Level>), // Stuck recursor
}

#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub env: Vec<Value>,
    pub term: Rc<Term>,
}

impl Value {
    pub fn var(level: usize) -> Self {
        Value::Neutral(Box::new(Neutral::Var(level)), vec![])
    }
}

/// Evaluation Environment (Values for bound variables)
pub type EvalEnv = Vec<Value>;

/// Evaluate a term to a value
pub fn eval(t: &Rc<Term>, env: &EvalEnv, global_env: &Env) -> Value {
    match &**t {
        Term::Var(idx) => {
            // De Bruijn Index -> Value from Environment
            // env is handled as a stack: bound var 0 is at the end
            // env[env.len() - 1 - idx]
            if let Some(val) = env.iter().rev().nth(*idx) {
                val.clone()
            } else {
                // Free variable in an open term - create a neutral
                // This allows normalization of terms with free variables
                // (e.g., when whnf is called with an empty environment)
                Value::Neutral(Box::new(Neutral::FreeVar(*idx)), vec![])
            }
        }
        Term::Sort(l) => Value::Sort(l.clone()),
        Term::Const(n, ls) => {
             // TODO: Check transparency/unfolding here
             if let Some(def) = global_env.get_definition(n) {
                 if def.is_total() && def.value.is_some() {
                     // Always unfold total definitions for now (simple consistency)
                     // Optimization: Use transparency flag
                     // For now: Always expand definitions
                     eval(def.value.as_ref().unwrap(), &vec![], global_env)
                 } else {
                     Value::Neutral(Box::new(Neutral::Const(n.clone(), ls.clone())), vec![])
                 }
             } else {
                 Value::Neutral(Box::new(Neutral::Const(n.clone(), ls.clone())), vec![])
             }
        }
        Term::App(f, a) => {
            let f_val = eval(f, env, global_env);
            let a_val = eval(a, env, global_env);
            apply(f_val, a_val, global_env)
        }
        Term::Lam(_, body, info) => {
             // Type generic ignored in evaluation? Usually yes for untyped evaluation.
             // We store it if we wanted to reify types, but for equality checking,
             // only the body matters for computation.
             Value::Lam("x".to_string(), *info, Closure {
                 env: env.clone(),
                 term: body.clone()
             })
        }
        Term::Pi(ty, body, info) => {
             let dom = eval(ty, env, global_env);
             Value::Pi("x".to_string(), *info, Box::new(dom), Closure {
                 env: env.clone(),
                 term: body.clone()
             })
        }
        Term::LetE(_, val, body) => {
            let v = eval(val, env, global_env);
            let mut new_env = env.clone();
            new_env.push(v);
            eval(body, &new_env, global_env)
        }
        Term::Ind(n, ls) => Value::Ind(n.clone(), ls.clone(), vec![]),
        Term::Ctor(n, idx, ls) => Value::Ctor(n.clone(), *idx, ls.clone(), vec![]),
        Term::Rec(n, ls) => Value::Neutral(Box::new(Neutral::Rec(n.clone(), ls.clone())), vec![]),
        Term::Meta(m) => panic!("Metavariables should not be present in kernel evaluation"),
    }
}

pub fn apply(f: Value, a: Value, global_env: &Env) -> Value {
    match f {
        Value::Lam(_, _, closure) => {
            let mut new_env = closure.env.clone();
            new_env.push(a);
            eval(&closure.term, &new_env, global_env)
        }
        Value::Neutral(head, mut spine) => {
            spine.push(a);
            
            // Check for Iota reduction if head is Rec
            if let Neutral::Rec(ind_name, levels) = &*head {
                 // Try to reduce
                 if let Some(reduced) = try_reduce_rec(ind_name, levels, &spine, global_env) {
                     return reduced;
                 }
            }
            Value::Neutral(head, spine)
        }
        Value::Ctor(n, idx, ls, mut args) => {
            args.push(a);
            Value::Ctor(n, idx, ls, args)
        }
        Value::Ind(n, ls, mut args) => {
            // Type-level application: e.g., List Nat
            args.push(a);
            Value::Ind(n, ls, args)
        }
        _ => panic!("Application of non-function value: {:?}", f),
    }
}

/// Try to partially reduce a Rec application
fn try_reduce_rec(ind_name: &str, levels: &[Level], args: &[Value], global_env: &Env) -> Option<Value> {
    if let Some(decl) = global_env.get_inductive(ind_name) {
        let num_params = decl.num_params;
        let num_ctors = decl.ctors.len();
        let num_indices = count_indices(&decl.ty, num_params);
        
        let expected_len = num_params + 1 + num_ctors + num_indices + 1;
        
        if args.len() >= expected_len {
            let major_idx = num_params + 1 + num_ctors + num_indices;
            if let Some(major) = args.get(major_idx) {
                if let Value::Ctor(_, c_idx, _, c_args) = major {
                    // IOTA REDUCTION
                    if *c_idx < num_ctors {
                         let minor_idx = num_params + 1 + *c_idx;
                         let minor = &args[minor_idx];
                         
                         let mut res = minor.clone();
                         
                         // Determine which args are recursive
                         let ctor_ty = &decl.ctors[*c_idx].ty;
                         let recursive_map = extract_ctor_args(ctor_ty, ind_name);

                         // c_args includes params.
                         // We iterate from num_params to end.
                         for i in num_params..c_args.len() {
                              let field_val = c_args[i].clone();
                              res = apply(res, field_val.clone(), global_env);
                              
                              // Check if recursive
                              if i < recursive_map.len() && recursive_map[i] {
                                  // Construct IH
                                  // Rec(params, motive, minors, indices, field_val)
                                  let mut ih_args = Vec::new();
                                  // Params
                                  if num_params > 0 {
                                      ih_args.extend_from_slice(&args[0..num_params]);
                                  }
                                  // Motive
                                  ih_args.push(args[num_params].clone());
                                  // Minors
                                  if num_ctors > 0 {
                                      ih_args.extend_from_slice(&args[num_params+1 .. num_params+1+num_ctors]);
                                  }
                                  // Indices?
                                  // We need indices for the recursive call.
                                  // The indices come from the FIELD's type.
                                  // But `Value::Rec` stores them?
                                  // If `field` is `Vec A m`, then `m` is index.
                                  // Handling this requires inspecting `field` type or value.
                                  // For simple types `Nat`, proper indices are empty.
                                  // For `Vec`, `tail` has index `n`.
                                  // If we don't pass correct indices, type checking fails, but reduction?
                                  // NbE is untyped reduction.
                                  // But we need to push SOMETHING for indices if the Rec expects them.
                                  // Wait, `Rec` expects `indices` + `major`.
                                  // Reducing `Rec` on `tail`. `tail` is major.
                                  // We must supply `tail_indices`.
                                  // Where do we get them? 
                                  // `extract_ctor_args` only gives bool.
                                  // We need `extract_recursive_indices`?
                                  // This is getting complicated for MVP.
                                  // HACK: For now, we reuse the OLD indices? NO, that's wrong (n vs succ n).
                                  // But if we just pass `major`, maybe it works if indices are ignored by runtime?
                                  // `args` must match length.
                                  // If we push WRONG indices, it might be fine for reduction logic if Logic doesn't read them.
                                  // `try_reduce_rec` DOES read indices count but not values (except for skipping).
                                  // So we can push `Value::Sort(Level::Zero)` as dummy indices?
                                  for _ in 0..num_indices {
                                      // DUMMY INDICES
                                      ih_args.push(Value::Sort(Level::Zero)); 
                                  }

                                  // Field val (new major)
                                  ih_args.push(field_val);
                                  
                                  let ih_val = Value::Neutral(
                                      Box::new(Neutral::Rec(ind_name.to_string(), levels.to_vec())), 
                                      ih_args
                                  );
                                  
                                  res = apply(res, ih_val, global_env);
                              }
                         }
                         
                         // Apply ANY extra arguments (if Rec was applied to more than needed)
                         for extra in &args[expected_len..] {
                             res = apply(res, extra.clone(), global_env);
                         }
                         return Some(res);
                    }
                }
            }
        }
    }
    None
}

fn count_indices(ty: &Rc<Term>, num_params: usize) -> usize {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(_, body, _) = &**current {
        count += 1;
        current = body;
    }
    if count >= num_params {
        count - num_params
    } else {
        0 // Should not happen for well-formed inductive
    }
}

// Helper: which arguments of constructor are recursive?
fn extract_ctor_args(ty: &Rc<Term>, ind_name: &str) -> Vec<bool> {
    let mut current = ty.clone();
    let mut res = Vec::new();
    while let Term::Pi(dom, body, _) = &*current {
         res.push(is_recursive_head(dom, ind_name));
         current = body.clone();
    }
    res
}

fn is_recursive_head(t: &Rc<Term>, name: &str) -> bool {
    match &**t {
        Term::Ind(n, _) => n == name,
        Term::App(f, _) => is_recursive_head(f, name), // Check head only
        Term::Pi(_, _, _) => false, // Infinitary not supported in primitive Rec yet
        _ => false
    }
}


// Old quote removed


pub fn quote(v: Value, level: usize, global_env: &Env) -> Rc<Term> {
    match v {
        Value::Neutral(head, spine) => {
            let mut t = match *head {
                Neutral::Var(l) => Rc::new(Term::Var(level - 1 - l)),
                Neutral::FreeVar(idx) => Rc::new(Term::Var(idx)), // Preserve original index for free vars
                Neutral::Const(n, ls) => Rc::new(Term::Const(n, ls)),
                Neutral::Rec(n, ls) => Rc::new(Term::Rec(n, ls)),
            };
            for arg in spine {
                t = Term::app(t, quote(arg, level, global_env));
            }
            t
        }
        Value::Lam(_, info, closure) => {
             let var = Value::var(level);
             let mut new_env = closure.env.clone();
             new_env.push(var);
             let body_val = eval(&closure.term, &new_env, global_env);
             Term::lam(Rc::new(Term::Sort(Level::Zero)), quote(body_val, level + 1, global_env), info) // Type erased in Value::Lam
        }
        Value::Pi(_, info, dom, closure) => {
             let dom_t = quote(*dom, level, global_env);
             let var = Value::var(level);
             let mut new_env = closure.env.clone();
             new_env.push(var);
             let body_val = eval(&closure.term, &new_env, global_env);
             Term::pi(dom_t, quote(body_val, level + 1, global_env), info)
        }
        Value::Sort(l) => Rc::new(Term::Sort(l)),
        Value::Ind(n, ls, args) => {
            let mut t = Rc::new(Term::Ind(n, ls));
            for arg in args {
                t = Term::app(t, quote(arg, level, global_env));
            }
            t
        }
        Value::Ctor(n, idx, ls, args) => {
             let mut t = Rc::new(Term::Ctor(n, idx, ls));
             for arg in args {
                 t = Term::app(t, quote(arg, level, global_env));
             }
             t
        }
        Value::Rec(n, ls) => Rc::new(Term::Rec(n, ls)),
    }
}

pub fn is_def_eq(t1: Rc<Term>, t2: Rc<Term>, global_env: &Env) -> bool {
    let v1 = eval(&t1, &vec![], global_env);
    let v2 = eval(&t2, &vec![], global_env);
    
    check_eq(v1, v2, 0, global_env)
}

fn check_eq(v1: Value, v2: Value, level: usize, global_env: &Env) -> bool {
    // Optimization: Physical equality check? 
    // NbE values can be complex, physical equality hard.
    
    match (v1, v2) {
        (Value::Lam(_, _, cls1), Value::Lam(_, _, cls2)) => {
            // Recurse with fresh var
            let var = Value::var(level);
            let mut env1 = cls1.env.clone(); env1.push(var.clone());
            let mut env2 = cls2.env.clone(); env2.push(var);
            let body1 = eval(&cls1.term, &env1, global_env);
            let body2 = eval(&cls2.term, &env2, global_env);
            check_eq(body1, body2, level + 1, global_env)
        }
        (Value::Lam(_, _, cls), other) | (other, Value::Lam(_, _, cls)) => {
            // Eta expansion
            // \x. body == other
            // body[x] == other x
            let var = Value::var(level);
            let mut env = cls.env.clone(); env.push(var.clone());
            let body = eval(&cls.term, &env, global_env);
            let app = apply(other, var, global_env);
            check_eq(body, app, level + 1, global_env)
        }
        (Value::Pi(_, _, d1, cls1), Value::Pi(_, _, d2, cls2)) => {
            if !check_eq(*d1, *d2, level, global_env) { return false; }
            let var = Value::var(level);
            let mut env1 = cls1.env.clone(); env1.push(var.clone());
            let mut env2 = cls2.env.clone(); env2.push(var);
            let body1 = eval(&cls1.term, &env1, global_env);
            let body2 = eval(&cls2.term, &env2, global_env);
            check_eq(body1, body2, level + 1, global_env)
        }
        (Value::Sort(l1), Value::Sort(l2)) => l1 == l2,
        (Value::Ind(n1, ls1, a1), Value::Ind(n2, ls2, a2)) => {
            n1 == n2 && ls1 == ls2 && check_eq_vec(&a1, &a2, level, global_env)
        }
        (Value::Ctor(n1, i1, ls1, a1), Value::Ctor(n2, i2, ls2, a2)) => {
             n1 == n2 && i1 == i2 && ls1 == ls2 && check_eq_vec(&a1, &a2, level, global_env)
        }
        (Value::Rec(n1, ls1), Value::Rec(n2, ls2)) => n1 == n2 && ls1 == ls2,
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) => {
             check_neutral_head(&*h1, &*h2) && check_eq_vec(&s1, &s2, level, global_env)
        }
        _ => false,
    }
}

fn check_neutral_head(h1: &Neutral, h2: &Neutral) -> bool {
    match (h1, h2) {
        (Neutral::Var(i1), Neutral::Var(i2)) => i1 == i2,
        (Neutral::FreeVar(i1), Neutral::FreeVar(i2)) => i1 == i2,
        (Neutral::Const(n1, ls1), Neutral::Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
        (Neutral::Rec(n1, ls1), Neutral::Rec(n2, ls2)) => n1 == n2 && ls1 == ls2,
        _ => false
    }
}

fn check_eq_vec(bs1: &[Value], bs2: &[Value], level: usize, global_env: &Env) -> bool {
    if bs1.len() != bs2.len() { return false; }
    for (b1, b2) in bs1.iter().zip(bs2.iter()) {
        if !check_eq(b1.clone(), b2.clone(), level, global_env) {
            return false;
        }
    }
    true
}
