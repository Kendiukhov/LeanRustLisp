use crate::ast::{level_eq, levels_eq, BinderInfo, FunctionKind, Level, Term, Transparency};
use crate::checker::Env;
use std::collections::HashMap;
use std::rc::Rc;
#[cfg(any(test, feature = "test-support"))]
use std::sync::Mutex;
use std::sync::OnceLock;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Definition;

    fn test_env() -> Env {
        let mut env = Env::new();
        env.set_allow_reserved_primitives(true);
        env
    }

    fn eval(t: &Rc<Term>, env: &EvalEnv, global_env: &Env, transparency: Transparency) -> Value {
        super::eval(t, env, global_env, transparency).expect("nbe eval failed")
    }

    fn quote(v: Value, level: usize, global_env: &Env, transparency: Transparency) -> Rc<Term> {
        super::quote(v, level, global_env, transparency).expect("nbe quote failed")
    }

    fn apply(f: Value, a: Value, global_env: &Env, transparency: Transparency) -> Value {
        super::apply(f, a, global_env, transparency).expect("nbe apply failed")
    }

    #[test]
    fn test_eval_id() {
        // \x. x
        let id = Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default);
        let env = test_env();

        let val = eval(&id, &vec![], &env, Transparency::All);
        if let Value::Lam(_, _, _, _, _) = val {
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

        let env = test_env();
        let val = eval(&app, &vec![], &env, Transparency::All);

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
        let mut env = test_env();
        let prop = Term::sort(Level::Zero);

        // Register opaque constants used in the definition.
        let zero_ty = prop.clone();
        let succ_ty = Term::pi(prop.clone(), prop.clone(), BinderInfo::Default);
        env.add_definition(Definition::axiom("zero".to_string(), zero_ty))
            .expect("Failed to add zero axiom");
        env.add_definition(Definition::axiom("succ".to_string(), succ_ty))
            .expect("Failed to add succ axiom");

        // def one = succ zero
        let one_tm = Term::app(
            Rc::new(Term::Const("succ".to_string(), vec![])),
            Rc::new(Term::Const("zero".to_string(), vec![])),
        );

        let mut def = Definition::total("one".to_string(), Term::sort(Level::Zero), one_tm.clone());
        def.noncomputable = true;
        env.add_definition(def).unwrap();

        let t = Rc::new(Term::Const("one".to_string(), vec![]));
        let val = eval(&t, &vec![], &env, Transparency::All);

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
    fn test_eval_const_never_unfolds() {
        let mut env = test_env();
        let type0 = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let ty = Term::pi(
            type0.clone(),
            Term::pi(Term::var(0), Term::var(1), BinderInfo::Default),
            BinderInfo::Default,
        );
        let val = Term::lam(
            type0.clone(),
            Term::lam(Term::var(0), Term::var(0), BinderInfo::Default),
            BinderInfo::Default,
        );
        env.add_definition(Definition::total("eval".to_string(), ty, val))
            .expect("Failed to add eval definition");

        let term = Rc::new(Term::Const("eval".to_string(), vec![]));
        let val = eval(&term, &vec![], &env, Transparency::All);

        match val {
            Value::Neutral(head, spine) => {
                match *head {
                    Neutral::Const(name, _) => assert_eq!(name, "eval"),
                    _ => panic!("Expected eval to remain a neutral const"),
                }
                assert!(spine.is_empty());
            }
            _ => panic!("Expected eval to remain opaque during NBE"),
        }
    }

    #[test]
    fn test_defeq_beta() {
        let env = test_env();
        // (\x. x) y
        let t1 = Term::app(
            Term::lam(Term::sort(Level::Zero), Term::var(0), BinderInfo::Default),
            Rc::new(Term::Const("y".to_string(), vec![])),
        );
        // y
        let t2 = Rc::new(Term::Const("y".to_string(), vec![]));

        assert!(is_def_eq(t1, t2, &env, Transparency::All));
    }

    #[test]
    fn test_eta_equality() {
        let env = test_env();
        // f = \x. f x ?
        // We test (\x. f x) == f
        let f = Rc::new(Term::Const("f".to_string(), vec![]));

        let eta = Term::lam(
            Term::sort(Level::Zero),
            Term::app(f.clone(), Term::var(0)),
            BinderInfo::Default,
        );
        assert!(
            is_def_eq(eta, f, &env, Transparency::All),
            "Eta reduction failed"
        );
    }

    #[test]
    fn test_deep_application() {
        let env = test_env();
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

        let val = eval(&term, &vec![], &env, Transparency::All);
        let quoted = quote(val, 0, &env, Transparency::All);

        if let Term::Const(n, _) = &*quoted {
            assert_eq!(n, "c");
        } else {
            panic!("Deep application failed: {:?}", quoted);
        }
    }

    #[test]
    fn test_vec_indices() {
        let mut env = test_env();
        // Vec A n

        let nat = crate::ast::InductiveDecl {
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
                        BinderInfo::Default,
                    ),
                },
            ],
            num_params: 0,
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(nat).unwrap();

        let vec_decl = crate::ast::InductiveDecl {
            name: "Vec".to_string(),
            univ_params: vec![],
            // Pi(A:Type) -> Pi(n:Nat) -> Type
            ty: Term::pi(
                Rc::new(Term::Sort(Level::Zero)),
                Term::pi(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    Term::sort(Level::Zero),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            ctors: vec![crate::ast::Constructor {
                name: "nil".to_string(),
                ty: Term::pi(
                    Rc::new(Term::Sort(Level::Zero)), // A
                    Term::app(
                        Term::app(Rc::new(Term::Ind("Vec".to_string(), vec![])), Term::var(0)),
                        Rc::new(Term::Ctor("Nat".to_string(), 0, vec![])),
                    ),
                    BinderInfo::Default,
                ),
            }],
            num_params: 1, // A
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(vec_decl).unwrap();

        let a = Term::sort(Level::Zero);
        let recursor = Rc::new(Term::Rec("Vec".to_string(), vec![Level::Zero]));
        let motive = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])), // index
            Term::lam(
                Term::app(Rc::new(Term::Ind("Vec".to_string(), vec![])), Term::var(0)), // val
                Term::sort(Level::Zero),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );

        let base = Rc::new(Term::Const("base".to_string(), vec![]));
        let zero = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
        let nil = Rc::new(Term::Ctor("Vec".to_string(), 0, vec![]));

        let nil_app = Term::app(nil, a.clone());

        // rec A P base zero (nil A)
        let app = Term::app(
            Term::app(
                Term::app(Term::app(Term::app(recursor, a), motive), base.clone()),
                zero,
            ),
            nil_app,
        );

        let val = eval(&app, &vec![], &env, Transparency::All);
        let quoted = quote(val, 0, &env, Transparency::All);
        assert!(
            is_def_eq(quoted, base, &env, Transparency::All),
            "Vec.rec did not reduce to base"
        );
    }
    #[test]
    fn test_shadowing() {
        let env = test_env();
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
        let val = eval(&term, &vec![], &env, Transparency::All);
        let quoted = quote(val, 0, &env, Transparency::All);

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
        let mut env = test_env();
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
                        BinderInfo::Default,
                    ),
                },
            ],
            num_params: 0,
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(nat_decl).unwrap();

        // Constants
        let zero = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
        let succ = |t: Rc<Term>| Term::app(Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])), t);
        let one = succ(zero.clone());

        let motive = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])),
            Term::pi(
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let base = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])),
            Term::var(0),
            BinderInfo::Default,
        );
        let step = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])),
            Term::lam(
                Term::pi(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    BinderInfo::Default,
                ),
                Term::lam(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    succ(Term::app(Term::var(1), Term::var(0))),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );

        let recursor = Rc::new(Term::Rec("Nat".to_string(), vec![Level::Zero]));
        let add_one = Term::app(
            Term::app(Term::app(Term::app(recursor, motive), base), step),
            one.clone(),
        );

        // Evaluate add_one
        let val = eval(&add_one, &vec![], &env, Transparency::All);
        // Should be a Lambda waiting for m
        match val {
            Value::Lam(_, _, _, _, _) | Value::Pi(_, _, _, _, _) => {} // OK
            _ => panic!("Expected function from partial application, got {:?}", val),
        }

        // Now apply it to one
        let one_val = eval(&one, &vec![], &env, Transparency::All);
        let res = apply(val, one_val, &env, Transparency::All);
        let quoted = quote(res, 0, &env, Transparency::All);

        let two = succ(one.clone());
        assert!(is_def_eq(quoted, two, &env, Transparency::All));
    }

    #[test]
    fn test_defeq_rejects_fix_unfold() {
        let env = test_env();
        let ty = Term::sort(Level::Zero);
        let body = Term::var(0);
        let fix = Rc::new(Term::Fix(ty, body));
        let arg = Rc::new(Term::Const("a".to_string(), vec![]));
        let app = Term::app(fix, arg);

        match is_def_eq_result(app.clone(), app, &env, Transparency::All, 10) {
            Err(NbeError::FixUnfoldDisallowed) => {}
            other => panic!("Expected FixUnfoldDisallowed, got {:?}", other),
        }
    }
    #[test]
    fn test_nat_add_recursion() {
        let mut env = test_env();
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
                        BinderInfo::Default,
                    ), // Nat -> Nat
                },
            ],
            num_params: 0,
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
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
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );

        // Base: \m. m
        let base = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])),
            Term::var(0),
            BinderInfo::Default,
        );

        // Step: \n ih m. succ (ih m)
        let step = Term::lam(
            Rc::new(Term::Ind("Nat".to_string(), vec![])), // n
            Term::lam(
                Term::pi(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    BinderInfo::Default,
                ), // ih: Nat -> Nat
                Term::lam(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])), // m
                    succ(Term::app(Term::var(1), Term::var(0))),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );

        // Term: add one one
        let recursor = Rc::new(Term::Rec("Nat".to_string(), vec![Level::Zero]));
        // Rec params(0) motive base step major
        let add_one = Term::app(
            Term::app(Term::app(Term::app(recursor, motive), base), step),
            one.clone(),
        );

        let result = Term::app(add_one, one.clone());

        // Check result == two
        assert!(is_def_eq(result, two, &env, Transparency::All));
    }
    #[test]
    fn test_recursion_detection() {
        // Unit test for is_recursive_head logic
        fn is_recursive_head_local(t: &Rc<Term>, name: &str) -> bool {
            match &**t {
                Term::Ind(n, _) => n == name,
                Term::App(f, _, _) => is_recursive_head_local(f, name), // Check head only
                Term::Pi(_, _, _, _) => false, // Infinitary not supported in primitive Rec yet
                _ => false,
            }
        }

        let tree_name = "Tree";

        // 1. Direct recursion: Tree
        let direct = Rc::new(Term::Ind(tree_name.to_string(), vec![]));
        assert!(is_recursive_head_local(&direct, tree_name));

        // 2. Indexed recursion: Tree a b
        let indexed = Term::app(Term::app(direct.clone(), Term::var(0)), Term::var(1));
        assert!(is_recursive_head_local(&indexed, tree_name));

        // 3. Nested recursion: List Tree
        let list = Rc::new(Term::Ind("List".to_string(), vec![]));
        let nested = Term::app(list, direct.clone());
        assert!(
            !is_recursive_head_local(&nested, tree_name),
            "Nested type (List Tree) should not be marked recursive for primitive Rec"
        );

        // 4. Infinitary recursion: Nat -> Tree
        let func = Term::pi(
            Rc::new(Term::Ind("Nat".to_string(), vec![])),
            direct.clone(),
            BinderInfo::Default,
        );
        assert!(
            !is_recursive_head_local(&func, tree_name),
            "Infinitary type (Nat -> Tree) should not be marked recursive for primitive Rec"
        );
    }

    #[test]
    fn test_indexed_recursor_iota_uses_field_indices() {
        let mut env = test_env();

        // Nat : Type
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
                        BinderInfo::Default,
                    ),
                },
            ],
            num_params: 0,
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(nat_decl).unwrap();

        let nat_ref = Rc::new(Term::Ind("Nat".to_string(), vec![]));
        let vec_ref = Rc::new(Term::Ind("Vec".to_string(), vec![]));

        // Vec : (A : Type) -> (n : Nat) -> Type
        let vec_ty = Term::pi(
            Term::sort(Level::Zero),
            Term::pi(
                nat_ref.clone(),
                Term::sort(Level::Zero),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );

        // nil : (A : Type) -> Vec A zero
        let nil_ty = Term::pi(
            Term::sort(Level::Zero),
            Term::app(
                Term::app(vec_ref.clone(), Term::var(0)),
                Rc::new(Term::Ctor("Nat".to_string(), 0, vec![])),
            ),
            BinderInfo::Default,
        );

        // cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (succ n)
        let cons_ty = Term::pi(
            Term::sort(Level::Zero), // A
            Term::pi(
                nat_ref.clone(), // n
                Term::pi(
                    Term::var(1), // A
                    Term::pi(
                        Term::app(
                            Term::app(vec_ref.clone(), Term::var(2)), // Vec A
                            Term::var(1),                             // n
                        ),
                        Term::app(
                            Term::app(vec_ref.clone(), Term::var(3)), // Vec A
                            Term::app(
                                Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])),
                                Term::var(2),
                            ), // succ n
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );

        let vec_decl = crate::ast::InductiveDecl {
            name: "Vec".to_string(),
            univ_params: vec![],
            ty: vec_ty,
            ctors: vec![
                crate::ast::Constructor {
                    name: "nil".to_string(),
                    ty: nil_ty,
                },
                crate::ast::Constructor {
                    name: "cons".to_string(),
                    ty: cons_ty,
                },
            ],
            num_params: 1,
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };
        env.add_inductive(vec_decl).unwrap();

        // Free variables in outer context: [A, n, x, xs] (xs is Var 0)
        let a = Term::var(3);
        let n = Term::var(2);
        let x = Term::var(1);
        let xs = Term::var(0);

        let recursor = Rc::new(Term::Rec("Vec".to_string(), vec![Level::Zero]));
        let motive = Term::lam(
            nat_ref.clone(),
            Term::lam(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default),
            BinderInfo::Default,
        );

        let minor_nil = Rc::new(Term::Const("base".to_string(), vec![]));
        let minor_cons = Term::lam(
            nat_ref.clone(),
            Term::lam(
                nat_ref.clone(),
                Term::lam(
                    nat_ref.clone(),
                    Term::lam(nat_ref.clone(), Term::var(0), BinderInfo::Default),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );

        let cons = Rc::new(Term::Ctor("Vec".to_string(), 1, vec![]));
        let cons_app = Term::app(
            Term::app(Term::app(Term::app(cons, a.clone()), n.clone()), x.clone()),
            xs.clone(),
        );
        let succ_n = Term::app(Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])), n.clone());

        // rec A motive nil cons (succ n) (cons A n x xs)
        let rec_app = Term::app(
            Term::app(
                Term::app(
                    Term::app(
                        Term::app(Term::app(recursor.clone(), a.clone()), motive.clone()),
                        minor_nil.clone(),
                    ),
                    minor_cons.clone(),
                ),
                succ_n,
            ),
            cons_app,
        );

        // Expected: IH = rec A motive nil cons n xs
        let ih_expected = Term::app(
            Term::app(
                Term::app(
                    Term::app(Term::app(Term::app(recursor, a.clone()), motive), minor_nil),
                    minor_cons,
                ),
                n.clone(),
            ),
            xs.clone(),
        );

        assert!(
            is_def_eq(rec_app, ih_expected, &env, Transparency::All),
            "Indexed recursor should use field indices for IH"
        );
    }

    #[test]
    fn test_eq_elimination() {
        let mut env = test_env();

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
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            ctors: vec![crate::ast::Constructor {
                name: "refl".to_string(),
                ty: Term::pi(
                    Rc::new(Term::Sort(Level::Param("u".to_string()))), // A
                    Term::pi(
                        Rc::new(Term::Var(0)), // a:A
                        Term::app(
                            Term::app(
                                Term::app(
                                    Rc::new(Term::Ind(
                                        "Eq".to_string(),
                                        vec![Level::Param("u".to_string())],
                                    )),
                                    Term::var(1),
                                ),
                                Term::var(0),
                            ),
                            Term::var(0),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            }],
            num_params: 2, // A, a
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
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
                Term::app(
                    Term::app(
                        Term::app(
                            Rc::new(Term::Ind("Eq".to_string(), vec![u.clone()])),
                            typ_a.clone(),
                        ),
                        val_a.clone(),
                    ),
                    Term::var(1),
                ),
                Term::sort(Level::Zero),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
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
                            val_a.clone(),                      // a
                        ),
                        motive,
                    ),
                    base.clone(),
                ),
                index_val, // index b (= a)
            ),
            major, // major (refl)
        );

        let val = eval(&app, &vec![], &env, Transparency::All);
        let quoted = quote(val, 0, &env, Transparency::All);

        assert!(
            is_def_eq(quoted, base, &env, Transparency::All),
            "J-eliminator (Eq.rec) failed to reduce"
        );
    }

    #[test]
    fn test_universe_levels_nbe() {
        let env = test_env();
        // Sort u
        let u = Level::Param("u".to_string());

        // This fails if Level::Param("u") != Level::Param("u")
        // Eval: Term::Sort(u) -> Value::Sort(u)
        let t = Term::Sort(u.clone());
        let val = eval(&Rc::new(t.clone()), &vec![], &env, Transparency::All);

        match val {
            Value::Sort(l) => assert_eq!(l, u),
            _ => panic!("Expected Sort u"),
        }

        // DefEq: Sort u == Sort u
        assert!(is_def_eq(
            Rc::new(t.clone()),
            Rc::new(Term::Sort(u.clone())),
            &env,
            Transparency::All
        ));

        // DefEq: Sort u != Sort v
        let v = Level::Param("v".to_string());
        let t_v = Term::Sort(v);
        assert!(!is_def_eq(
            Rc::new(t_v),
            Rc::new(Term::Sort(u)),
            &env,
            Transparency::All
        ));
    }
    #[test]
    fn test_let_recursion_interaction() {
        let mut env = test_env();
        // Nat definition (standard)
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
                        BinderInfo::Default,
                    ),
                },
            ],
            num_params: 0,
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
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
            let recursor = Rc::new(Term::Rec("Nat".to_string(), vec![Level::Zero]));
            let motive = Term::lam(
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                Term::pi(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            );
            let base = Term::lam(
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                Term::var(0),
                BinderInfo::Default,
            );
            let step = Term::lam(
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                Term::lam(
                    Term::pi(
                        Rc::new(Term::Ind("Nat".to_string(), vec![])),
                        Rc::new(Term::Ind("Nat".to_string(), vec![])),
                        BinderInfo::Default,
                    ),
                    Term::lam(
                        Rc::new(Term::Ind("Nat".to_string(), vec![])),
                        succ(Term::app(Term::var(1), Term::var(0))),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            );

            // \n m. (Rec ... n) m
            Term::lam(
                Rc::new(Term::Ind("Nat".to_string(), vec![])),
                Term::lam(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    Term::app(
                        Term::app(
                            Term::app(Term::app(Term::app(recursor, motive), base), step),
                            Term::var(1), // n (outer arg)
                        ),
                        Term::var(0), // m (inner arg) THIS WAS MISSING
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            )
        };

        let let_expr = Term::LetE(
            Rc::new(Term::Ind("Nat".to_string(), vec![])), // Type
            two.clone(),                                   // Value
            Term::app(Term::app(add.clone(), Term::var(0)), Term::var(0)), // Body
        );

        let val = eval(&Rc::new(let_expr), &vec![], &env, Transparency::All);
        let quoted = quote(val, 0, &env, Transparency::All);

        if !is_def_eq(quoted.clone(), four.clone(), &env, Transparency::All) {
            panic!(
                "Let binding + Recursion failed. Expected: {:?}\nGot: {:?}",
                four, quoted
            );
        }
    }

    #[test]
    fn test_fix_eval() {
        // fix f. \x. x
        // Type: Nat -> Nat
        let nat = Rc::new(Term::Ind("Nat".to_string(), vec![]));
        let ty = Term::pi(nat.clone(), nat.clone(), BinderInfo::Default);

        let body = Term::lam(nat.clone(), Term::var(0), BinderInfo::Default); // \x. x (ignores f at Var(1))

        let fix_term = Rc::new(Term::Fix(ty.clone(), body));

        let env = test_env();
        // eval
        let val = eval(&fix_term, &vec![], &env, Transparency::All);

        // check value structure
        match val {
            Value::Fix(_, _) => {}
            _ => panic!("Expected Value::Fix, got {:?}", val),
        }

        // apply to argument
        let zero = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
        let zero_val = eval(&zero, &vec![], &env, Transparency::All);

        let res = apply(val, zero_val, &env, Transparency::All);
        let quoted = quote(res, 0, &env, Transparency::All);

        // Should be zero
        if let Term::Ctor(n, i, _) = &*quoted {
            assert_eq!(n, "Nat");
            assert_eq!(*i, 0);
        } else {
            panic!("Expected Nat.zero, got {:?}", quoted);
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpineItem {
    pub arg: Value,
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    // Semantic values
    Lam(String, BinderInfo, FunctionKind, Box<Value>, Closure),
    Pi(String, BinderInfo, FunctionKind, Box<Value>, Closure),
    Sort(Level),
    Ind(String, Vec<Level>, Vec<Value>), // Inductive type with applied arguments (e.g., List Nat)
    Ctor(String, usize, Vec<Level>, Vec<Value>), // Constructor with arguments
    Rec(String, Vec<Level>),             // Recursor constant
    Fix(Box<Value>, Closure),            // Fixpoint value

    // Stuck terms (Neutral)
    Neutral(Box<Neutral>, Vec<SpineItem>), // Head + Spine
}

#[derive(Debug, Clone, PartialEq)]
pub enum Neutral {
    Var(usize),                // De Bruijn LEVEL (absolute index)
    FreeVar(usize),            // Free variable with original de Bruijn INDEX (for open terms)
    Const(String, Vec<Level>), // Opaque constant
    Rec(String, Vec<Level>),   // Stuck recursor
    Meta(usize),               // Unsolved metavariable (stuck during elaboration)
}

#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub env: Vec<Value>,
    pub term: Rc<Term>,
}

const MAX_FUEL_TRACE: usize = 4;

#[derive(Debug, Clone, PartialEq, Eq)]
enum FuelEvent {
    UnfoldConst(String),
    UnfoldFix,
    ReduceRecursor(String),
}

impl std::fmt::Display for FuelEvent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FuelEvent::UnfoldConst(name) => write!(f, "unfold const {}", name),
            FuelEvent::UnfoldFix => write!(f, "unfold fix"),
            FuelEvent::ReduceRecursor(ind_name) => write!(f, "reduce recursor {}", ind_name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FuelExhaustion {
    last_event: Option<FuelEvent>,
    recent_defs: Vec<String>,
}

impl FuelExhaustion {
    fn note_event(&mut self, event: FuelEvent) {
        if let FuelEvent::UnfoldConst(name) = &event {
            let should_push = self
                .recent_defs
                .last()
                .map(|last| last != name)
                .unwrap_or(true);
            if should_push {
                self.recent_defs.push(name.clone());
                if self.recent_defs.len() > MAX_FUEL_TRACE {
                    self.recent_defs.remove(0);
                }
            }
        }
        self.last_event = Some(event);
    }

    pub fn last_event_label(&self) -> Option<String> {
        self.last_event.as_ref().map(|event| event.to_string())
    }

    pub fn recent_definitions(&self) -> &[String] {
        &self.recent_defs
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NbeError {
    FuelExhausted(FuelExhaustion),
    FixUnfoldDisallowed,
    NonFunctionApplication,
}

const DEFAULT_DEF_EQ_FUEL: usize = 100_000;
#[cfg(any(test, feature = "test-support"))]
static DEF_EQ_FUEL_OVERRIDE: OnceLock<Mutex<Option<DefEqFuelPolicy>>> = OnceLock::new();
#[cfg(not(any(test, feature = "test-support")))]
static DEF_EQ_FUEL_OVERRIDE: OnceLock<DefEqFuelPolicy> = OnceLock::new();

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefEqFuelSource {
    Override,
    Env,
    Default,
}

impl DefEqFuelSource {
    pub fn label(self) -> &'static str {
        match self {
            DefEqFuelSource::Override => "override",
            DefEqFuelSource::Env => "LRL_DEFEQ_FUEL",
            DefEqFuelSource::Default => "default",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefEqFuelPolicy {
    pub fuel: usize,
    pub source: DefEqFuelSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefEqFuelOverrideError {
    ZeroFuel,
    AlreadySet,
}

/// Configure the definitional equality fuel policy for this process.
pub fn set_def_eq_fuel_policy(
    fuel: usize,
    source: DefEqFuelSource,
) -> Result<(), DefEqFuelOverrideError> {
    if fuel == 0 {
        return Err(DefEqFuelOverrideError::ZeroFuel);
    }
    let policy = DefEqFuelPolicy { fuel, source };
    #[cfg(any(test, feature = "test-support"))]
    {
        let lock = DEF_EQ_FUEL_OVERRIDE.get_or_init(|| Mutex::new(None));
        let mut guard = lock.lock().expect("defeq fuel override lock poisoned");
        if let Some(existing) = *guard {
            if existing == policy {
                return Ok(());
            }
            return Err(DefEqFuelOverrideError::AlreadySet);
        }
        *guard = Some(policy);
        return Ok(());
    }
    #[cfg(not(any(test, feature = "test-support")))]
    {
        return DEF_EQ_FUEL_OVERRIDE
            .set(policy)
            .map_err(|_| DefEqFuelOverrideError::AlreadySet);
    }
}

/// Override the default definitional equality fuel for this process.
pub fn set_def_eq_fuel_override(fuel: usize) -> Result<(), DefEqFuelOverrideError> {
    set_def_eq_fuel_policy(fuel, DefEqFuelSource::Override)
}

fn defeq_fuel_override() -> Option<DefEqFuelPolicy> {
    #[cfg(any(test, feature = "test-support"))]
    {
        let lock = DEF_EQ_FUEL_OVERRIDE.get_or_init(|| Mutex::new(None));
        let guard = lock.lock().expect("defeq fuel override lock poisoned");
        *guard
    }
    #[cfg(not(any(test, feature = "test-support")))]
    {
        DEF_EQ_FUEL_OVERRIDE.get().copied()
    }
}

/// Test-only: clear the cached defeq fuel policy so new configs can be applied.
#[cfg(any(test, feature = "test-support"))]
pub fn reset_defeq_fuel_cache_for_tests() {
    if let Some(lock) = DEF_EQ_FUEL_OVERRIDE.get() {
        let mut guard = lock.lock().expect("defeq fuel override lock poisoned");
        *guard = None;
    }
}

/// Return the defeq fuel policy (with source) for this process.
/// Precedence: configured policy (override/env) > built-in default.
pub fn defeq_fuel_policy() -> DefEqFuelPolicy {
    if let Some(policy) = defeq_fuel_override() {
        return policy;
    }
    DefEqFuelPolicy {
        fuel: DEFAULT_DEF_EQ_FUEL,
        source: DefEqFuelSource::Default,
    }
}

fn default_def_eq_fuel() -> usize {
    defeq_fuel_policy().fuel
}

pub fn default_eval_fuel() -> usize {
    default_def_eq_fuel()
}

#[derive(Debug, Clone)]
struct EvalConfig {
    fuel: Option<usize>,
    allow_fix_unfold: bool,
    fuel_exhaustion: FuelExhaustion,
}

impl EvalConfig {
    fn unlimited() -> Self {
        Self {
            fuel: None,
            allow_fix_unfold: true,
            fuel_exhaustion: FuelExhaustion::default(),
        }
    }

    fn with_fuel(fuel: usize) -> Self {
        Self {
            fuel: Some(fuel),
            allow_fix_unfold: true,
            fuel_exhaustion: FuelExhaustion::default(),
        }
    }

    fn with_fuel_for_defeq(fuel: usize) -> Self {
        Self {
            fuel: Some(fuel),
            allow_fix_unfold: false,
            fuel_exhaustion: FuelExhaustion::default(),
        }
    }

    fn tick(&mut self, event: FuelEvent) -> Result<(), NbeError> {
        match self.fuel.as_mut() {
            None => Ok(()),
            Some(remaining) => {
                self.fuel_exhaustion.note_event(event);
                if *remaining == 0 {
                    Err(NbeError::FuelExhausted(self.fuel_exhaustion.clone()))
                } else {
                    *remaining -= 1;
                    Ok(())
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CacheKey {
    term: Rc<Term>,
    transparency: Transparency,
    level: usize,
}

#[derive(Debug, Clone)]
pub struct DefEqConfig {
    transparency: Transparency,
    eval_config: EvalConfig,
    cache: HashMap<CacheKey, Value>,
}

impl DefEqConfig {
    pub fn new(transparency: Transparency, fuel: usize) -> Self {
        DefEqConfig {
            transparency,
            eval_config: EvalConfig::with_fuel_for_defeq(fuel),
            cache: HashMap::new(),
        }
    }

    fn cache_key(&self, term: &Rc<Term>, level: usize) -> CacheKey {
        CacheKey {
            term: term.clone(),
            transparency: self.transparency,
            level,
        }
    }
}

impl Value {
    pub fn var(level: usize) -> Self {
        Value::Neutral(Box::new(Neutral::Var(level)), vec![])
    }
}

/// Evaluation Environment (Values for bound variables)
pub type EvalEnv = Vec<Value>;

/// Evaluate a term to a value
pub fn eval(
    t: &Rc<Term>,
    env: &EvalEnv,
    global_env: &Env,
    transparency: Transparency,
) -> Result<Value, NbeError> {
    let mut config = EvalConfig::unlimited();
    eval_with_config(t, env, global_env, transparency, &mut config)
}

pub fn eval_with_fuel(
    t: &Rc<Term>,
    env: &EvalEnv,
    global_env: &Env,
    transparency: Transparency,
    fuel: usize,
) -> Result<Value, NbeError> {
    let mut config = EvalConfig::with_fuel(fuel);
    eval_with_config(t, env, global_env, transparency, &mut config)
}

fn eval_with_config(
    t: &Rc<Term>,
    env: &EvalEnv,
    global_env: &Env,
    transparency: Transparency,
    config: &mut EvalConfig,
) -> Result<Value, NbeError> {
    match &**t {
        Term::Var(idx) => {
            // De Bruijn Index -> Value from Environment
            // env is handled as a stack: bound var 0 is at the end
            // env[env.len() - 1 - idx]
            if let Some(val) = env.iter().rev().nth(*idx) {
                Ok(val.clone())
            } else {
                // Free variable in an open term - create a neutral
                Ok(Value::Neutral(Box::new(Neutral::FreeVar(*idx)), vec![]))
            }
        }
        Term::Sort(l) => Ok(Value::Sort(l.clone())),
        Term::Const(n, ls) => {
            if crate::checker::reserved_effect_totality(n).is_some() {
                return Ok(Value::Neutral(
                    Box::new(Neutral::Const(n.clone(), ls.clone())),
                    vec![],
                ));
            }
            if let Some(def) = global_env.get_definition(n) {
                // Check transparency
                let should_unfold = match transparency {
                    Transparency::All => true,
                    Transparency::Reducible => def.transparency != Transparency::None,
                    Transparency::Instances => def.transparency == Transparency::Instances, // Strict match or >=? Usually >=
                    Transparency::None => false,
                };

                if def.is_total() && def.value.is_some() && should_unfold {
                    config.tick(FuelEvent::UnfoldConst(n.clone()))?;
                    eval_with_config(
                        def.value.as_ref().unwrap(),
                        &vec![],
                        global_env,
                        transparency,
                        config,
                    )
                } else {
                    Ok(Value::Neutral(
                        Box::new(Neutral::Const(n.clone(), ls.clone())),
                        vec![],
                    ))
                }
            } else {
                Ok(Value::Neutral(
                    Box::new(Neutral::Const(n.clone(), ls.clone())),
                    vec![],
                ))
            }
        }
        Term::App(f, a, label) => {
            let f_val = eval_with_config(f, env, global_env, transparency, config)?;
            let a_val = eval_with_config(a, env, global_env, transparency, config)?;
            apply_with_config(
                f_val,
                a_val,
                label.clone(),
                global_env,
                transparency,
                config,
            )
        }
        Term::Lam(ty, body, info, kind) => {
            let dom = eval_with_config(ty, env, global_env, transparency, config)?;
            Ok(Value::Lam(
                "x".to_string(),
                *info,
                *kind,
                Box::new(dom),
                Closure {
                    env: env.clone(),
                    term: body.clone(),
                },
            ))
        }
        Term::Pi(ty, body, info, kind) => {
            let dom = eval_with_config(ty, env, global_env, transparency, config)?;
            Ok(Value::Pi(
                "x".to_string(),
                *info,
                *kind,
                Box::new(dom),
                Closure {
                    env: env.clone(),
                    term: body.clone(),
                },
            ))
        }
        Term::LetE(_, val, body) => {
            let v = eval_with_config(val, env, global_env, transparency, config)?;
            let mut new_env = env.clone();
            new_env.push(v);
            eval_with_config(body, &new_env, global_env, transparency, config)
        }
        Term::Ind(n, ls) => Ok(Value::Ind(n.clone(), ls.clone(), vec![])),
        Term::Ctor(n, idx, ls) => Ok(Value::Ctor(n.clone(), *idx, ls.clone(), vec![])),
        Term::Rec(n, ls) => Ok(Value::Neutral(
            Box::new(Neutral::Rec(n.clone(), ls.clone())),
            vec![],
        )),
        Term::Fix(ty, body) => {
            let ty_val = eval_with_config(ty, env, global_env, transparency, config)?;
            Ok(Value::Fix(
                Box::new(ty_val),
                Closure {
                    env: env.clone(),
                    term: body.clone(),
                },
            ))
        }
        Term::Meta(m) => Ok(Value::Neutral(Box::new(Neutral::Meta(*m)), vec![])),
    }
}

pub fn apply(
    f: Value,
    a: Value,
    global_env: &Env,
    transparency: Transparency,
) -> Result<Value, NbeError> {
    let mut config = EvalConfig::unlimited();
    apply_with_config(f, a, None, global_env, transparency, &mut config)
}

fn apply_with_config(
    f: Value,
    a: Value,
    label: Option<String>,
    global_env: &Env,
    transparency: Transparency,
    config: &mut EvalConfig,
) -> Result<Value, NbeError> {
    match f {
        Value::Lam(_, _, _, _, closure) => {
            let mut new_env = closure.env.clone();
            new_env.push(a);
            eval_with_config(&closure.term, &new_env, global_env, transparency, config)
        }
        Value::Fix(ty, closure) => {
            if !config.allow_fix_unfold {
                return Err(NbeError::FixUnfoldDisallowed);
            }
            // Unfold: body[f := fix]
            config.tick(FuelEvent::UnfoldFix)?;
            let mut new_env = closure.env.clone();
            let fix_val = Value::Fix(ty, closure.clone());
            new_env.push(fix_val); // Push the Fix value itself
            let body_val =
                eval_with_config(&closure.term, &new_env, global_env, transparency, config)?;
            apply_with_config(body_val, a, None, global_env, transparency, config)
        }
        Value::Neutral(head, mut spine) => {
            spine.push(SpineItem { arg: a, label });

            // Check for Iota reduction if head is Rec
            if let Neutral::Rec(ind_name, levels) = &*head {
                // Try to reduce
                if let Some(reduced) =
                    try_reduce_rec(ind_name, levels, &spine, global_env, transparency, config)?
                {
                    return Ok(reduced);
                }
            }
            Ok(Value::Neutral(head, spine))
        }
        Value::Ctor(n, idx, ls, mut args) => {
            args.push(a);
            Ok(Value::Ctor(n, idx, ls, args))
        }
        Value::Ind(n, ls, mut args) => {
            // Type-level application: e.g., List Nat
            args.push(a);
            Ok(Value::Ind(n, ls, args))
        }
        _ => Err(NbeError::NonFunctionApplication),
    }
}

/// Try to partially reduce a Rec application
fn try_reduce_rec(
    ind_name: &str,
    levels: &[Level],
    args: &[SpineItem],
    global_env: &Env,
    transparency: Transparency,
    config: &mut EvalConfig,
) -> Result<Option<Value>, NbeError> {
    let info = match global_env.inductive_info(ind_name) {
        Some(info) => info,
        None => return Ok(None),
    };
    let rec = &info.recursor;

    if args.len() < rec.expected_args {
        return Ok(None);
    }

    let major_idx = rec.major_index();
    let major = match args.get(major_idx) {
        Some(major) => major,
        None => return Ok(None),
    };

    let (ctor_idx, ctor_args) = match &major.arg {
        Value::Ctor(_, ctor_idx, _, ctor_args) => (*ctor_idx, ctor_args),
        _ => return Ok(None),
    };

    let ctor_info = match rec.ctor_infos.get(ctor_idx) {
        Some(info) => info,
        None => return Ok(None),
    };
    if ctor_args.len() != ctor_info.arity {
        return Ok(None);
    }

    let minor_idx = match rec.minor_index(ctor_idx) {
        Some(idx) => idx,
        None => return Ok(None),
    };
    let minor = &args[minor_idx].arg;

    let mut res = minor.clone();
    config.tick(FuelEvent::ReduceRecursor(ind_name.to_string()))?;

    // c_args includes params. We iterate from num_params to end.
    for i in rec.num_params..ctor_info.arity {
        let field_val = ctor_args[i].clone();
        res = apply_with_config(
            res,
            field_val.clone(),
            None,
            global_env,
            transparency,
            config,
        )?;

        let rec_terms = ctor_info.rec_indices.get(i).and_then(|v| v.as_ref());
        if let Some(terms) = rec_terms {
            let mut index_vals = Vec::new();
            let mut env_vals = Vec::new();
            for v in ctor_args.iter().take(i) {
                env_vals.push(v.clone());
            }
            for term in terms {
                let idx_val = eval_with_config(term, &env_vals, global_env, transparency, config)?;
                index_vals.push(idx_val);
            }

            // Construct IH: Rec(params, motive, minors, indices, field_val)
            let mut ih_args: Vec<Value> = Vec::new();
            if rec.num_params > 0 {
                ih_args.extend(args[0..rec.num_params].iter().map(|item| item.arg.clone()));
            }
            ih_args.push(args[rec.num_params].arg.clone());
            if rec.num_ctors > 0 {
                ih_args.extend(
                    args[rec.num_params + 1..rec.num_params + 1 + rec.num_ctors]
                        .iter()
                        .map(|item| item.arg.clone()),
                );
            }
            if rec.num_indices > 0 {
                if index_vals.len() != rec.num_indices {
                    return Ok(None);
                }
                ih_args.extend(index_vals.into_iter());
            }
            ih_args.push(field_val);

            let ih_val = apply_recursor_with_args(
                ind_name,
                levels,
                &ih_args,
                global_env,
                transparency,
                config,
            )?;

            res = apply_with_config(res, ih_val, None, global_env, transparency, config)?;
        }
    }

    // Apply ANY extra arguments (if Rec was applied to more than needed)
    for extra in &args[rec.expected_args..] {
        res = apply_with_config(
            res,
            extra.arg.clone(),
            None,
            global_env,
            transparency,
            config,
        )?;
    }
    Ok(Some(res))
}

fn apply_recursor_with_args(
    ind_name: &str,
    levels: &[Level],
    args: &[Value],
    global_env: &Env,
    transparency: Transparency,
    config: &mut EvalConfig,
) -> Result<Value, NbeError> {
    let mut value = Value::Neutral(
        Box::new(Neutral::Rec(ind_name.to_string(), levels.to_vec())),
        Vec::new(),
    );
    for arg in args {
        value = apply_with_config(value, arg.clone(), None, global_env, transparency, config)?;
    }
    Ok(value)
}

pub fn quote(
    v: Value,
    level: usize,
    global_env: &Env,
    transparency: Transparency,
) -> Result<Rc<Term>, NbeError> {
    match v {
        Value::Neutral(head, spine) => {
            let mut t = match *head {
                Neutral::Var(l) => Rc::new(Term::Var(level - 1 - l)),
                Neutral::FreeVar(idx) => Rc::new(Term::Var(idx)), // Preserve original index for free vars
                Neutral::Const(n, ls) => Rc::new(Term::Const(n, ls)),
                Neutral::Rec(n, ls) => Rc::new(Term::Rec(n, ls)),
                Neutral::Meta(id) => Rc::new(Term::Meta(id)), // Preserve metavariable
            };
            for item in spine {
                t = Term::app_with_label(
                    t,
                    quote(item.arg, level, global_env, transparency)?,
                    item.label,
                );
            }
            Ok(t)
        }
        Value::Lam(_, info, kind, dom, closure) => {
            let dom_t = quote(*dom, level, global_env, transparency)?;
            let var = Value::var(level);
            let mut new_env = closure.env.clone();
            new_env.push(var);
            let body_val = eval(&closure.term, &new_env, global_env, transparency)?;
            Ok(Term::lam_with_kind(
                dom_t,
                quote(body_val, level + 1, global_env, transparency)?,
                info,
                kind,
            ))
        }
        Value::Pi(_, info, kind, dom, closure) => {
            let dom_t = quote(*dom, level, global_env, transparency)?;
            let var = Value::var(level);
            let mut new_env = closure.env.clone();
            new_env.push(var);
            let body_val = eval(&closure.term, &new_env, global_env, transparency)?;
            Ok(Term::pi_with_kind(
                dom_t,
                quote(body_val, level + 1, global_env, transparency)?,
                info,
                kind,
            ))
        }
        Value::Sort(l) => Ok(Rc::new(Term::Sort(l))),
        Value::Ind(n, ls, args) => {
            let mut t = Rc::new(Term::Ind(n, ls));
            for arg in args {
                t = Term::app(t, quote(arg, level, global_env, transparency)?);
            }
            Ok(t)
        }
        Value::Ctor(n, idx, ls, args) => {
            let mut t = Rc::new(Term::Ctor(n, idx, ls));
            for arg in args {
                t = Term::app(t, quote(arg, level, global_env, transparency)?);
            }
            Ok(t)
        }
        Value::Rec(n, ls) => Ok(Rc::new(Term::Rec(n, ls))),
        Value::Fix(ty, closure) => {
            let ty_t = quote(*ty, level, global_env, transparency)?;
            let var = Value::var(level);
            let mut new_env = closure.env.clone();
            new_env.push(var);
            let body_val = eval(&closure.term, &new_env, global_env, transparency)?;
            Ok(Rc::new(Term::Fix(
                ty_t,
                quote(body_val, level + 1, global_env, transparency)?,
            )))
        }
    }
}

pub fn quote_with_fuel(
    v: Value,
    level: usize,
    global_env: &Env,
    transparency: Transparency,
    fuel: usize,
) -> Result<Rc<Term>, NbeError> {
    match v {
        Value::Neutral(head, spine) => {
            let mut t = match *head {
                Neutral::Var(l) => Rc::new(Term::Var(level - 1 - l)),
                Neutral::FreeVar(idx) => Rc::new(Term::Var(idx)),
                Neutral::Const(n, ls) => Rc::new(Term::Const(n, ls)),
                Neutral::Rec(n, ls) => Rc::new(Term::Rec(n, ls)),
                Neutral::Meta(id) => Rc::new(Term::Meta(id)),
            };
            for item in spine {
                t = Term::app_with_label(
                    t,
                    quote_with_fuel(item.arg, level, global_env, transparency, fuel)?,
                    item.label,
                );
            }
            Ok(t)
        }
        Value::Lam(_, info, kind, dom, closure) => {
            let dom_t = quote_with_fuel(*dom, level, global_env, transparency, fuel)?;
            let var = Value::var(level);
            let mut new_env = closure.env.clone();
            new_env.push(var);
            let body_val = eval_with_fuel(&closure.term, &new_env, global_env, transparency, fuel)?;
            Ok(Term::lam_with_kind(
                dom_t,
                quote_with_fuel(body_val, level + 1, global_env, transparency, fuel)?,
                info,
                kind,
            ))
        }
        Value::Pi(_, info, kind, dom, closure) => {
            let dom_t = quote_with_fuel(*dom, level, global_env, transparency, fuel)?;
            let var = Value::var(level);
            let mut new_env = closure.env.clone();
            new_env.push(var);
            let body_val = eval_with_fuel(&closure.term, &new_env, global_env, transparency, fuel)?;
            Ok(Term::pi_with_kind(
                dom_t,
                quote_with_fuel(body_val, level + 1, global_env, transparency, fuel)?,
                info,
                kind,
            ))
        }
        Value::Sort(l) => Ok(Rc::new(Term::Sort(l))),
        Value::Ind(n, ls, args) => {
            let mut t = Rc::new(Term::Ind(n, ls));
            for arg in args {
                t = Term::app(
                    t,
                    quote_with_fuel(arg, level, global_env, transparency, fuel)?,
                );
            }
            Ok(t)
        }
        Value::Ctor(n, idx, ls, args) => {
            let mut t = Rc::new(Term::Ctor(n, idx, ls));
            for arg in args {
                t = Term::app(
                    t,
                    quote_with_fuel(arg, level, global_env, transparency, fuel)?,
                );
            }
            Ok(t)
        }
        Value::Rec(n, ls) => Ok(Rc::new(Term::Rec(n, ls))),
        Value::Fix(ty, closure) => {
            let ty_t = quote_with_fuel(*ty, level, global_env, transparency, fuel)?;
            let var = Value::var(level);
            let mut new_env = closure.env.clone();
            new_env.push(var);
            let body_val = eval_with_fuel(&closure.term, &new_env, global_env, transparency, fuel)?;
            Ok(Rc::new(Term::Fix(
                ty_t,
                quote_with_fuel(body_val, level + 1, global_env, transparency, fuel)?,
            )))
        }
    }
}

pub fn is_def_eq(t1: Rc<Term>, t2: Rc<Term>, global_env: &Env, transparency: Transparency) -> bool {
    is_def_eq_with_fuel(t1, t2, global_env, transparency, default_def_eq_fuel())
}

pub fn is_def_eq_with_fuel(
    t1: Rc<Term>,
    t2: Rc<Term>,
    global_env: &Env,
    transparency: Transparency,
    fuel: usize,
) -> bool {
    match is_def_eq_result(t1, t2, global_env, transparency, fuel) {
        Ok(result) => result,
        Err(_) => false,
    }
}

pub fn is_def_eq_result(
    t1: Rc<Term>,
    t2: Rc<Term>,
    global_env: &Env,
    transparency: Transparency,
    fuel: usize,
) -> Result<bool, NbeError> {
    let mut config = DefEqConfig::new(transparency, fuel);
    is_def_eq_with_config(&t1, &t2, &vec![], global_env, &mut config)
}

pub fn is_def_eq_in_ctx_result(
    t1: Rc<Term>,
    t2: Rc<Term>,
    env: &EvalEnv,
    global_env: &Env,
    transparency: Transparency,
    fuel: usize,
) -> Result<bool, NbeError> {
    let mut config = DefEqConfig::new(transparency, fuel);
    is_def_eq_with_config(&t1, &t2, env, global_env, &mut config)
}

fn eval_with_cache(
    t: &Rc<Term>,
    env: &EvalEnv,
    global_env: &Env,
    config: &mut DefEqConfig,
) -> Result<Value, NbeError> {
    let key = config.cache_key(t, env.len());
    if let Some(val) = config.cache.get(&key) {
        return Ok(val.clone());
    }
    let val = eval_with_config(
        t,
        env,
        global_env,
        config.transparency,
        &mut config.eval_config,
    )?;
    config.cache.insert(key, val.clone());
    Ok(val)
}

fn is_def_eq_with_config(
    t1: &Rc<Term>,
    t2: &Rc<Term>,
    env: &EvalEnv,
    global_env: &Env,
    config: &mut DefEqConfig,
) -> Result<bool, NbeError> {
    let level = env.len();
    let v1 = eval_with_cache(t1, env, global_env, config)?;
    let v2 = eval_with_cache(t2, env, global_env, config)?;
    check_eq(
        v1,
        v2,
        level,
        global_env,
        config.transparency,
        &mut config.eval_config,
    )
}

fn check_eq(
    v1: Value,
    v2: Value,
    level: usize,
    global_env: &Env,
    transparency: Transparency,
    config: &mut EvalConfig,
) -> Result<bool, NbeError> {
    match (v1, v2) {
        (Value::Lam(_, _, kind1, dom1, cls1), Value::Lam(_, _, kind2, dom2, cls2)) => {
            if kind1 != kind2 {
                return Ok(false);
            }
            if !check_eq(*dom1, *dom2, level, global_env, transparency, config)? {
                return Ok(false);
            }
            // Recurse with fresh var
            let var = Value::var(level);
            let mut env1 = cls1.env.clone();
            env1.push(var.clone());
            let mut env2 = cls2.env.clone();
            env2.push(var);
            let body1 = eval_with_config(&cls1.term, &env1, global_env, transparency, config)?;
            let body2 = eval_with_config(&cls2.term, &env2, global_env, transparency, config)?;
            check_eq(body1, body2, level + 1, global_env, transparency, config)
        }
        (Value::Lam(_, _, kind, _, cls), other) | (other, Value::Lam(_, _, kind, _, cls)) => {
            // Eta expansion
            if matches!(kind, FunctionKind::FnOnce) {
                return Ok(false);
            }
            let var = Value::var(level);
            let mut env = cls.env.clone();
            env.push(var.clone());
            let body = eval_with_config(&cls.term, &env, global_env, transparency, config)?;
            let app = apply_with_config(other, var, None, global_env, transparency, config)?;
            check_eq(body, app, level + 1, global_env, transparency, config)
        }
        (Value::Pi(_, _, kind1, d1, cls1), Value::Pi(_, _, kind2, d2, cls2)) => {
            if kind1 != kind2 {
                return Ok(false);
            }
            if !check_eq(*d1, *d2, level, global_env, transparency, config)? {
                return Ok(false);
            }
            let var = Value::var(level);
            let mut env1 = cls1.env.clone();
            env1.push(var.clone());
            let mut env2 = cls2.env.clone();
            env2.push(var);
            let body1 = eval_with_config(&cls1.term, &env1, global_env, transparency, config)?;
            let body2 = eval_with_config(&cls2.term, &env2, global_env, transparency, config)?;
            check_eq(body1, body2, level + 1, global_env, transparency, config)
        }
        (Value::Sort(l1), Value::Sort(l2)) => Ok(level_eq(&l1, &l2)),
        (Value::Ind(n1, ls1, a1), Value::Ind(n2, ls2, a2)) => Ok(n1 == n2
            && levels_eq(&ls1, &ls2)
            && check_eq_vec(&a1, &a2, level, global_env, transparency, config)?),
        (Value::Ctor(n1, i1, ls1, a1), Value::Ctor(n2, i2, ls2, a2)) => Ok(n1 == n2
            && i1 == i2
            && levels_eq(&ls1, &ls2)
            && check_eq_vec(&a1, &a2, level, global_env, transparency, config)?),
        (Value::Rec(n1, ls1), Value::Rec(n2, ls2)) => Ok(n1 == n2 && levels_eq(&ls1, &ls2)),
        (Value::Fix(ty1, cls1), Value::Fix(ty2, cls2)) => {
            if !check_eq(*ty1, *ty2, level, global_env, transparency, config)? {
                return Ok(false);
            }
            let var = Value::var(level);
            let mut env1 = cls1.env.clone();
            env1.push(var.clone());
            let mut env2 = cls2.env.clone();
            env2.push(var);
            let body1 = eval_with_config(&cls1.term, &env1, global_env, transparency, config)?;
            let body2 = eval_with_config(&cls2.term, &env2, global_env, transparency, config)?;
            check_eq(body1, body2, level + 1, global_env, transparency, config)
        }
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) => Ok(check_neutral_head(&*h1, &*h2)
            && check_eq_spine(&s1, &s2, level, global_env, transparency, config)?),
        _ => Ok(false),
    }
}

fn check_neutral_head(h1: &Neutral, h2: &Neutral) -> bool {
    match (h1, h2) {
        (Neutral::Var(i1), Neutral::Var(i2)) => i1 == i2,
        (Neutral::FreeVar(i1), Neutral::FreeVar(i2)) => i1 == i2,
        (Neutral::Const(n1, ls1), Neutral::Const(n2, ls2)) => n1 == n2 && levels_eq(ls1, ls2),
        (Neutral::Rec(n1, ls1), Neutral::Rec(n2, ls2)) => n1 == n2 && levels_eq(ls1, ls2),
        (Neutral::Meta(id1), Neutral::Meta(id2)) => id1 == id2,
        _ => false,
    }
}

fn check_eq_vec(
    bs1: &[Value],
    bs2: &[Value],
    level: usize,
    global_env: &Env,
    transparency: Transparency,
    config: &mut EvalConfig,
) -> Result<bool, NbeError> {
    if bs1.len() != bs2.len() {
        return Ok(false);
    }
    for (b1, b2) in bs1.iter().zip(bs2.iter()) {
        if !check_eq(
            b1.clone(),
            b2.clone(),
            level,
            global_env,
            transparency,
            config,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn check_eq_spine(
    bs1: &[SpineItem],
    bs2: &[SpineItem],
    level: usize,
    global_env: &Env,
    transparency: Transparency,
    config: &mut EvalConfig,
) -> Result<bool, NbeError> {
    if bs1.len() != bs2.len() {
        return Ok(false);
    }
    for (b1, b2) in bs1.iter().zip(bs2.iter()) {
        if b1.label != b2.label {
            return Ok(false);
        }
        if !check_eq(
            b1.arg.clone(),
            b2.arg.clone(),
            level,
            global_env,
            transparency,
            config,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}
