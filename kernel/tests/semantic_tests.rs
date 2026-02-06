//! Kernel semantic tests for Mode A: Semantics & IR Stability
//!
//! These tests verify core language semantics that must remain stable.

use kernel::ast::{
    BinderInfo, Constructor, Definition, FunctionKind, InductiveDecl, Level, Term, Transparency,
};
use kernel::checker::{
    classical_axiom_dependencies, infer, is_copy_type_in_env, is_def_eq, whnf, Context, Env,
    TypeError,
};
use kernel::nbe::is_def_eq_with_fuel;
use std::rc::Rc;

fn add_comp(env: &mut Env) {
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let comp_ind = Rc::new(Term::Ind("Comp".to_string(), vec![]));
    let comp_body = Term::app(comp_ind.clone(), Term::var(1));
    let ret_ty = Term::pi(
        type1.clone(),
        Term::pi(Term::var(0), comp_body, BinderInfo::Default),
        BinderInfo::Default,
    );
    let comp_decl = InductiveDecl::new(
        "Comp".to_string(),
        Term::pi(
            type1,
            Term::sort(Level::Succ(Box::new(Level::Zero))),
            BinderInfo::Default,
        ),
        vec![Constructor {
            name: "ret".to_string(),
            ty: ret_ty,
        }],
    );
    env.add_inductive(comp_decl)
        .expect("Comp inductive should be accepted");
    env.set_allow_reserved_primitives(allow_reserved);
}

fn add_nat(env: &mut Env) -> Rc<Term> {
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ref = Rc::new(Term::Ind("Nat".to_string(), vec![]));
    let nat_decl = InductiveDecl::new_copy(
        "Nat".to_string(),
        type0,
        vec![Constructor {
            name: "zero".to_string(),
            ty: nat_ref.clone(),
        }],
    );
    env.add_inductive(nat_decl)
        .expect("Nat inductive should be accepted");
    env.set_allow_reserved_primitives(allow_reserved);
    nat_ref
}

// =============================================================================
// IMPREDICATIVE PROP TESTS
// =============================================================================

/// Test: Prop is impredicative - forall P:Prop, P has type Prop
#[test]
fn test_impredicative_prop_basic() {
    let env = Env::new();
    let ctx = Context::new();

    // (Pi P : Prop. P) : Prop
    // In de Bruijn: (Pi (Sort Prop) (Var 0))
    let prop = Rc::new(Term::Sort(Level::Zero)); // Prop = Sort 0
    let forall_p_p = Rc::new(Term::Pi(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let result = infer(&env, &ctx, forall_p_p).expect("Should infer type");

    // Result should be Prop (Sort 0)
    if let Term::Sort(level) = &*result {
        assert!(
            matches!(level, Level::Zero),
            "forall P:Prop, P should be in Prop"
        );
    } else {
        panic!("Expected Sort, got {:?}", result);
    }
}

/// Test: Prop -> Type lifts to Type (predicative at higher levels)
#[test]
fn test_prop_to_type_lifts() {
    let env = Env::new();
    let ctx = Context::new();

    // (Pi _ : Prop. Type) should be Type
    let prop = Rc::new(Term::Sort(Level::Zero));
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let pi = Rc::new(Term::Pi(prop, type1, BinderInfo::Default, FunctionKind::Fn));

    let result = infer(&env, &ctx, pi).expect("Should infer type");

    if let Term::Sort(level) = &*result {
        // Should be at least Type 1
        assert!(
            !matches!(level, Level::Zero),
            "Prop -> Type should not be in Prop"
        );
    } else {
        panic!("Expected Sort, got {:?}", result);
    }
}

/// Test: Nested impredicative Prop
#[test]
fn test_nested_impredicative_prop() {
    let env = Env::new();
    let ctx = Context::new();

    // (Pi P : Prop. (Pi Q : Prop. P)) : Prop
    let prop = Rc::new(Term::Sort(Level::Zero));
    let var_p = Rc::new(Term::Var(1)); // P is now at index 1 after Q binding
    let inner = Rc::new(Term::Pi(
        prop.clone(),
        var_p,
        BinderInfo::Default,
        FunctionKind::Fn,
    )); // Pi Q : Prop. P
    let outer = Rc::new(Term::Pi(
        prop.clone(),
        inner,
        BinderInfo::Default,
        FunctionKind::Fn,
    )); // Pi P : Prop. (...)

    let result = infer(&env, &ctx, outer).expect("Should infer type");

    if let Term::Sort(level) = &*result {
        assert!(
            matches!(level, Level::Zero),
            "Nested forall in Prop should stay in Prop"
        );
    } else {
        panic!("Expected Sort, got {:?}", result);
    }
}

/// Test: Partial definitions must return Comp A and should register.
#[test]
fn test_partial_def_returns_comp() {
    let mut env = Env::new();
    add_comp(&mut env);
    let nat_ref = add_nat(&mut env);

    let comp_nat = Term::app(Term::ind("Comp".to_string()), nat_ref.clone());
    let ret_nat = Term::app(
        Term::app(Term::ctor("Comp".to_string(), 0), nat_ref.clone()),
        Term::ctor("Nat".to_string(), 0),
    );

    let partial_def = Definition::partial("safe_partial".to_string(), comp_nat, ret_nat);
    env.add_definition(partial_def)
        .expect("Partial definition should register");
}

// =============================================================================
// TRANSPARENCY TESTS
// =============================================================================

/// Test: Transparent definitions unfold in defeq
#[test]
fn test_transparent_unfolds_in_defeq() {
    let mut env = Env::new();

    // Define: id := lam x. x (transparent by default)
    let prop = Rc::new(Term::Sort(Level::Zero));
    let id_body = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let id_type = Rc::new(Term::Pi(
        prop.clone(),
        prop.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // Add a total transparent definition
    env.add_definition(Definition::total(
        "id".to_string(),
        id_type,
        id_body.clone(),
    ))
    .expect("Failed to add id");

    // id should be defeq to (lam x. x) when transparent
    let id_const = Rc::new(Term::Const("id".to_string(), vec![]));

    assert!(
        is_def_eq(&env, id_const, id_body, Transparency::Reducible),
        "Transparent definition should unfold in defeq"
    );
}

/// Test: Opaque definitions do NOT unfold in defeq
#[test]
fn test_opaque_does_not_unfold() {
    let mut env = Env::new();

    // Define: secret := lam x. x (OPAQUE)
    let prop = Rc::new(Term::Sort(Level::Zero));
    let secret_body = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let secret_type = Rc::new(Term::Pi(
        prop.clone(),
        prop.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // Create definition and set it as opaque (Transparency::None = opaque/irreducible)
    let mut def = Definition::total("secret".to_string(), secret_type, secret_body.clone());
    def.transparency = Transparency::None;
    env.add_definition(def).expect("Failed to add secret");

    let secret_const = Rc::new(Term::Const("secret".to_string(), vec![]));

    // secret should NOT be defeq to (lam x. x) when opaque
    // Use Reducible transparency which respects opacity
    assert!(
        !is_def_eq(
            &env,
            secret_const.clone(),
            secret_body.clone(),
            Transparency::Reducible
        ),
        "Opaque definition should NOT unfold in defeq"
    );
    assert!(
        is_def_eq(&env, secret_const, secret_body, Transparency::All),
        "Transparency::All should unfold opaque definitions"
    );
}

// =============================================================================
// NBE/DEF-EQ REGRESSIONS
// =============================================================================

#[test]
fn test_whnf_preserves_lambda_domain() {
    let env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));
    let dom = Rc::new(Term::Pi(
        prop.clone(),
        prop.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let lam = Rc::new(Term::Lam(
        dom.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let reduced = whnf(&env, lam, Transparency::All).expect("whnf failed");
    match &*reduced {
        Term::Lam(dom_whnf, _, _, FunctionKind::Fn) => {
            assert!(
                is_def_eq(&env, dom_whnf.clone(), dom, Transparency::Reducible),
                "whnf should preserve lambda binder types"
            );
        }
        _ => panic!("Expected lambda after whnf"),
    }
}

#[test]
fn test_defeq_fuel_limits_unfolding() {
    let mut env = Env::new();
    let ty = Rc::new(Term::Sort(Level::Zero));
    let base = Rc::new(Term::Const("base".to_string(), vec![]));

    env.add_definition(Definition::axiom("base".to_string(), ty.clone()))
        .expect("Failed to add base axiom");

    let mut d0 = Definition::total("d0".to_string(), ty.clone(), base.clone());
    d0.noncomputable = true;
    env.add_definition(d0).expect("Failed to add d0");
    let mut d1 = Definition::total(
        "d1".to_string(),
        ty.clone(),
        Rc::new(Term::Const("d0".to_string(), vec![])),
    );
    d1.noncomputable = true;
    env.add_definition(d1).expect("Failed to add d1");
    let mut d2 = Definition::total(
        "d2".to_string(),
        ty.clone(),
        Rc::new(Term::Const("d1".to_string(), vec![])),
    );
    d2.noncomputable = true;
    env.add_definition(d2).expect("Failed to add d2");
    let mut d3 = Definition::total(
        "d3".to_string(),
        ty.clone(),
        Rc::new(Term::Const("d2".to_string(), vec![])),
    );
    d3.noncomputable = true;
    env.add_definition(d3).expect("Failed to add d3");
    let mut d4 = Definition::total(
        "d4".to_string(),
        ty.clone(),
        Rc::new(Term::Const("d3".to_string(), vec![])),
    );
    d4.noncomputable = true;
    env.add_definition(d4).expect("Failed to add d4");

    let deep = Rc::new(Term::Const("d4".to_string(), vec![]));
    assert!(
        !is_def_eq_with_fuel(deep.clone(), base.clone(), &env, Transparency::All, 2),
        "fuel should bound delta unfolding"
    );
    assert!(
        is_def_eq_with_fuel(deep, base, &env, Transparency::All, 10),
        "enough fuel should allow unfolding to succeed"
    );
}

#[test]
fn test_boom_eq_exponential_unfolding_is_bounded() {
    let mut env = Env::new();
    let ty = Rc::new(Term::Sort(Level::Zero));
    let pair = Rc::new(Term::Const("pair".to_string(), vec![]));
    let base = Rc::new(Term::Const("z".to_string(), vec![]));

    let pair_ty = Rc::new(Term::Pi(
        ty.clone(),
        Rc::new(Term::Pi(
            ty.clone(),
            ty.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    env.add_definition(Definition::axiom("pair".to_string(), pair_ty))
        .expect("Failed to add pair axiom");
    env.add_definition(Definition::axiom("z".to_string(), ty.clone()))
        .expect("Failed to add z axiom");

    let boom_term = |n: usize| {
        fn build(n: usize, pair: &Rc<Term>, base: &Rc<Term>) -> Rc<Term> {
            if n == 0 {
                return base.clone();
            }
            let prev = build(n - 1, pair, base);
            Term::app(Term::app(pair.clone(), prev.clone()), prev)
        }
        build(n, &pair, &base)
    };

    let n = 7;
    let mut boom0 = Definition::total("boom0".to_string(), ty.clone(), base.clone());
    boom0.noncomputable = true;
    env.add_definition(boom0).expect("Failed to add boom0");
    for i in 1..=n {
        let prev = Rc::new(Term::Const(format!("boom{}", i - 1), vec![]));
        let body = Term::app(Term::app(pair.clone(), prev.clone()), prev);
        let mut boom = Definition::total(format!("boom{}", i), ty.clone(), body);
        boom.noncomputable = true;
        env.add_definition(boom).expect("Failed to add boom def");
    }

    let boom_n = Rc::new(Term::Const(format!("boom{}", n), vec![]));
    let expected = boom_term(n);

    assert!(
        !is_def_eq_with_fuel(
            boom_n.clone(),
            expected.clone(),
            &env,
            Transparency::All,
            10
        ),
        "boom should exceed low defeq fuel on exponential unfolding"
    );
    assert!(
        is_def_eq_with_fuel(boom_n, expected, &env, Transparency::All, 2000),
        "boom should normalize with sufficient defeq fuel"
    );
}

#[test]
fn test_indexed_recursor_uses_field_indices() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    // Nat : Type
    let nat_decl = InductiveDecl {
        name: "Nat".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: Term::sort(Level::Zero),
        ctors: vec![
            Constructor {
                name: "zero".to_string(),
                ty: Rc::new(Term::Ind("Nat".to_string(), vec![])),
            },
            Constructor {
                name: "succ".to_string(),
                ty: Term::pi(
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    Rc::new(Term::Ind("Nat".to_string(), vec![])),
                    BinderInfo::Default,
                ),
            },
        ],
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

    let vec_decl = InductiveDecl {
        name: "Vec".to_string(),
        univ_params: vec![],
        num_params: 1,
        ty: vec_ty,
        ctors: vec![
            Constructor {
                name: "nil".to_string(),
                ty: nil_ty,
            },
            Constructor {
                name: "cons".to_string(),
                ty: cons_ty,
            },
        ],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(vec_decl).unwrap();

    let info = env.inductive_info("Vec").expect("Vec inductive info");
    assert_eq!(info.recursor.num_params, 1);
    assert_eq!(info.recursor.num_indices, 1);
    assert_eq!(info.recursor.num_ctors, 2);
    assert_eq!(info.recursor.expected_args, 1 + 1 + 2 + 1 + 1);
    let cons_info = &info.recursor.ctor_infos[1];
    assert_eq!(cons_info.arity, 4);
    assert_eq!(cons_info.rec_indices.len(), 4);
    let cons_rec_indices_ok = match cons_info.rec_indices.get(3) {
        Some(Some(indices)) => indices.len() == 1,
        _ => false,
    };
    assert!(cons_rec_indices_ok);

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
        is_def_eq(&env, rec_app, ih_expected, Transparency::All),
        "Indexed recursor should use field indices for IH"
    );
}

/// Test: Defeq is deterministic
#[test]
fn test_defeq_deterministic() {
    let env = Env::new();

    // Same terms should always be defeq (reflexivity)
    let term = Rc::new(Term::Lam(
        Rc::new(Term::Sort(Level::Zero)),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // Run multiple times to check determinism
    for _ in 0..10 {
        assert!(
            is_def_eq(&env, term.clone(), term.clone(), Transparency::Reducible),
            "Defeq should be deterministic and reflexive"
        );
    }
}

// =============================================================================
// DEFINITIONAL EQUALITY TESTS (beta/delta/iota)
// =============================================================================

/// Test: Beta reduction - (lam x. t) arg = t[arg/x]
#[test]
fn test_beta_reduction() {
    let env = Env::new();

    // (lam x:Prop. x) applied to Prop
    let prop = Rc::new(Term::Sort(Level::Zero));
    let identity = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let app = Term::app(identity, prop.clone());

    // Should reduce to Prop
    let reduced = whnf(&env, app, Transparency::Reducible).expect("whnf failed");

    assert!(
        is_def_eq(&env, reduced, prop, Transparency::Reducible),
        "Beta reduction: (lam x. x) Prop should equal Prop"
    );
}

/// Test: Multiple beta reductions
#[test]
fn test_nested_beta() {
    let env = Env::new();

    // (lam f. lam x. f x) (lam y. y) z ≡ z
    let prop = Rc::new(Term::Sort(Level::Zero));

    // lam y. y
    let id = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // lam f. lam x. f x
    let apply = Rc::new(Term::Lam(
        prop.clone(), // type of f (simplified)
        Rc::new(Term::Lam(
            prop.clone(), // type of x
            Term::app(Rc::new(Term::Var(1)), Rc::new(Term::Var(0))),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // (apply id)
    let apply_id = Term::app(apply, id);

    // (apply id) z where z is just Prop
    let z = Rc::new(Term::Sort(Level::Zero)); // using Prop as "z"
    let result = Term::app(apply_id, z.clone());

    let reduced = whnf(&env, result, Transparency::Reducible).expect("whnf failed");

    assert!(
        is_def_eq(&env, reduced, z, Transparency::Reducible),
        "Nested beta should reduce correctly"
    );
}

/// Test: Zeta reduction - let bindings reduce in WHNF
#[test]
fn test_zeta_reduction() {
    let env = Env::new();

    // let x : Prop = Prop in x  ==> Prop
    let prop = Rc::new(Term::Sort(Level::Zero));
    let let_expr = Rc::new(Term::LetE(
        prop.clone(),
        prop.clone(),
        Rc::new(Term::Var(0)),
    ));

    let reduced = whnf(&env, let_expr, Transparency::Reducible).expect("whnf failed");

    assert!(
        is_def_eq(&env, reduced, prop, Transparency::Reducible),
        "Zeta reduction: let x = Prop in x should reduce to Prop"
    );
}

// =============================================================================
// UNIVERSE LEVEL TESTS
// =============================================================================

/// Test: Type 0 : Type 1
#[test]
fn test_universe_hierarchy() {
    let env = Env::new();
    let ctx = Context::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let result = infer(&env, &ctx, type0).expect("Type 0 should have a type");

    if let Term::Sort(Level::Succ(inner)) = &*result {
        if let Level::Succ(_) = &**inner {
            // Type 0 : Type 1, good
        } else {
            panic!("Type 0 should be in Type 1");
        }
    } else {
        panic!("Expected higher universe");
    }
}

/// Test: Universe level variables work correctly
#[test]
fn test_level_max() {
    let env = Env::new();
    let ctx = Context::new();

    // Pi (A : Type 0) (B : Type 1). B should have type Type 1
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Succ(Box::new(
        Level::Zero,
    ))))));

    let pi = Rc::new(Term::Pi(
        type0,
        Rc::new(Term::Pi(
            type1,
            Rc::new(Term::Var(0)),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let result = infer(&env, &ctx, pi).expect("Should infer universe");

    // Should be in a high enough universe
    if let Term::Sort(_) = &*result {
        // Good - it has a universe type
    } else {
        panic!("Expected Sort");
    }
}

// =============================================================================
// SUBSTITUTION CORRECTNESS
// =============================================================================

/// Test: Substitution preserves well-typedness
#[test]
fn test_substitution_preserves_typing() {
    let env = Env::new();
    let ctx = Context::new();

    // Test substitution via beta reduction
    // (lam P : Prop. P) applied to Prop should give Prop
    let prop = Rc::new(Term::Sort(Level::Zero));

    // (lam P : Prop. P) - takes a Prop and returns it
    // This has type (P : Prop) -> Prop = Prop -> Prop
    let id_prop = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // Verify the identity on Prop type checks
    let id_type = infer(&env, &ctx, id_prop.clone()).expect("id on Prop should type check");

    // id_type should be Prop -> Prop = (Pi Prop Prop)
    let expected_type = Rc::new(Term::Pi(
        prop.clone(),
        prop.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    assert!(
        is_def_eq(&env, id_type, expected_type, Transparency::Reducible),
        "Identity function should have type Prop -> Prop"
    );
}

// =============================================================================
// RECURSOR / IOTA REDUCTION TESTS
// =============================================================================

/// Test: Inductive type declaration
#[test]
fn test_inductive_type_declaration() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    // Set up Nat inductive with zero and succ
    let nat_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));

    let ctors = vec![
        Constructor {
            name: "zero".to_string(),
            ty: nat_ind.clone(),
        },
        Constructor {
            name: "succ".to_string(),
            ty: Rc::new(Term::Pi(
                nat_ind.clone(),
                nat_ind.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        },
    ];

    env.add_inductive(InductiveDecl::new_copy(
        "Nat".to_string(),
        nat_ty.clone(),
        ctors,
    ))
    .expect("Failed to add Nat");

    let ctx = Context::new();

    // Verify Nat inductive term has type Type 0
    let nat_type = infer(&env, &ctx, nat_ind.clone()).expect("Nat should type check");
    assert!(
        is_def_eq(&env, nat_type, nat_ty, Transparency::Reducible),
        "Nat should have type Type 0"
    );

    // Verify the inductive is in the environment
    assert!(
        env.get_inductive("Nat").is_some(),
        "Nat inductive should be registered"
    );
}

/// Test: Iota reduction on succ case for Nat.rec
#[test]
fn test_iota_reduction_succ_case() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    // Nat : Type 0
    let nat_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));

    let ctors = vec![
        Constructor {
            name: "zero".to_string(),
            ty: nat_ind.clone(),
        },
        Constructor {
            name: "succ".to_string(),
            ty: Rc::new(Term::Pi(
                nat_ind.clone(),
                nat_ind.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        },
    ];

    env.add_inductive(InductiveDecl::new_copy("Nat".to_string(), nat_ty, ctors))
        .expect("Failed to add Nat");

    // Build: Nat.rec motive base step (succ zero)
    // motive = λ_. Nat, base = zero, step = λn. λih. succ ih
    let rec = Rc::new(Term::Rec(
        "Nat".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));
    let motive = Rc::new(Term::Lam(
        nat_ind.clone(),
        nat_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let base = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
    let step = Rc::new(Term::Lam(
        nat_ind.clone(),
        Rc::new(Term::Lam(
            nat_ind.clone(),
            Term::app(
                Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])),
                Rc::new(Term::Var(0)),
            ),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let succ_zero = Term::app(
        Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])),
        base.clone(),
    );

    let app1 = Term::app(rec, motive);
    let app2 = Term::app(app1, base.clone());
    let app3 = Term::app(app2, step);
    let app4 = Term::app(app3, succ_zero.clone());

    let reduced = whnf(&env, app4, Transparency::Reducible).expect("whnf failed");

    assert!(
        is_def_eq(&env, reduced, succ_zero, Transparency::Reducible),
        "Iota reduction should reduce Nat.rec on succ to step application"
    );
}

/// Test: Iota reduction on zero case for Nat.rec
#[test]
fn test_iota_reduction_zero_case() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    // Nat : Type 0
    let nat_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));

    let ctors = vec![
        Constructor {
            name: "zero".to_string(),
            ty: nat_ind.clone(),
        },
        Constructor {
            name: "succ".to_string(),
            ty: Rc::new(Term::Pi(
                nat_ind.clone(),
                nat_ind.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        },
    ];

    env.add_inductive(InductiveDecl::new_copy("Nat".to_string(), nat_ty, ctors))
        .expect("Failed to add Nat");

    // Build: Nat.rec motive base step zero
    let rec = Rc::new(Term::Rec(
        "Nat".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));
    let motive = Rc::new(Term::Lam(
        nat_ind.clone(),
        nat_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let base = Rc::new(Term::Ctor("Nat".to_string(), 0, vec![]));
    let step = Rc::new(Term::Lam(
        nat_ind.clone(),
        Rc::new(Term::Lam(
            nat_ind.clone(),
            Term::app(
                Rc::new(Term::Ctor("Nat".to_string(), 1, vec![])),
                Rc::new(Term::Var(0)),
            ),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let zero = base.clone();

    let app1 = Term::app(rec, motive);
    let app2 = Term::app(app1, base.clone());
    let app3 = Term::app(app2, step);
    let app4 = Term::app(app3, zero.clone());

    let reduced = whnf(&env, app4, Transparency::Reducible).expect("whnf failed");

    assert!(
        is_def_eq(&env, reduced, base, Transparency::Reducible),
        "Iota reduction should reduce Nat.rec on zero to base"
    );
}

// =============================================================================
// PROOF IRRELEVANCE TESTS (Prop elimination restriction)
// =============================================================================

/// Test scaffold: Prop elimination should be restricted
#[test]
fn test_prop_elimination_restricted() {
    let mut env = Env::new();
    let ctx = Context::new();

    // Inductive PWrap : Prop with constructor mk : (Type0) -> PWrap
    // Large elimination to Type should be rejected.
    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let pwrap = Rc::new(Term::Ind("PWrap".to_string(), vec![]));

    let ctor = Constructor {
        name: "mk".to_string(),
        ty: Rc::new(Term::Pi(
            type0,
            pwrap.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
    };

    let decl = InductiveDecl {
        name: "PWrap".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors: vec![ctor],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl).expect("Failed to add PWrap");

    let rec = Rc::new(Term::Rec(
        "PWrap".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));

    match infer(&env, &ctx, rec) {
        Err(TypeError::LargeElimination(name)) => assert_eq!(name, "PWrap"),
        other => panic!("Expected LargeElimination error, got {:?}", other),
    }
}

/// Test: Equality in Prop allows controlled elimination (transport) into Type
#[test]
fn test_eq_allows_large_elimination() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);
    let ctx = Context::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    // Eq : (A : Type 0) -> (a : A) -> (b : A) -> Prop
    let eq_ty = Rc::new(Term::Pi(
        type0.clone(),
        Rc::new(Term::Pi(
            Rc::new(Term::Var(0)),
            Rc::new(Term::Pi(
                Rc::new(Term::Var(1)),
                prop.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // refl : (A : Type 0) -> (a : A) -> Eq A a a
    let eq_ind = Rc::new(Term::Ind("Eq".to_string(), vec![]));
    let refl_body = Term::app(
        Term::app(
            Term::app(eq_ind.clone(), Rc::new(Term::Var(1))),
            Rc::new(Term::Var(0)),
        ),
        Rc::new(Term::Var(0)),
    );
    let refl_ty = Rc::new(Term::Pi(
        type0.clone(),
        Rc::new(Term::Pi(
            Rc::new(Term::Var(0)),
            refl_body,
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let decl = InductiveDecl {
        name: "Eq".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: eq_ty,
        ctors: vec![Constructor {
            name: "refl".to_string(),
            ty: refl_ty,
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl).expect("Failed to add Eq");

    let rec = Rc::new(Term::Rec(
        "Eq".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));

    let result = infer(&env, &ctx, rec);
    assert!(
        result.is_ok(),
        "Eq eliminator should allow elimination into Type: {:?}",
        result
    );
}

/// Test: Proofs in Prop are computationally irrelevant
#[test]
fn test_prop_proofs_irrelevant() {
    let env = Env::new();

    let prop = Rc::new(Term::Sort(Level::Zero));

    // Two identity proofs (same structure)
    let proof1 = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let proof2 = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // Same structure should be defeq
    assert!(
        is_def_eq(&env, proof1, proof2, Transparency::Reducible),
        "Identical proof terms should be defeq"
    );
}

/// Test: Large elimination from Prop is allowed for singleton Prop with Prop fields
#[test]
fn test_large_elim_allowed_for_prop_singleton() {
    let mut env = Env::new();
    let ctx = Context::new();

    // Inductive UnitProp : Prop with constructor mk : UnitProp
    let prop = Rc::new(Term::Sort(Level::Zero));
    let unit_prop = Rc::new(Term::Ind("UnitProp".to_string(), vec![]));
    let ctor = Constructor {
        name: "mk".to_string(),
        ty: unit_prop.clone(),
    };

    let decl = InductiveDecl {
        name: "UnitProp".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors: vec![ctor],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl).expect("Failed to add UnitProp");

    // Recursor into Type 0 should be permitted for singleton Prop
    let rec = Rc::new(Term::Rec(
        "UnitProp".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));

    let result = infer(&env, &ctx, rec);
    assert!(
        result.is_ok(),
        "Large elimination for singleton Prop should be allowed: {:?}",
        result
    );
}

/// Test: Elimination into Prop is always allowed, even for multi-constructor Prop
#[test]
fn test_prop_elim_into_prop_allowed_multi_ctor() {
    let mut env = Env::new();
    let ctx = Context::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let bool_prop = Rc::new(Term::Ind("BoolProp".to_string(), vec![]));
    let ctors = vec![
        Constructor {
            name: "ptrue".to_string(),
            ty: bool_prop.clone(),
        },
        Constructor {
            name: "pfalse".to_string(),
            ty: bool_prop.clone(),
        },
    ];

    let decl = InductiveDecl {
        name: "BoolProp".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors,
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl).expect("Failed to add BoolProp");

    let rec = Rc::new(Term::Rec("BoolProp".to_string(), vec![Level::Zero]));
    let result = infer(&env, &ctx, rec);
    assert!(
        result.is_ok(),
        "Prop elimination into Prop should be allowed for multi-ctor Prop: {:?}",
        result
    );
}

// =============================================================================
// CLASSICAL LOGIC TRACKING (Scaffold)
// =============================================================================

/// Test scaffold: Classical axioms should be tracked
#[test]
fn test_classical_axiom_tracking() {
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));

    // Declare a classical axiom and a non-classical axiom (name should not imply classical)
    let classical_def = Definition::axiom_classical("classical_choice".to_string(), prop.clone());
    env.add_definition(classical_def)
        .expect("Add classical axiom");
    let non_classical_def = Definition::axiom("classical_postulate".to_string(), prop.clone());
    env.add_definition(non_classical_def)
        .expect("Add non-classical axiom");

    // Use the classical axiom
    let mut use_classical_def = Definition::total(
        "use_classical".to_string(),
        prop.clone(),
        Rc::new(Term::Const("classical_choice".to_string(), vec![])),
    );
    use_classical_def.noncomputable = true;
    env.add_definition(use_classical_def)
        .expect("Add use_classical");

    // Use the non-classical axiom
    let mut use_postulate_def = Definition::total(
        "use_postulate".to_string(),
        prop.clone(),
        Rc::new(Term::Const("classical_postulate".to_string(), vec![])),
    );
    use_postulate_def.noncomputable = true;
    env.add_definition(use_postulate_def)
        .expect("Add use_postulate");

    let classical_axiom = env.get_definition("classical_choice").unwrap();
    assert_eq!(
        classical_axiom_dependencies(&env, classical_axiom),
        vec!["classical_choice".to_string()]
    );

    let use_classical = env.get_definition("use_classical").unwrap();
    assert_eq!(
        classical_axiom_dependencies(&env, use_classical),
        vec!["classical_choice".to_string()]
    );

    let use_postulate = env.get_definition("use_postulate").unwrap();
    assert!(classical_axiom_dependencies(&env, use_postulate).is_empty());
}

#[test]
fn test_classical_axiom_dependencies_multiple() {
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));

    env.add_definition(Definition::axiom_classical(
        "Choice".to_string(),
        prop.clone(),
    ))
    .expect("Add Choice");
    env.add_definition(Definition::axiom_classical("EM".to_string(), prop.clone()))
        .expect("Add EM");

    let mut use_choice = Definition::total(
        "use_choice".to_string(),
        prop.clone(),
        Rc::new(Term::Const("Choice".to_string(), vec![])),
    );
    use_choice.noncomputable = true;
    env.add_definition(use_choice).expect("Add use_choice");

    let mut use_em = Definition::total(
        "use_em".to_string(),
        prop.clone(),
        Rc::new(Term::Const("EM".to_string(), vec![])),
    );
    use_em.noncomputable = true;
    env.add_definition(use_em).expect("Add use_em");

    let mut use_both = Definition::total(
        "use_both".to_string(),
        prop.clone(),
        Rc::new(Term::LetE(
            prop.clone(),
            Rc::new(Term::Const("use_choice".to_string(), vec![])),
            Rc::new(Term::Const("use_em".to_string(), vec![])),
        )),
    );
    use_both.noncomputable = true;
    env.add_definition(use_both).expect("Add use_both");

    let deps = classical_axiom_dependencies(&env, env.get_definition("use_both").unwrap());
    assert_eq!(deps, vec!["Choice".to_string(), "EM".to_string()]);
}

/// Test: Constructive proofs should not be marked classical
#[test]
fn test_constructive_unmarked() {
    let env = Env::new();
    let ctx = Context::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let id = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // This should type check without any classical dependency
    let _ = infer(&env, &ctx, id).expect("Constructive term should type check");
}

// =============================================================================
// COPY INSTANCE RESOLUTION TESTS
// =============================================================================

#[test]
fn test_conditional_copy_instance_resolution() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    // Nat : Type 0 (Copy)
    let nat_ref = Term::ind("Nat".to_string());
    let nat_decl = InductiveDecl {
        name: "Nat".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0.clone(),
        ctors: vec![
            Constructor {
                name: "zero".to_string(),
                ty: nat_ref.clone(),
            },
            Constructor {
                name: "succ".to_string(),
                ty: Term::pi(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default),
            },
        ],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(nat_decl).expect("Failed to add Nat");

    // Option A : Type -> Type (Copy if A is Copy)
    let option_ref = Term::ind("Option".to_string());
    let option_ty = Term::pi(type0.clone(), type0.clone(), BinderInfo::Default);
    let none_ty = Term::pi(
        type0.clone(),
        Term::app(option_ref.clone(), Term::var(0)),
        BinderInfo::Default,
    );
    let some_ty = Term::pi(
        type0.clone(),
        Term::pi(
            Term::var(0),
            Term::app(option_ref.clone(), Term::var(1)),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let option_decl = InductiveDecl {
        name: "Option".to_string(),
        univ_params: vec![],
        num_params: 1,
        ty: option_ty,
        ctors: vec![
            Constructor {
                name: "none".to_string(),
                ty: none_ty,
            },
            Constructor {
                name: "some".to_string(),
                ty: some_ty,
            },
        ],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(option_decl)
        .expect("Failed to add Option");

    // List A : Type -> Type (recursive, not Copy)
    let list_ref = Term::ind("List".to_string());
    let list_ty = Term::pi(type0.clone(), type0.clone(), BinderInfo::Default);
    let nil_ty = Term::pi(
        type0.clone(),
        Term::app(list_ref.clone(), Term::var(0)),
        BinderInfo::Default,
    );
    let cons_ty = Term::pi(
        type0.clone(),
        Term::pi(
            Term::var(0),
            Term::pi(
                Term::app(list_ref.clone(), Term::var(1)),
                Term::app(list_ref.clone(), Term::var(2)),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let list_decl = InductiveDecl {
        name: "List".to_string(),
        univ_params: vec![],
        num_params: 1,
        ty: list_ty,
        ctors: vec![
            Constructor {
                name: "nil".to_string(),
                ty: nil_ty,
            },
            Constructor {
                name: "cons".to_string(),
                ty: cons_ty,
            },
        ],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(list_decl).expect("Failed to add List");

    let option_nat = Term::app(option_ref.clone(), nat_ref.clone());
    assert!(
        is_copy_type_in_env(&env, &option_nat),
        "Option Nat should be Copy"
    );

    let list_nat = Term::app(list_ref.clone(), nat_ref);
    assert!(
        !is_copy_type_in_env(&env, &list_nat),
        "List Nat should not be Copy"
    );

    let option_list_nat = Term::app(option_ref, list_nat);
    assert!(
        !is_copy_type_in_env(&env, &option_list_nat),
        "Option (List Nat) should not be Copy"
    );
}

#[test]
fn test_ref_shared_copy_semantics() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    env.add_definition(Definition::axiom("Shared".to_string(), sort1.clone()))
        .expect("Failed to add Shared");
    env.add_definition(Definition::axiom("Mut".to_string(), sort1.clone()))
        .expect("Failed to add Mut");

    let ref_ty = Rc::new(Term::Pi(
        sort1.clone(),
        Rc::new(Term::Pi(
            sort1.clone(),
            sort1.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    env.add_definition(Definition::axiom("Ref".to_string(), ref_ty))
        .expect("Failed to add Ref");
    env.add_definition(Definition::axiom("A".to_string(), sort1.clone()))
        .expect("Failed to add A");

    let const_term = |name: &str| Rc::new(Term::Const(name.to_string(), vec![]));
    let ref_shared = Term::app(
        Term::app(const_term("Ref"), const_term("Shared")),
        const_term("A"),
    );
    let ref_mut = Term::app(
        Term::app(const_term("Ref"), const_term("Mut")),
        const_term("A"),
    );

    assert!(
        is_copy_type_in_env(&env, &ref_shared),
        "Ref Shared A should be Copy"
    );
    assert!(
        !is_copy_type_in_env(&env, &ref_mut),
        "Ref Mut A should not be Copy"
    );
}

#[test]
fn test_ref_label_defeq_distinguishes_labels() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    env.add_definition(Definition::axiom("Shared".to_string(), sort1.clone()))
        .expect("Failed to add Shared");
    env.add_definition(Definition::axiom("Mut".to_string(), sort1.clone()))
        .expect("Failed to add Mut");

    let ref_ty = Rc::new(Term::Pi(
        sort1.clone(),
        Rc::new(Term::Pi(
            sort1.clone(),
            sort1.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    env.add_definition(Definition::axiom("Ref".to_string(), ref_ty))
        .expect("Failed to add Ref");
    env.add_definition(Definition::axiom("A".to_string(), sort1.clone()))
        .expect("Failed to add A");

    let const_term = |name: &str| Rc::new(Term::Const(name.to_string(), vec![]));
    let ref_shared = Term::app(const_term("Ref"), const_term("Shared"));
    let ref_a = Term::app_with_label(ref_shared.clone(), const_term("A"), Some("a".to_string()));
    let ref_b = Term::app_with_label(ref_shared, const_term("A"), Some("b".to_string()));

    assert!(
        !is_def_eq(&env, ref_a, ref_b, Transparency::Reducible),
        "Ref #[a] Shared A should not be defeq to Ref #[b] Shared A"
    );
}

fn double_apply_term(kind: FunctionKind) -> Rc<Term> {
    let ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let f_ty = Rc::new(Term::Pi(ty.clone(), ty.clone(), BinderInfo::Default, kind));
    let inner = Term::app(Rc::new(Term::Var(1)), Rc::new(Term::Var(0)));
    let body = Term::app(Rc::new(Term::Var(1)), inner);
    let lam_x = Rc::new(Term::Lam(ty.clone(), body, BinderInfo::Default, kind));
    Rc::new(Term::Lam(
        f_ty,
        lam_x,
        BinderInfo::Default,
        FunctionKind::Fn,
    ))
}

#[test]
fn test_fn_twice_typechecks() {
    let env = Env::new();
    let ctx = Context::new();
    let term = double_apply_term(FunctionKind::Fn);
    let ty = infer(&env, &ctx, term).expect("Fn repeated call should typecheck");

    match &*ty {
        Term::Pi(dom, _, _, FunctionKind::Fn) => match &**dom {
            Term::Pi(_, _, _, FunctionKind::Fn) => {}
            other => panic!("Expected Fn function type, got {:?}", other),
        },
        other => panic!("Expected Pi type, got {:?}", other),
    }
}

#[test]
fn test_fnmut_twice_typechecks() {
    let env = Env::new();
    let ctx = Context::new();
    let term = double_apply_term(FunctionKind::FnMut);
    let ty = infer(&env, &ctx, term).expect("FnMut repeated call should typecheck");

    match &*ty {
        Term::Pi(dom, _, _, FunctionKind::Fn) => match &**dom {
            Term::Pi(_, _, _, FunctionKind::FnMut) => {}
            other => panic!("Expected FnMut function type, got {:?}", other),
        },
        other => panic!("Expected Pi type, got {:?}", other),
    }
}

#[cfg(test)]
mod property_tests {
    use super::*;

    /// Property: Defeq is reflexive
    #[test]
    fn prop_defeq_reflexive() {
        let env = Env::new();

        let terms = vec![
            Rc::new(Term::Sort(Level::Zero)),
            Rc::new(Term::Lam(
                Rc::new(Term::Sort(Level::Zero)),
                Rc::new(Term::Var(0)),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        ];

        for term in terms {
            assert!(
                is_def_eq(&env, term.clone(), term.clone(), Transparency::Reducible),
                "Defeq must be reflexive"
            );
        }
    }

    /// Property: Defeq is symmetric
    #[test]
    fn prop_defeq_symmetric() {
        let env = Env::new();

        let a = Rc::new(Term::Sort(Level::Zero));
        let b = Rc::new(Term::Sort(Level::Zero));

        if is_def_eq(&env, a.clone(), b.clone(), Transparency::Reducible) {
            assert!(
                is_def_eq(&env, b, a, Transparency::Reducible),
                "Defeq must be symmetric"
            );
        }
    }

    /// Property: Defeq is transitive
    #[test]
    fn prop_defeq_transitive() {
        let env = Env::new();

        let prop = Rc::new(Term::Sort(Level::Zero));
        let id = Rc::new(Term::Lam(
            prop.clone(),
            Rc::new(Term::Var(0)),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let app = Term::app(id, prop.clone());
        let let_term = Rc::new(Term::LetE(
            prop.clone(),
            prop.clone(),
            Rc::new(Term::Var(0)),
        ));

        assert!(is_def_eq(
            &env,
            app.clone(),
            prop.clone(),
            Transparency::Reducible
        ));
        assert!(is_def_eq(
            &env,
            prop.clone(),
            let_term.clone(),
            Transparency::Reducible
        ));
        assert!(
            is_def_eq(&env, app, let_term, Transparency::Reducible),
            "Defeq must be transitive"
        );
    }

    /// Property: Defeq is congruent under application
    #[test]
    fn prop_defeq_congruent_app() {
        let env = Env::new();

        let prop = Rc::new(Term::Sort(Level::Zero));
        let id1 = Rc::new(Term::Lam(
            prop.clone(),
            Rc::new(Term::Var(0)),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));
        let id2 = Rc::new(Term::Lam(
            prop.clone(),
            Rc::new(Term::Var(0)),
            BinderInfo::Default,
            FunctionKind::Fn,
        ));

        assert!(is_def_eq(
            &env,
            id1.clone(),
            id2.clone(),
            Transparency::Reducible
        ));

        let app1 = Term::app(id1, prop.clone());
        let app2 = Term::app(id2, prop);

        assert!(
            is_def_eq(&env, app1, app2, Transparency::Reducible),
            "Defeq must be preserved under application"
        );
    }

    /// Substitution: Var(0) is replaced by the substitution term.
    #[test]
    fn prop_subst_var_replacement() {
        let s = Rc::new(Term::Sort(Level::Zero));
        let v0 = Rc::new(Term::Var(0));
        assert_eq!(v0.subst(0, &s), s);
    }

    /// Substitution: indices above the substitution point shift down.
    #[test]
    fn prop_subst_var_shift_down() {
        let s = Rc::new(Term::Sort(Level::Zero));
        let v2 = Rc::new(Term::Var(2));
        assert_eq!(v2.subst(0, &s), Rc::new(Term::Var(1)));
    }

    /// Substitution under lambda shifts the substitution term.
    #[test]
    fn prop_subst_under_lambda() {
        let prop = Rc::new(Term::Sort(Level::Zero));
        let body = Term::app(Rc::new(Term::Var(1)), Rc::new(Term::Var(0)));
        let lam = Rc::new(Term::Lam(
            prop.clone(),
            body,
            BinderInfo::Default,
            FunctionKind::Fn,
        ));

        let result = lam.subst(0, &prop);
        let expected_body = Term::app(prop.clone(), Rc::new(Term::Var(0)));
        let expected = Rc::new(Term::Lam(
            prop.clone(),
            expected_body,
            BinderInfo::Default,
            FunctionKind::Fn,
        ));

        assert_eq!(result, expected);
    }

    /// Substitution under let binds only in the body.
    #[test]
    fn prop_subst_under_let() {
        let prop = Rc::new(Term::Sort(Level::Zero));
        let term = Rc::new(Term::LetE(
            prop.clone(),
            Rc::new(Term::Var(0)),
            Rc::new(Term::Var(1)),
        ));

        let result = term.subst(0, &prop);
        let expected = Rc::new(Term::LetE(prop.clone(), prop.clone(), prop));

        assert_eq!(result, expected);
    }
}
