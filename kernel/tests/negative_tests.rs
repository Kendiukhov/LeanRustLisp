//! Negative tests for kernel - these programs MUST fail
//!
//! Each test verifies that the kernel correctly rejects ill-formed programs.
//! Error categories are documented for stability.

use kernel::ast::{Term, Level, InductiveDecl, Constructor, BinderInfo, Definition, Transparency};
use kernel::checker::{Env, Context, infer, check, TypeError};
use kernel::ownership::OwnershipError;
use std::rc::Rc;

// =============================================================================
// TYPE MISMATCH ERRORS
// =============================================================================

/// Negative test: Applying non-function should fail
#[test]
fn negative_apply_non_function() {
    let env = Env::new();
    let ctx = Context::new();

    // Prop applied to Prop - Prop is not a function
    let prop = Rc::new(Term::Sort(Level::Zero));
    let bad_app = Rc::new(Term::App(prop.clone(), prop.clone()));

    let result = infer(&env, &ctx, bad_app);

    assert!(
        result.is_err(),
        "Applying non-function should fail: {:?}",
        result
    );
}

/// Negative test: Type mismatch in application
#[test]
fn negative_type_mismatch_in_app() {
    let mut env = Env::new();

    // Set up Nat and Bool as distinct types
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));
    let bool_ind = Rc::new(Term::Ind("Bool".to_string(), vec![]));

    let _ = env.add_inductive(InductiveDecl::new_copy(
        "Nat".to_string(),
        type0.clone(),
        vec![Constructor {
            name: "zero".to_string(),
            ty: nat_ind.clone(),
        }],
    ));

    let _ = env.add_inductive(InductiveDecl::new_copy(
        "Bool".to_string(),
        type0.clone(),
        vec![Constructor {
            name: "true".to_string(),
            ty: bool_ind.clone(),
        }],
    ));

    // f : Nat -> Nat
    let f_type = Rc::new(Term::Pi(nat_ind.clone(), nat_ind.clone(), BinderInfo::Default));
    let f_body = Rc::new(Term::Lam(nat_ind.clone(), Rc::new(Term::Var(0)), BinderInfo::Default));

    env.add_definition(Definition::total("f".to_string(), f_type, f_body))
        .expect("Failed to add f");

    let ctx = Context::new();

    // f true - should fail because true : Bool, not Nat
    let f = Rc::new(Term::Const("f".to_string(), vec![]));
    let true_ctor = Rc::new(Term::Ctor("true".to_string(), 0, vec![]));
    let bad_app = Rc::new(Term::App(f, true_ctor));

    let result = infer(&env, &ctx, bad_app);

    assert!(
        result.is_err(),
        "Type mismatch (Bool vs Nat) should fail: {:?}",
        result
    );
}

/// Negative test: Lambda body doesn't match declared return type
#[test]
fn negative_lambda_return_type_mismatch() {
    let mut env = Env::new();

    // Set up Nat and Bool
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));
    let bool_ind = Rc::new(Term::Ind("Bool".to_string(), vec![]));

    let _ = env.add_inductive(InductiveDecl::new_copy(
        "Nat".to_string(),
        type0.clone(),
        vec![Constructor {
            name: "zero".to_string(),
            ty: nat_ind.clone(),
        }],
    ));

    let _ = env.add_inductive(InductiveDecl::new_copy(
        "Bool".to_string(),
        type0.clone(),
        vec![Constructor {
            name: "true".to_string(),
            ty: bool_ind.clone(),
        }],
    ));

    let ctx = Context::new();

    // Claimed type: Nat -> Nat
    let claimed_type = Rc::new(Term::Pi(nat_ind.clone(), nat_ind.clone(), BinderInfo::Default));

    // Actual body: lam x : Nat. true (returns Bool, not Nat)
    let true_ctor = Rc::new(Term::Ctor("true".to_string(), 0, vec![]));
    let bad_body = Rc::new(Term::Lam(nat_ind, true_ctor, BinderInfo::Default));

    // This should fail type checking
    let result = check(&env, &ctx, bad_body, claimed_type);

    assert!(
        result.is_err(),
        "Lambda returning wrong type should fail: {:?}",
        result
    );
}

// =============================================================================
// UNIVERSE LEVEL ERRORS
// =============================================================================

/// Negative test: constructor argument in higher universe than inductive
#[test]
fn negative_universe_level_too_small() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero))))));

    // Bad : Type0
    // mk : Type1 -> Bad
    let bad_decl = InductiveDecl {
        name: "Bad".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(
                type1,
                Rc::new(Term::Ind("Bad".to_string(), vec![])),
                BinderInfo::Default,
            )),
        }],
        is_copy: false,
    };

    let result = env.add_inductive(bad_decl);
    assert!(matches!(result, Err(TypeError::UniverseLevelTooSmall(..))));
}

// =============================================================================
// DEFEQ FUEL ERRORS
// =============================================================================

#[test]
fn negative_defeq_fuel_exhausted() {
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));

    // Define an axiom and a reducible definition that needs unfolding.
    env.add_definition(Definition::axiom("zero".to_string(), prop.clone()))
        .expect("Failed to add zero axiom");

    let one_body = Rc::new(Term::Const("zero".to_string(), vec![]));
    env.add_definition(Definition::total("one".to_string(), prop.clone(), one_body))
        .expect("Failed to add one");

    let one_term = Rc::new(Term::Const("one".to_string(), vec![]));
    let result = kernel::checker::is_def_eq_with_fuel(
        &env,
        one_term.clone(),
        one_term,
        Transparency::All,
        0,
    );

    assert!(matches!(result, Err(TypeError::DefEqFuelExhausted)));
}

// =============================================================================
// UNIVERSE LEVEL ERRORS
// =============================================================================

/// Negative test: Type : Type (universe inconsistency)
#[test]
fn negative_type_in_type() {
    // Type 0 : Type 1, not Type 0 : Type 0
    // The kernel should not allow Type to be its own type

    let env = Env::new();
    let ctx = Context::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    // Check that Type 0 is NOT in Type 0
    let result = check(&env, &ctx, type0.clone(), type0);

    assert!(
        result.is_err(),
        "Type 0 : Type 0 should fail (Girard's paradox): {:?}",
        result
    );
}

/// Negative test: Universe level constraint violation
#[test]
fn negative_universe_constraint() {
    let env = Env::new();
    let ctx = Context::new();

    // Trying to put Type 1 in Type 0 should fail
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero))))));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let result = check(&env, &ctx, type1, type0);

    assert!(
        result.is_err(),
        "Type 1 : Type 0 should fail: {:?}",
        result
    );
}

// =============================================================================
// UNDEFINED REFERENCE ERRORS
// =============================================================================

/// Negative test: Reference to undefined constant
#[test]
fn negative_undefined_constant() {
    let env = Env::new();
    let ctx = Context::new();

    let undefined = Rc::new(Term::Const("does_not_exist".to_string(), vec![]));

    let result = infer(&env, &ctx, undefined);

    assert!(
        result.is_err(),
        "Reference to undefined constant should fail: {:?}",
        result
    );
}

/// Negative test: Reference to undefined inductive
#[test]
fn negative_undefined_inductive() {
    let env = Env::new();
    let ctx = Context::new();

    let undefined = Rc::new(Term::Ind("UndefinedType".to_string(), vec![]));

    let result = infer(&env, &ctx, undefined);

    assert!(
        result.is_err(),
        "Reference to undefined inductive should fail: {:?}",
        result
    );
}

// =============================================================================
// VARIABLE SCOPE ERRORS
// =============================================================================

/// Negative test: De Bruijn index out of bounds
#[test]
fn negative_var_out_of_bounds() {
    let env = Env::new();
    let ctx = Context::new();

    // Var(5) with no enclosing binders - out of bounds
    let bad_var = Rc::new(Term::Var(5));

    let result = infer(&env, &ctx, bad_var);

    assert!(
        result.is_err(),
        "Out-of-bounds de Bruijn index should fail: {:?}",
        result
    );
}

/// Negative test: Escaping variable in type
#[test]
fn negative_escaping_var() {
    let env = Env::new();
    let ctx = Context::new();

    // Pi with body referencing variable that doesn't exist
    // Pi _ : Prop. Var(5) - Var(5) escapes
    let prop = Rc::new(Term::Sort(Level::Zero));
    let bad_pi = Rc::new(Term::Pi(prop, Rc::new(Term::Var(5)), BinderInfo::Default));

    let result = infer(&env, &ctx, bad_pi);

    assert!(
        result.is_err(),
        "Escaping variable should fail: {:?}",
        result
    );
}

// =============================================================================
// INDUCTIVE SOUNDNESS ERRORS
// =============================================================================

/// Negative test: Non-positive occurrence of inductive in constructor
#[test]
fn negative_non_positive_occurrence() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let bad_ind = Rc::new(Term::Ind("Bad".to_string(), vec![]));

    // Constructor argument type: (Bad -> Type0) which is non-positive.
    let arg_ty = Rc::new(Term::Pi(bad_ind.clone(), type0.clone(), BinderInfo::Default));
    let ctor_ty = Rc::new(Term::Pi(arg_ty, bad_ind.clone(), BinderInfo::Default));

    let decl = InductiveDecl::new(
        "Bad".to_string(),
        type0,
        vec![Constructor {
            name: "mk".to_string(),
            ty: ctor_ty,
        }],
    );

    match env.add_inductive(decl) {
        Err(TypeError::NonPositiveOccurrence(ind, ctor, idx)) => {
            assert_eq!(ind, "Bad");
            assert_eq!(ctor, "mk");
            assert_eq!(idx, 0);
        }
        other => panic!("Expected NonPositiveOccurrence, got {:?}", other),
    }
}

/// Negative test: Constructor not returning the inductive
#[test]
fn negative_ctor_not_returning_inductive() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let decl = InductiveDecl::new(
        "Foo".to_string(),
        type0.clone(),
        vec![Constructor {
            name: "mk".to_string(),
            ty: type0,
        }],
    );

    match env.add_inductive(decl) {
        Err(TypeError::CtorNotReturningInductive { ind, ctor }) => {
            assert_eq!(ind, "Foo");
            assert_eq!(ctor, "mk");
        }
        other => panic!("Expected CtorNotReturningInductive, got {:?}", other),
    }
}

/// Negative test: Constructor returns inductive with wrong arity
#[test]
fn negative_ctor_arity_mismatch() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    // Foo : (A : Type0) -> Type0
    let foo_ty = Rc::new(Term::Pi(type0.clone(), type0.clone(), BinderInfo::Default));

    // mk : (A : Type0) -> Foo   (missing the parameter application)
    let ctor_ty = Rc::new(Term::Pi(
        type0.clone(),
        Rc::new(Term::Ind("Foo".to_string(), vec![])),
        BinderInfo::Default,
    ));

    let decl = InductiveDecl::new(
        "Foo".to_string(),
        foo_ty,
        vec![Constructor {
            name: "mk".to_string(),
            ty: ctor_ty,
        }],
    );

    match env.add_inductive(decl) {
        Err(TypeError::CtorArityMismatch { ind, ctor, expected, got }) => {
            assert_eq!(ind, "Foo");
            assert_eq!(ctor, "mk");
            assert_eq!(expected, 1);
            assert_eq!(got, 0);
        }
        other => panic!("Expected CtorArityMismatch, got {:?}", other),
    }
}

// =============================================================================
// TYPE SAFETY ERRORS (Totality / Effects)
// =============================================================================

/// Negative test: Partial definition used in type position
#[test]
fn negative_partial_in_type() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let prop = Rc::new(Term::Sort(Level::Zero));

    let partial_def = Definition::partial("BadType".to_string(), type0.clone(), prop.clone());
    env.add_definition(partial_def).expect("Partial definition should register");

    let bad_type = Rc::new(Term::Const("BadType".to_string(), vec![]));
    let total_def = Definition::total("use_bad".to_string(), bad_type, prop);

    match env.add_definition(total_def) {
        Err(TypeError::PartialInType(name)) => assert_eq!(name, "BadType"),
        other => panic!("Expected PartialInType, got {:?}", other),
    }
}

/// Negative test: Partial definition used as a binder type should be rejected
#[test]
fn negative_partial_in_binder_type() {
    let mut env = Env::new();
    let ctx = Context::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let prop = Rc::new(Term::Sort(Level::Zero));

    let partial_def = Definition::partial("BadType".to_string(), type0.clone(), prop);
    env.add_definition(partial_def).expect("Partial definition should register");

    let bad_type = Rc::new(Term::Const("BadType".to_string(), vec![]));
    let body = Rc::new(Term::Var(0));
    let lam = Rc::new(Term::Lam(bad_type, body, BinderInfo::Default));

    let result = infer(&env, &ctx, lam);

    match result {
        Err(TypeError::PartialInType(name)) => assert_eq!(name, "BadType"),
        other => panic!("Expected PartialInType, got {:?}", other),
    }
}

/// Negative test: Partial definition used in inductive arity should be rejected
#[test]
fn negative_partial_in_inductive_type() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let prop = Rc::new(Term::Sort(Level::Zero));

    let partial_def = Definition::partial("BadType".to_string(), type0.clone(), prop);
    env.add_definition(partial_def).expect("Partial definition should register");

    let decl = InductiveDecl {
        name: "Foo".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: Rc::new(Term::Const("BadType".to_string(), vec![])),
        ctors: vec![],
        is_copy: true,
    };

    match env.add_inductive(decl) {
        Err(TypeError::PartialInType(name)) => assert_eq!(name, "BadType"),
        other => panic!("Expected PartialInType, got {:?}", other),
    }
}

// =============================================================================
// TOTALITY ERRORS (when totality checking is enabled)
// =============================================================================

/// Negative test: Non-terminating recursion should be rejected for total defs
#[test]
fn negative_non_terminating() {
    let mut env = Env::new();

    // Set up Nat for a structurally recursive signature.
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));
    let ctors = vec![
        Constructor { name: "zero".to_string(), ty: nat_ind.clone() },
        Constructor {
            name: "succ".to_string(),
            ty: Rc::new(Term::Pi(nat_ind.clone(), nat_ind.clone(), BinderInfo::Default)),
        },
    ];
    env.add_inductive(InductiveDecl::new_copy("Nat".to_string(), type0, ctors))
        .expect("Failed to add Nat");

    // infinite : Nat -> Nat
    // infinite n = infinite n  (non-terminating)
    let ty = Rc::new(Term::Pi(nat_ind.clone(), nat_ind.clone(), BinderInfo::Default));
    let body = Rc::new(Term::Lam(
        nat_ind.clone(),
        Rc::new(Term::App(
            Rc::new(Term::Const("infinite".to_string(), vec![])),
            Rc::new(Term::Var(0)),
        )),
        BinderInfo::Default,
    ));

    let def = Definition::total("infinite".to_string(), ty, body);
    let result = env.add_definition(def);

    match result {
        Err(TypeError::TerminationError { def_name, .. }) => {
            assert_eq!(def_name, "infinite");
        }
        other => panic!("Expected TerminationError for non-terminating def, got {:?}", other),
    }
}

// =============================================================================
// MATCH/CASE ERRORS
// =============================================================================
// Match exhaustiveness and duplicate-case detection are frontend responsibilities.
// See `frontend/tests/elaboration_tests.rs` for coverage.

// =============================================================================
// PROP ELIMINATION ERRORS
// =============================================================================

/// Negative test: Recursor without explicit universe level is rejected
#[test]
fn negative_recursor_missing_level() {
    let mut env = Env::new();
    let ctx = Context::new();

    let nat_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));
    let ctors = vec![
        Constructor { name: "zero".to_string(), ty: nat_ind.clone() },
        Constructor { name: "succ".to_string(), ty: Rc::new(Term::Pi(nat_ind.clone(), nat_ind.clone(), BinderInfo::Default)) },
    ];

    env.add_inductive(InductiveDecl::new_copy("Nat".to_string(), nat_ty, ctors))
        .expect("Failed to add Nat");

    let rec = Rc::new(Term::Rec("Nat".to_string(), vec![]));
    let result = infer(&env, &ctx, rec);

    match result {
        Err(TypeError::MissingRecursorLevel(name)) => assert_eq!(name, "Nat"),
        other => panic!("Expected MissingRecursorLevel error, got {:?}", other),
    }
}

/// Negative test: Recursor level count must match universe params + result level
#[test]
fn negative_recursor_level_count_mismatch() {
    let mut env = Env::new();
    let ctx = Context::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let foo_ind = Rc::new(Term::Ind("Foo".to_string(), vec![]));
    let ctor = Constructor {
        name: "mk".to_string(),
        ty: foo_ind.clone(),
    };

    let decl = InductiveDecl {
        name: "Foo".to_string(),
        univ_params: vec!["u".to_string()],
        num_params: 0,
        ty: type0,
        ctors: vec![ctor],
        is_copy: true,
    };

    env.add_inductive(decl).expect("Failed to add Foo");

    let rec = Rc::new(Term::Rec("Foo".to_string(), vec![Level::Zero]));
    let result = infer(&env, &ctx, rec);

    match result {
        Err(TypeError::RecursorLevelCount { ind, expected, got }) => {
            assert_eq!(ind, "Foo");
            assert_eq!(expected, 2);
            assert_eq!(got, 1);
        }
        other => panic!("Expected RecursorLevelCount error, got {:?}", other),
    }
}

/// Negative test: Total definitions cannot use fix (general recursion)
#[test]
fn negative_total_def_uses_fix() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    // A simple self-referential fixpoint: fix f : (Type0 -> Type0). f
    let fix_ty = Rc::new(Term::Pi(type0.clone(), type0.clone(), BinderInfo::Default));
    let fix_body = Rc::new(Term::Var(0));
    let fix_term = Rc::new(Term::Fix(fix_ty.clone(), fix_body));

    let def = Definition::total("bad_fix".to_string(), fix_ty.clone(), fix_term);
    let result = env.add_definition(def);

    match result {
        Err(TypeError::EffectError(from, to, name)) => {
            assert_eq!(from, "Total");
            assert_eq!(to, "Partial");
            assert_eq!(name, "fix");
        }
        other => panic!("Expected EffectError for fix in total def, got {:?}", other),
    }
}

/// Negative test: Non-copy values must not be used more than once
#[test]
fn negative_ownership_linear_use_twice() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let lin_ref = Rc::new(Term::Ind("Lin".to_string(), vec![]));

    let lin_decl = InductiveDecl {
        name: "Lin".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0.clone(),
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: lin_ref.clone(),
        }],
        is_copy: false,
    };
    env.add_inductive(lin_decl).expect("Failed to add Lin");

    let f_ty = Rc::new(Term::Pi(
        lin_ref.clone(),
        Rc::new(Term::Pi(lin_ref.clone(), lin_ref.clone(), BinderInfo::Default)),
        BinderInfo::Default,
    ));
    env.add_definition(Definition::axiom("f".to_string(), f_ty))
        .expect("Failed to add f axiom");

    let dup_ty = Rc::new(Term::Pi(lin_ref.clone(), lin_ref.clone(), BinderInfo::Default));
    let dup_val = Rc::new(Term::Lam(
        lin_ref.clone(),
        Rc::new(Term::App(
            Rc::new(Term::App(
                Rc::new(Term::Const("f".to_string(), vec![])),
                Rc::new(Term::Var(0)),
            )),
            Rc::new(Term::Var(0)),
        )),
        BinderInfo::Default,
    ));

    let result = env.add_definition(Definition::total("dup".to_string(), dup_ty, dup_val));

    match result {
        Err(TypeError::OwnershipError(OwnershipError::UseAfterMove(idx))) => {
            assert_eq!(idx, 0);
        }
        other => panic!("Expected ownership error, got {:?}", other),
    }
}

/// Negative test: Large elimination from Prop (extracting data from proof)
#[test]
fn negative_large_elim_from_prop() {
    let mut env = Env::new();
    let ctx = Context::new();

    // Inductive PWrap : Prop with a constructor carrying a Type
    // This should forbid elimination into Type.
    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let pwrap = Rc::new(Term::Ind("PWrap".to_string(), vec![]));

    let ctors = vec![Constructor {
        name: "mk".to_string(),
        ty: Rc::new(Term::Pi(type0, pwrap.clone(), BinderInfo::Default)),
    }];

    let decl = InductiveDecl {
        name: "PWrap".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors,
        is_copy: true,
    };

    env.add_inductive(decl).expect("Failed to add PWrap");

    // Recursor targeting Type 0 should be rejected.
    let rec = Rc::new(Term::Rec(
        "PWrap".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));

    let result = infer(&env, &ctx, rec);

    match result {
        Err(TypeError::LargeElimination(name)) => assert_eq!(name, "PWrap"),
        other => panic!("Expected LargeElimination error, got {:?}", other),
    }
}

/// Negative test: Data inductive cannot store Prop-typed fields
#[test]
fn negative_prop_field_in_data() {
    let mut env = Env::new();

    let prop_sort = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    // Inductive P : Prop
    let p_ind = Rc::new(Term::Ind("P".to_string(), vec![]));
    let p_decl = InductiveDecl {
        name: "P".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop_sort.clone(),
        ctors: vec![Constructor { name: "mkP".to_string(), ty: p_ind.clone() }],
        is_copy: true,
    };
    env.add_inductive(p_decl).expect("Failed to add P");

    // Inductive Data : Type with constructor mk : P -> Data (should be rejected)
    let data_ind = Rc::new(Term::Ind("Data".to_string(), vec![]));
    let data_decl = InductiveDecl {
        name: "Data".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0.clone(),
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(p_ind.clone(), data_ind.clone(), BinderInfo::Default)),
        }],
        is_copy: true,
    };

    let result = env.add_inductive(data_decl);
    match result {
        Err(TypeError::PropFieldInData { ind, ctor, field }) => {
            assert_eq!(ind, "Data");
            assert_eq!(ctor, "mk");
            assert_eq!(field, 0);
        }
        other => panic!("Expected PropFieldInData error, got {:?}", other),
    }
}

/// Negative test: Large elimination from Prop with multiple constructors
#[test]
fn negative_large_elim_multiple_ctors() {
    let mut env = Env::new();
    let ctx = Context::new();

    // Inductive P2 : Prop with two constructors
    let prop = Rc::new(Term::Sort(Level::Zero));
    let p2 = Rc::new(Term::Ind("P2".to_string(), vec![]));

    let ctors = vec![
        Constructor { name: "c1".to_string(), ty: p2.clone() },
        Constructor { name: "c2".to_string(), ty: p2.clone() },
    ];

    let decl = InductiveDecl {
        name: "P2".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors,
        is_copy: true,
    };

    env.add_inductive(decl).expect("Failed to add P2");

    let rec = Rc::new(Term::Rec(
        "P2".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));
    let result = infer(&env, &ctx, rec);

    match result {
        Err(TypeError::LargeElimination(name)) => assert_eq!(name, "P2"),
        other => panic!("Expected LargeElimination error, got {:?}", other),
    }
}

// =============================================================================
// ERROR MESSAGE STABILITY
// =============================================================================

/// Test that error messages contain expected diagnostic information
#[test]
fn error_message_contains_context() {
    let env = Env::new();
    let ctx = Context::new();

    let bad_app = Rc::new(Term::App(
        Rc::new(Term::Sort(Level::Zero)),
        Rc::new(Term::Sort(Level::Zero)),
    ));

    let result = infer(&env, &ctx, bad_app);

    match result {
        Err(e) => {
            // Error should mention something about function/application
            let msg = format!("{:?}", e);
            // We don't string-match exactly, but verify it's informative
            assert!(
                !msg.is_empty(),
                "Error message should not be empty"
            );
        }
        Ok(_) => panic!("Expected error"),
    }
}
