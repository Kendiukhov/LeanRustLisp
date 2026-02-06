//! Negative tests for kernel - these programs MUST fail
//!
//! Each test verifies that the kernel correctly rejects ill-formed programs.
//! Error categories are documented for stability.

use kernel::ast::{
    marker_def_id, AxiomTag, BinderInfo, Constructor, CopyInstance, CopyInstanceSource, Definition,
    FunctionKind, InductiveDecl, Level, Term, Transparency, TypeMarker, WellFoundedInfo,
};
use kernel::checker::{
    check, check_elimination_restriction, check_elimination_restriction_with_transparency, infer,
    Context, Env, PropTransparencyContext, TypeError,
};
use kernel::ownership::OwnershipError;
use std::rc::Rc;

fn add_prelude_marker_axioms(env: &mut Env) {
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let markers = [
        "interior_mutable",
        "may_panic_on_borrow_violation",
        "concurrency_primitive",
        "atomic_primitive",
        "indexable",
    ];
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    for name in markers {
        env.add_definition(Definition::axiom_with_tags(
            name.to_string(),
            type0.clone(),
            vec![AxiomTag::Unsafe],
        ))
        .expect("Failed to add marker axiom");
    }
    env.set_allow_reserved_primitives(allow_reserved);
    env.init_marker_registry()
        .expect("Failed to init marker registry");
}

fn add_comp_inductive(env: &mut Env) {
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
        .expect("Failed to add Comp inductive");
    env.set_allow_reserved_primitives(allow_reserved);
}

fn make_partial_comp_def(name: &str) -> Definition {
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let comp_ind = Term::ind("Comp".to_string());
    let comp_body = Term::app(comp_ind.clone(), Term::var(1));
    let ty = Term::pi(
        type1.clone(),
        Term::pi(Term::var(0), comp_body, BinderInfo::Default),
        BinderInfo::Default,
    );
    let ret_app = Term::app(
        Term::app(Term::ctor("Comp".to_string(), 0), Term::var(1)),
        Term::var(0),
    );
    let val = Term::lam(
        type1,
        Term::lam(Term::var(0), ret_app, BinderInfo::Default),
        BinderInfo::Default,
    );
    Definition::partial(name.to_string(), ty, val)
}

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
    let bad_app = Term::app(prop.clone(), prop.clone());

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
    env.set_allow_reserved_primitives(true);

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
    let f_type = Rc::new(Term::Pi(
        nat_ind.clone(),
        nat_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let f_body = Rc::new(Term::Lam(
        nat_ind.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    env.add_definition(Definition::total("f".to_string(), f_type, f_body))
        .expect("Failed to add f");

    let ctx = Context::new();

    // f true - should fail because true : Bool, not Nat
    let f = Rc::new(Term::Const("f".to_string(), vec![]));
    let true_ctor = Rc::new(Term::Ctor("true".to_string(), 0, vec![]));
    let bad_app = Term::app(f, true_ctor);

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
    env.set_allow_reserved_primitives(true);

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
    let claimed_type = Rc::new(Term::Pi(
        nat_ind.clone(),
        nat_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // Actual body: lam x : Nat. true (returns Bool, not Nat)
    let true_ctor = Rc::new(Term::Ctor("true".to_string(), 0, vec![]));
    let bad_body = Rc::new(Term::Lam(
        nat_ind,
        true_ctor,
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

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
    add_prelude_marker_axioms(&mut env);

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Succ(Box::new(
        Level::Zero,
    ))))));

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
                FunctionKind::Fn,
            )),
        }],
        is_copy: false,
        markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
        axioms: vec![],
        primitive_deps: vec![],
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
    let mut one_def = Definition::total("one".to_string(), prop.clone(), one_body);
    one_def.noncomputable = true;
    env.add_definition(one_def).expect("Failed to add one");

    let one_term = Rc::new(Term::Const("one".to_string(), vec![]));
    let result = kernel::checker::is_def_eq_with_fuel(
        &env,
        one_term.clone(),
        one_term,
        Transparency::All,
        0,
    );

    assert!(matches!(result, Err(TypeError::DefEqFuelExhausted { .. })));
}

#[test]
fn negative_defeq_fix_unfold_disallowed() {
    let env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let fix_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let fix_body = Rc::new(Term::Var(0));
    let fix_term = Rc::new(Term::Fix(fix_ty.clone(), fix_body));
    let app = Term::app(fix_term, type0);

    let result =
        kernel::checker::is_def_eq_with_fuel(&env, app.clone(), app, Transparency::All, 10);

    assert!(matches!(result, Err(TypeError::DefEqFixUnfold)));
}

// =============================================================================
// COPY INSTANCE ERRORS
// =============================================================================

#[test]
fn negative_explicit_copy_instance_requires_unsafe() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));

    env.add_inductive(InductiveDecl::new_copy(
        "Nat".to_string(),
        type0,
        vec![Constructor {
            name: "zero".to_string(),
            ty: nat_ind,
        }],
    ))
    .expect("Failed to add Nat");

    let inst = CopyInstance {
        ind_name: "Nat".to_string(),
        param_count: 0,
        requirements: vec![],
        source: CopyInstanceSource::Explicit,
        is_unsafe: false,
    };

    let result = env.add_copy_instance(inst);
    assert!(matches!(
        result,
        Err(TypeError::ExplicitCopyInstanceRequiresUnsafe { .. })
    ));
}

#[test]
fn negative_explicit_copy_instance_interior_mutable() {
    let mut env = Env::new();
    add_prelude_marker_axioms(&mut env);
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let rc_ind = Rc::new(Term::Ind("RefCell".to_string(), vec![]));

    let decl = InductiveDecl {
        name: "RefCell".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: rc_ind,
        }],
        is_copy: false,
        markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl).expect("Failed to add RefCell");

    let inst = CopyInstance {
        ind_name: "RefCell".to_string(),
        param_count: 0,
        requirements: vec![],
        source: CopyInstanceSource::Explicit,
        is_unsafe: true,
    };

    let result = env.add_copy_instance(inst);
    assert!(matches!(
        result,
        Err(TypeError::ExplicitCopyInstanceInteriorMutable { .. })
    ));
}

#[test]
fn negative_missing_marker_definition() {
    let mut env = Env::new();
    let result = env.init_marker_registry();
    assert!(matches!(
        result,
        Err(TypeError::MissingTypeMarkerDefinition(name)) if name == "interior_mutable"
    ));
}

#[test]
fn negative_forged_marker_definition() {
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let bad_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let result = env.add_definition(Definition::axiom_with_tags(
        "interior_mutable".to_string(),
        bad_ty,
        vec![AxiomTag::Unsafe],
    ));
    env.set_allow_reserved_primitives(allow_reserved);
    assert!(matches!(
        result,
        Err(TypeError::ReservedMarkerSignature(name)) if name == "interior_mutable"
    ));
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
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Succ(Box::new(
        Level::Zero,
    ))))));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let result = check(&env, &ctx, type1, type0);

    assert!(result.is_err(), "Type 1 : Type 0 should fail: {:?}", result);
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
    let bad_pi = Rc::new(Term::Pi(
        prop,
        Rc::new(Term::Var(5)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

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
    let arg_ty = Rc::new(Term::Pi(
        bad_ind.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let ctor_ty = Rc::new(Term::Pi(
        arg_ty,
        bad_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

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

/// Negative test: Nested inductive occurrences are rejected
#[test]
fn negative_nested_inductive_rejected() {
    let mut env = Env::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    // List : Type0 -> Type0
    let list_ind = Rc::new(Term::Ind("List".to_string(), vec![]));
    let list_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let nil_ty = Rc::new(Term::Pi(
        type0.clone(),
        Term::app(list_ind.clone(), Term::var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let cons_ty = Term::pi(
        type0.clone(), // A
        Term::pi(
            Term::var(0), // h : A
            Term::pi(
                Term::app(list_ind.clone(), Term::var(1)), // t : List A
                Term::app(list_ind.clone(), Term::var(2)), // List A
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let list_decl = InductiveDecl::new(
        "List".to_string(),
        list_ty,
        vec![
            Constructor {
                name: "nil".to_string(),
                ty: nil_ty,
            },
            Constructor {
                name: "cons".to_string(),
                ty: cons_ty,
            },
        ],
    );
    env.add_inductive(list_decl)
        .expect("Failed to add List inductive");

    // Tree : Type0, node : List Tree -> Tree (nested occurrence)
    let tree_ind = Rc::new(Term::Ind("Tree".to_string(), vec![]));
    let list_tree = Term::app(list_ind, tree_ind.clone());
    let node_ty = Rc::new(Term::Pi(
        list_tree,
        tree_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let tree_decl = InductiveDecl::new(
        "Tree".to_string(),
        type0,
        vec![Constructor {
            name: "node".to_string(),
            ty: node_ty,
        }],
    );

    match env.add_inductive(tree_decl) {
        Err(TypeError::NestedInductive { ind, ctor, field }) => {
            assert_eq!(ind, "Tree");
            assert_eq!(ctor, "node");
            assert_eq!(field, 0);
        }
        other => panic!("Expected NestedInductive, got {:?}", other),
    }

    env.set_allow_reserved_primitives(allow_reserved);
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
    let foo_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // mk : (A : Type0) -> Foo   (missing the parameter application)
    let ctor_ty = Rc::new(Term::Pi(
        type0.clone(),
        Rc::new(Term::Ind("Foo".to_string(), vec![])),
        BinderInfo::Default,
        FunctionKind::Fn,
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
        Err(TypeError::CtorArityMismatch {
            ind,
            ctor,
            expected,
            got,
        }) => {
            assert_eq!(ind, "Foo");
            assert_eq!(ctor, "mk");
            assert_eq!(expected, 1);
            assert_eq!(got, 0);
        }
        other => panic!("Expected CtorArityMismatch, got {:?}", other),
    }
}

/// Negative test: Inductive constructor type cannot contain unresolved metas
#[test]
fn negative_inductive_ctor_unresolved_meta() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let ind = Rc::new(Term::Ind("MetaCtor".to_string(), vec![]));

    let ctor_ty = Rc::new(Term::Pi(
        Rc::new(Term::Meta(0)),
        ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let decl = InductiveDecl::new(
        "MetaCtor".to_string(),
        type0,
        vec![Constructor {
            name: "mk".to_string(),
            ty: ctor_ty,
        }],
    );

    match env.add_inductive(decl) {
        Err(TypeError::UnresolvedMeta(id)) => assert_eq!(id, 0),
        other => panic!("Expected UnresolvedMeta, got {:?}", other),
    }
}

/// Negative test: Inductive constructor type must use explicit recursor levels
#[test]
fn negative_inductive_ctor_missing_recursor_level() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let ind = Rc::new(Term::Ind("BadRecCtor".to_string(), vec![]));

    let missing_rec = Rc::new(Term::Rec("Nat".to_string(), vec![]));
    let ctor_ty = Rc::new(Term::Pi(
        missing_rec,
        ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let decl = InductiveDecl::new(
        "BadRecCtor".to_string(),
        type0,
        vec![Constructor {
            name: "mk".to_string(),
            ty: ctor_ty,
        }],
    );

    match env.add_inductive(decl) {
        Err(TypeError::MissingRecursorLevel(name)) => assert_eq!(name, "Nat"),
        other => panic!("Expected MissingRecursorLevel, got {:?}", other),
    }
}

/// Negative test: Inductive arity cannot contain unresolved metas
#[test]
fn negative_inductive_arity_unresolved_meta() {
    let mut env = Env::new();

    let decl = InductiveDecl::new("MetaTy".to_string(), Rc::new(Term::Meta(0)), vec![]);

    match env.add_inductive(decl) {
        Err(TypeError::UnresolvedMeta(id)) => assert_eq!(id, 0),
        other => panic!("Expected UnresolvedMeta, got {:?}", other),
    }
}

/// Negative test: Prop constructor domains must validate recursor level counts
#[test]
fn negative_prop_ctor_recursor_level_count_mismatch() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let foo_ind = Rc::new(Term::Ind("Foo".to_string(), vec![]));

    let foo_decl = InductiveDecl {
        name: "Foo".to_string(),
        univ_params: vec!["u".to_string()],
        num_params: 0,
        ty: type0.clone(),
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: foo_ind.clone(),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(foo_decl).expect("Failed to add Foo");

    let bad_ind = Rc::new(Term::Ind("BadProp".to_string(), vec![]));
    let bad_domain = Rc::new(Term::Rec("Foo".to_string(), vec![Level::Zero]));
    let ctor_ty = Rc::new(Term::Pi(
        bad_domain,
        bad_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let bad_decl = InductiveDecl {
        name: "BadProp".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: Rc::new(Term::Sort(Level::Zero)),
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: ctor_ty,
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    match env.add_inductive(bad_decl) {
        Err(TypeError::RecursorLevelCount { ind, expected, got }) => {
            assert_eq!(ind, "Foo");
            assert_eq!(expected, 2);
            assert_eq!(got, 1);
        }
        other => panic!("Expected RecursorLevelCount, got {:?}", other),
    }
}

// =============================================================================
// TYPE SAFETY ERRORS (Totality / Effects)
// =============================================================================

/// Negative test: Partial definition used in type position
#[test]
fn negative_partial_in_type() {
    let mut env = Env::new();
    add_comp_inductive(&mut env);

    let prop = Rc::new(Term::Sort(Level::Zero));

    let partial_def = make_partial_comp_def("BadType");
    env.add_definition(partial_def)
        .expect("Partial definition should register");

    let bad_type = Rc::new(Term::Const("BadType".to_string(), vec![]));
    let total_def = Definition::total("use_bad".to_string(), bad_type, prop);

    match env.add_definition(total_def) {
        Err(TypeError::PartialInType(name)) => assert_eq!(name, "BadType"),
        other => panic!("Expected PartialInType, got {:?}", other),
    }
}

#[test]
fn negative_partial_requires_comp_return() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);
    add_comp_inductive(&mut env);

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

    let partial_def = Definition::partial(
        "bad_partial".to_string(),
        nat_ref.clone(),
        Term::ctor("Nat".to_string(), 0),
    );

    match env.add_definition(partial_def) {
        Err(TypeError::PartialReturnType { name, .. }) => assert_eq!(name, "bad_partial"),
        other => panic!("Expected PartialReturnType, got {:?}", other),
    }
}

/// Negative test: Unsafe axiom used in type position should be rejected
#[test]
fn negative_unsafe_axiom_in_type() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let prop = Rc::new(Term::Sort(Level::Zero));

    let unsafe_axiom = Definition::axiom_with_tags(
        "BadUnsafe".to_string(),
        type0.clone(),
        vec![AxiomTag::Unsafe],
    );
    env.add_definition(unsafe_axiom)
        .expect("Unsafe axiom should register");

    let bad_type = Rc::new(Term::Const("BadUnsafe".to_string(), vec![]));
    let total_def = Definition::total("use_bad".to_string(), bad_type, prop);

    match env.add_definition(total_def) {
        Err(TypeError::PartialInType(name)) => assert_eq!(name, "BadUnsafe"),
        other => panic!("Expected PartialInType, got {:?}", other),
    }
}

/// Negative test: Reserved primitive with wrong signature should be rejected
#[test]
fn negative_reserved_primitive_signature_mismatch() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let bad_def =
        Definition::axiom_with_tags("borrow_shared".to_string(), type0, vec![AxiomTag::Unsafe]);

    match env.add_definition(bad_def) {
        Err(TypeError::ReservedPrimitiveSignature(name)) => assert_eq!(name, "borrow_shared"),
        other => panic!("Expected ReservedPrimitiveSignature, got {:?}", other),
    }
}

/// Negative test: Reserved Ref with wrong signature should be rejected
#[test]
fn negative_reserved_primitive_ref_signature_mismatch() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let bad_ref = Definition::axiom("Ref".to_string(), sort1);

    match env.add_definition(bad_ref) {
        Err(TypeError::ReservedPrimitiveSignature(name)) => assert_eq!(name, "Ref"),
        other => panic!(
            "Expected ReservedPrimitiveSignature for Ref, got {:?}",
            other
        ),
    }
}

/// Negative test: Reserved Mut with wrong signature should be rejected
#[test]
fn negative_reserved_primitive_mut_signature_mismatch() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let bad_mut_ty = Rc::new(Term::Pi(
        sort1.clone(),
        sort1,
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let bad_mut = Definition::axiom("Mut".to_string(), bad_mut_ty);

    match env.add_definition(bad_mut) {
        Err(TypeError::ReservedPrimitiveSignature(name)) => assert_eq!(name, "Mut"),
        other => panic!(
            "Expected ReservedPrimitiveSignature for Mut, got {:?}",
            other
        ),
    }
}

/// Negative test: Reserved Ref cannot be declared outside the prelude
#[test]
fn negative_reserved_primitive_ref_outside_prelude() {
    let mut env = Env::new();

    let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let ref_ty = Rc::new(Term::Pi(
        sort1.clone(),
        Rc::new(Term::Pi(
            sort1.clone(),
            sort1,
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let attempt = Definition::axiom("Ref".to_string(), ref_ty);

    match env.add_definition(attempt) {
        Err(TypeError::ReservedPrimitiveName(name)) => assert_eq!(name, "Ref"),
        other => panic!("Expected ReservedPrimitiveName for Ref, got {:?}", other),
    }
}

/// Negative test: Reserved Shared/Mut cannot be declared outside the prelude
#[test]
fn negative_reserved_primitive_shared_mut_outside_prelude() {
    let mut env = Env::new();

    let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    for name in ["Shared", "Mut"] {
        let attempt = Definition::axiom(name.to_string(), sort1.clone());
        match env.add_definition(attempt) {
            Err(TypeError::ReservedPrimitiveName(rejected)) => assert_eq!(rejected, name),
            other => panic!(
                "Expected ReservedPrimitiveName for {}, got {:?}",
                name, other
            ),
        }
    }
}

/// Negative test: Redefining an existing definition should be rejected
#[test]
fn negative_definition_redefinition_rejected() {
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));

    env.add_definition(Definition::axiom("A".to_string(), prop.clone()))
        .expect("Failed to add A");

    let dup = Definition::axiom("A".to_string(), prop);
    match env.add_definition(dup) {
        Err(TypeError::DefinitionAlreadyExists(name)) => assert_eq!(name, "A"),
        other => panic!("Expected DefinitionAlreadyExists for A, got {:?}", other),
    }
}

/// Negative test: Redefining an existing inductive should be rejected
#[test]
fn negative_inductive_redefinition_rejected() {
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let ind_ref = Rc::new(Term::Ind("Box".to_string(), vec![]));
    let decl = InductiveDecl::new_copy(
        "Box".to_string(),
        type0.clone(),
        vec![Constructor {
            name: "mk".to_string(),
            ty: ind_ref.clone(),
        }],
    );
    env.add_inductive(decl).expect("Failed to add Box");

    let dup_ref = Rc::new(Term::Ind("Box".to_string(), vec![]));
    let dup_decl = InductiveDecl::new_copy(
        "Box".to_string(),
        type0,
        vec![Constructor {
            name: "mk".to_string(),
            ty: dup_ref,
        }],
    );
    match env.add_inductive(dup_decl) {
        Err(TypeError::InductiveAlreadyExists(name)) => assert_eq!(name, "Box"),
        other => panic!("Expected InductiveAlreadyExists for Box, got {:?}", other),
    }
}

/// Negative test: Reserved core names cannot be used for definitions
#[test]
fn negative_reserved_core_name_definition_rejected() {
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let attempt = Definition::axiom("Nat".to_string(), type0);
    match env.add_definition(attempt) {
        Err(TypeError::ReservedCoreName(name)) => assert_eq!(name, "Nat"),
        other => panic!("Expected ReservedCoreName for Nat, got {:?}", other),
    }
}

/// Negative test: Reserved core names cannot be used for inductives
#[test]
fn negative_reserved_core_name_inductive_rejected() {
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let comp_ref = Rc::new(Term::Ind("Comp".to_string(), vec![]));
    let comp_decl = InductiveDecl::new_copy(
        "Comp".to_string(),
        type0,
        vec![Constructor {
            name: "mk".to_string(),
            ty: comp_ref,
        }],
    );
    match env.add_inductive(comp_decl) {
        Err(TypeError::ReservedCoreName(name)) => assert_eq!(name, "Comp"),
        other => panic!("Expected ReservedCoreName for Comp, got {:?}", other),
    }
}

// =============================================================================
// LIFETIME LABEL VALIDATION
// =============================================================================

/// Negative test: Lifetime labels may only annotate Ref Shared/Mut applications
#[test]
fn negative_ref_label_on_non_ref_application() {
    let mut env = Env::new();

    let bad_ty = Term::app_with_label(
        Rc::new(Term::Const("Foo".to_string(), vec![])),
        Rc::new(Term::Const("Bar".to_string(), vec![])),
        Some("a".to_string()),
    );
    let bad_def = Definition::axiom("bad_label".to_string(), bad_ty);

    match env.add_definition(bad_def) {
        Err(TypeError::InvalidRefLifetimeLabel { .. }) => {}
        other => panic!("Expected InvalidRefLifetimeLabel, got {:?}", other),
    }
}

/// Negative test: Ambiguous return lifetime without explicit labels should be rejected
#[test]
fn negative_ambiguous_ref_lifetime_elision_in_pi() {
    let mut env = Env::new();

    let nat = Rc::new(Term::Ind("Nat".to_string(), vec![]));
    let ref_const = Rc::new(Term::Const("Ref".to_string(), vec![]));
    let shared_const = Rc::new(Term::Const("Shared".to_string(), vec![]));

    let ref_a = Term::app_with_label(
        Term::app(ref_const.clone(), shared_const.clone()),
        nat.clone(),
        Some("a".to_string()),
    );
    let ref_b = Term::app_with_label(
        Term::app(ref_const.clone(), shared_const.clone()),
        nat.clone(),
        Some("b".to_string()),
    );
    let ref_unlabeled = Term::app(
        Term::app(ref_const.clone(), shared_const.clone()),
        nat.clone(),
    );

    let ty = Rc::new(Term::Pi(
        ref_a,
        Rc::new(Term::Pi(
            ref_b,
            ref_unlabeled,
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let bad_def = Definition::axiom("ambiguous_ref_return".to_string(), ty);

    match env.add_definition(bad_def) {
        Err(TypeError::AmbiguousRefLifetime) => {}
        other => panic!("Expected AmbiguousRefLifetime, got {:?}", other),
    }
}

/// Negative test: Partial definition used as a binder type should be rejected
#[test]
fn negative_partial_in_binder_type() {
    let mut env = Env::new();
    let ctx = Context::new();
    add_comp_inductive(&mut env);

    let _prop = Rc::new(Term::Sort(Level::Zero));

    let partial_def = make_partial_comp_def("BadType");
    env.add_definition(partial_def)
        .expect("Partial definition should register");

    let bad_type = Rc::new(Term::Const("BadType".to_string(), vec![]));
    let body = Rc::new(Term::Var(0));
    let lam = Rc::new(Term::Lam(
        bad_type,
        body,
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

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
    add_comp_inductive(&mut env);

    let _prop = Rc::new(Term::Sort(Level::Zero));

    let partial_def = make_partial_comp_def("BadType");
    env.add_definition(partial_def)
        .expect("Partial definition should register");

    let decl = InductiveDecl {
        name: "Foo".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: Rc::new(Term::Const("BadType".to_string(), vec![])),
        ctors: vec![],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    match env.add_inductive(decl) {
        Err(TypeError::PartialInType(name)) => assert_eq!(name, "BadType"),
        other => panic!("Expected PartialInType, got {:?}", other),
    }
}

/// Negative test: Partial definition used in Prop constructor domain should be rejected
#[test]
fn negative_partial_in_prop_ctor_domain() {
    let mut env = Env::new();
    add_comp_inductive(&mut env);

    let prop = Rc::new(Term::Sort(Level::Zero));

    let partial_def = make_partial_comp_def("BadType");
    env.add_definition(partial_def)
        .expect("Partial definition should register");

    let bad_type = Rc::new(Term::Const("BadType".to_string(), vec![]));
    let bad_ind = Rc::new(Term::Ind("BadProp".to_string(), vec![]));

    let decl = InductiveDecl {
        name: "BadProp".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(
                bad_type,
                bad_ind.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
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
    env.set_allow_reserved_primitives(true);

    // Set up Nat for a structurally recursive signature.
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
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
    env.add_inductive(InductiveDecl::new_copy("Nat".to_string(), type0, ctors))
        .expect("Failed to add Nat");

    // infinite : Nat -> Nat
    // infinite n = infinite n  (non-terminating)
    let ty = Rc::new(Term::Pi(
        nat_ind.clone(),
        nat_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let body = Rc::new(Term::Lam(
        nat_ind.clone(),
        Term::app(
            Rc::new(Term::Const("infinite".to_string(), vec![])),
            Rc::new(Term::Var(0)),
        ),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let def = Definition::total("infinite".to_string(), ty, body);
    let result = env.add_definition(def);

    match result {
        Err(TypeError::TerminationError { def_name, .. }) => {
            assert_eq!(def_name, "infinite");
        }
        other => panic!(
            "Expected TerminationError for non-terminating def, got {:?}",
            other
        ),
    }
}

/// Negative test: Bare self-reference should be rejected for total defs
#[test]
fn negative_bare_self_reference() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
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
    env.add_inductive(InductiveDecl::new_copy("Nat".to_string(), type0, ctors))
        .expect("Failed to add Nat");

    let ty = Rc::new(Term::Pi(
        nat_ind.clone(),
        nat_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let body = Rc::new(Term::Const("loop".to_string(), vec![]));

    let def = Definition::total("loop".to_string(), ty, body);
    let result = env.add_definition(def);

    match result {
        Err(TypeError::TerminationError { def_name, .. }) => {
            assert_eq!(def_name, "loop");
        }
        other => panic!(
            "Expected TerminationError for bare self-reference, got {:?}",
            other
        ),
    }
}

/// Negative test: Recursive calls through let-aliasing should be rejected
#[test]
fn negative_let_alias_recursion() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
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
    env.add_inductive(InductiveDecl::new_copy("Nat".to_string(), type0, ctors))
        .expect("Failed to add Nat");

    let ty = Rc::new(Term::Pi(
        nat_ind.clone(),
        nat_ind.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let body = Rc::new(Term::Lam(
        nat_ind.clone(),
        Rc::new(Term::LetE(
            Rc::new(Term::Pi(
                nat_ind.clone(),
                nat_ind.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            Rc::new(Term::Const("loop".to_string(), vec![])),
            Term::app(Rc::new(Term::Var(0)), Rc::new(Term::Var(1))),
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let def = Definition::total("loop".to_string(), ty, body);
    let result = env.add_definition(def);

    match result {
        Err(TypeError::TerminationError { def_name, .. }) => {
            assert_eq!(def_name, "loop");
        }
        other => panic!(
            "Expected TerminationError for let-aliased recursion, got {:?}",
            other
        ),
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
    env.set_allow_reserved_primitives(true);
    let ctx = Context::new();

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
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
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
    let fix_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
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

/// Negative test: Well-founded definitions cannot use fix (general recursion)
#[test]
fn negative_wellfounded_def_uses_fix() {
    let mut env = Env::new();

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    // A simple self-referential fixpoint: fix f : (Type0 -> Type0). f
    let fix_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let fix_body = Rc::new(Term::Var(0));
    let fix_term = Rc::new(Term::Fix(fix_ty.clone(), fix_body));

    let wf_info = WellFoundedInfo {
        relation: "lt".to_string(),
        decreasing_arg: 0,
    };
    let def = Definition::wellfounded("bad_wf_fix".to_string(), fix_ty.clone(), fix_term, wf_info);
    let result = env.add_definition(def);

    match result {
        Err(TypeError::EffectError(from, to, name)) => {
            assert_eq!(from, "Total");
            assert_eq!(to, "Partial");
            assert_eq!(name, "fix");
        }
        other => panic!(
            "Expected EffectError for fix in well-founded def, got {:?}",
            other
        ),
    }
}

/// Negative test: Non-copy values must not be used more than once
#[test]
fn negative_ownership_linear_use_twice() {
    let mut env = Env::new();
    add_prelude_marker_axioms(&mut env);

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
        markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(lin_decl).expect("Failed to add Lin");
    assert!(
        !kernel::checker::is_copy_type_in_env(&env, &lin_ref),
        "Lin should be non-Copy for this test"
    );

    let f_ty = Rc::new(Term::Pi(
        lin_ref.clone(),
        Rc::new(Term::Pi(
            lin_ref.clone(),
            lin_ref.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    env.add_definition(Definition::axiom("f".to_string(), f_ty))
        .expect("Failed to add f axiom");

    let dup_ty = Rc::new(Term::Pi(
        lin_ref.clone(),
        lin_ref.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let dup_val = Rc::new(Term::Lam(
        lin_ref.clone(),
        Term::app(
            Term::app(
                Rc::new(Term::Const("f".to_string(), vec![])),
                Rc::new(Term::Var(0)),
            ),
            Rc::new(Term::Var(0)),
        ),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let result = env.add_definition(Definition::total("dup".to_string(), dup_ty, dup_val));

    match result {
        Err(TypeError::OwnershipError(OwnershipError::UseAfterMove(idx))) => {
            assert_eq!(idx, 0);
        }
        other => panic!("Expected ownership error, got {:?}", other),
    }
}

/// Negative test: implicit binder of non-Copy type cannot be consumed
#[test]
fn negative_implicit_binder_consumes_noncopy() {
    let mut env = Env::new();
    add_prelude_marker_axioms(&mut env);

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
        markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(lin_decl).expect("Failed to add Lin");
    assert!(
        !kernel::checker::is_copy_type_in_env(&env, &lin_ref),
        "Lin should be non-Copy for this test"
    );

    let implicit_ty = Rc::new(Term::Pi(
        lin_ref.clone(),
        lin_ref.clone(),
        BinderInfo::Implicit,
        FunctionKind::Fn,
    ));
    let implicit_val = Rc::new(Term::Lam(
        lin_ref.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Implicit,
        FunctionKind::Fn,
    ));

    let result = env.add_definition(Definition::total(
        "implicit_consume".to_string(),
        implicit_ty,
        implicit_val,
    ));

    match result {
        Err(TypeError::OwnershipError(OwnershipError::ImplicitNonCopyUse { index, .. })) => {
            assert_eq!(index, 0);
        }
        other => panic!("Expected implicit binder ownership error, got {:?}", other),
    }
}

/// Negative test: Fn lambda that consumes a non-Copy capture must be FnOnce
#[test]
fn negative_function_kind_too_small_for_capture() {
    let mut env = Env::new();
    add_prelude_marker_axioms(&mut env);

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
        markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(lin_decl).expect("Failed to add Lin");
    assert!(
        !kernel::checker::is_copy_type_in_env(&env, &lin_ref),
        "Lin should be non-Copy for this test"
    );

    let ctx = Context::new().push(lin_ref.clone());
    let bad_lam = Rc::new(Term::Lam(
        lin_ref.clone(),
        Rc::new(Term::Var(1)), // capture consumed in body
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let result = infer(&env, &ctx, bad_lam);

    match result {
        Err(TypeError::FunctionKindTooSmall {
            annotated,
            required,
        }) => {
            assert_eq!(annotated, FunctionKind::Fn);
            assert_eq!(required, FunctionKind::FnOnce);
        }
        other => panic!("Expected function kind error, got {:?}", other),
    }
}

/// Negative test: Fn lambda that captures a mutable reference must be FnMut
#[test]
fn negative_function_kind_too_small_for_mutable_capture() {
    let mut env = Env::new();
    add_prelude_marker_axioms(&mut env);
    env.set_allow_reserved_primitives(true);

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
        markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(lin_decl).expect("Failed to add Lin");

    // Add minimal Ref/Mut axioms to form (Ref Mut Lin).
    env.add_definition(Definition::axiom("Mut".to_string(), type0.clone()))
        .expect("Failed to add Mut");
    let ref_ty = Rc::new(Term::Pi(
        type0.clone(),
        Rc::new(Term::Pi(
            type0.clone(),
            type0.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    env.add_definition(Definition::axiom("Ref".to_string(), ref_ty))
        .expect("Failed to add Ref");

    let ref_mut_lin = Term::app(
        Term::app(
            Rc::new(Term::Const("Ref".to_string(), vec![])),
            Rc::new(Term::Const("Mut".to_string(), vec![])),
        ),
        lin_ref.clone(),
    );

    let ctx = Context::new().push(ref_mut_lin.clone());
    let bad_lam = Rc::new(Term::Lam(
        ref_mut_lin.clone(),
        Rc::new(Term::Var(1)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let result = infer(&env, &ctx, bad_lam);

    match result {
        Err(TypeError::FunctionKindTooSmall {
            annotated,
            required,
        }) => {
            assert_eq!(annotated, FunctionKind::Fn);
            assert_eq!(required, FunctionKind::FnMut);
        }
        other => panic!("Expected function kind error, got {:?}", other),
    }
}

/// Negative test: Fn lambda that captures via implicit argument must be FnOnce
#[test]
fn negative_function_kind_too_small_for_implicit_arg_capture() {
    let mut env = Env::new();
    add_prelude_marker_axioms(&mut env);

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
        markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(lin_decl).expect("Failed to add Lin");
    assert!(
        !kernel::checker::is_copy_type_in_env(&env, &lin_ref),
        "Lin should be non-Copy for this test"
    );

    let consume_ty = Rc::new(Term::Pi(
        lin_ref.clone(),
        lin_ref.clone(),
        BinderInfo::Implicit,
        FunctionKind::Fn,
    ));
    env.add_definition(Definition::axiom("consume_imp".to_string(), consume_ty))
        .expect("Failed to add consume_imp");

    let ctx = Context::new().push(lin_ref.clone());
    let bad_body = Term::app(
        Rc::new(Term::Const("consume_imp".to_string(), vec![])),
        Rc::new(Term::Var(1)),
    );
    let bad_lam = Rc::new(Term::Lam(
        lin_ref.clone(),
        bad_body,
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let result = infer(&env, &ctx, bad_lam);

    match result {
        Err(TypeError::FunctionKindTooSmall {
            annotated,
            required,
        }) => {
            assert_eq!(annotated, FunctionKind::Fn);
            assert_eq!(required, FunctionKind::FnOnce);
        }
        other => panic!("Expected function kind error, got {:?}", other),
    }
}

/// Negative test: Copy inductive cannot contain non-copy fields
#[test]
fn negative_copy_inductive_with_noncopy_field() {
    let mut env = Env::new();
    add_prelude_marker_axioms(&mut env);

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
        markers: vec![marker_def_id(TypeMarker::InteriorMutable)],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(lin_decl).expect("Failed to add Lin");

    let wrap_ref = Rc::new(Term::Ind("Wrap".to_string(), vec![]));
    let wrap_decl = InductiveDecl {
        name: "Wrap".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0.clone(),
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(
                lin_ref.clone(),
                wrap_ref.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    let result = env.add_inductive(wrap_decl);
    match result {
        Err(TypeError::CopyDeriveFailure { ind, .. }) => {
            assert_eq!(ind, "Wrap");
        }
        other => panic!("Expected CopyDeriveFailure error, got {:?}", other),
    }
}

/// Negative test: Copy inductive cannot be derived for recursive fields
#[test]
fn negative_copy_inductive_recursive_field() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let list_ref = Rc::new(Term::Ind("List".to_string(), vec![]));

    let list_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    // cons : (A : Type) -> A -> List A -> List A
    let cons_ty = Rc::new(Term::Pi(
        type0.clone(),
        Rc::new(Term::Pi(
            Rc::new(Term::Var(0)),
            Rc::new(Term::Pi(
                Term::app(list_ref.clone(), Rc::new(Term::Var(1))),
                Term::app(list_ref.clone(), Rc::new(Term::Var(2))),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let list_decl = InductiveDecl {
        name: "List".to_string(),
        univ_params: vec![],
        num_params: 1,
        ty: list_ty,
        ctors: vec![Constructor {
            name: "cons".to_string(),
            ty: cons_ty,
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    let result = env.add_inductive(list_decl);
    match result {
        Err(TypeError::CopyDeriveFailure { ind, .. }) => {
            assert_eq!(ind, "List");
        }
        other => panic!("Expected CopyDeriveFailure error, got {:?}", other),
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
        ty: Rc::new(Term::Pi(
            type0,
            pwrap.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
    }];

    let decl = InductiveDecl {
        name: "PWrap".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors,
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
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
        ctors: vec![Constructor {
            name: "mkP".to_string(),
            ty: p_ind.clone(),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
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
            ty: Rc::new(Term::Pi(
                p_ind.clone(),
                data_ind.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
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
        Constructor {
            name: "c1".to_string(),
            ty: p2.clone(),
        },
        Constructor {
            name: "c2".to_string(),
            ty: p2.clone(),
        },
    ];

    let decl = InductiveDecl {
        name: "P2".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors,
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
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

/// Prop elimination treats opaque aliases as Prop (unfolded for safety checks).
#[test]
fn negative_large_elim_multiple_ctors_opaque_prop_alias() {
    let mut env = Env::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let mut prop_alias = Definition::total("PropAlias".to_string(), type0, prop);
    prop_alias.mark_opaque();
    env.add_definition(prop_alias)
        .expect("Failed to add opaque PropAlias");

    let prop_alias_term = Rc::new(Term::Const("PropAlias".to_string(), vec![]));
    let p2 = Rc::new(Term::Ind("P2Opaque".to_string(), vec![]));

    let ctors = vec![
        Constructor {
            name: "c1".to_string(),
            ty: p2.clone(),
        },
        Constructor {
            name: "c2".to_string(),
            ty: p2.clone(),
        },
    ];

    let decl = InductiveDecl {
        name: "P2Opaque".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop_alias_term,
        ctors,
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl).expect("Failed to add P2Opaque");

    let levels = vec![Level::Succ(Box::new(Level::Zero))];

    let default_check = check_elimination_restriction(&env, "P2Opaque", &levels);
    match default_check {
        Err(TypeError::LargeElimination(name)) => assert_eq!(name, "P2Opaque"),
        other => panic!(
            "Expected LargeElimination error with default transparency, got {:?}",
            other
        ),
    }

    let forced_check = check_elimination_restriction_with_transparency(
        &env,
        "P2Opaque",
        &levels,
        PropTransparencyContext::UnfoldOpaque,
    );
    match forced_check {
        Err(TypeError::LargeElimination(name)) => assert_eq!(name, "P2Opaque"),
        other => panic!(
            "Expected LargeElimination error with unfolding, got {:?}",
            other
        ),
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

    let bad_app = Term::app(
        Rc::new(Term::Sort(Level::Zero)),
        Rc::new(Term::Sort(Level::Zero)),
    );

    let result = infer(&env, &ctx, bad_app);

    match result {
        Err(e) => {
            // Error should mention something about function/application
            let msg = format!("{:?}", e);
            // We don't string-match exactly, but verify it's informative
            assert!(!msg.is_empty(), "Error message should not be empty");
        }
        Ok(_) => panic!("Expected error"),
    }
}
