//! Kernel-level invariants mapped to README promises.

use kernel::ast::{
    AxiomTag, BinderInfo, Constructor, Definition, FunctionKind, InductiveDecl, Level, Term,
    Transparency,
};
use kernel::checker::{
    axiom_dependencies_with_tag, check_mutual_termination, check_wellfounded_termination, infer,
    is_copy_type_in_env, is_def_eq, is_def_eq_in_ctx, is_def_eq_with_fuel, whnf, Context,
    DefEqFuelContext, Env, TerminationErrorDetails, TypeError, WellFoundedError, WellFoundedSpec,
};
use std::rc::Rc;

fn add_nat(env: &mut Env) -> Rc<Term> {
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let nat_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ref = Rc::new(Term::Ind("Nat".to_string(), vec![]));
    let nat_decl = InductiveDecl {
        name: "Nat".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: nat_ty,
        ctors: vec![
            Constructor {
                name: "zero".to_string(),
                ty: nat_ref.clone(),
            },
            Constructor {
                name: "succ".to_string(),
                ty: Rc::new(Term::Pi(
                    nat_ref.clone(),
                    nat_ref.clone(),
                    BinderInfo::Default,
                    FunctionKind::Fn,
                )),
            },
        ],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(nat_decl)
        .expect("Nat inductive should be accepted");
    env.set_allow_reserved_primitives(allow_reserved);
    nat_ref
}

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

fn comp_of(ty: Rc<Term>) -> Rc<Term> {
    Term::app(Term::ind("Comp".to_string()), ty)
}

fn comp_ret(ty: Rc<Term>, val: Rc<Term>) -> Rc<Term> {
    Term::app(Term::app(Term::ctor("Comp".to_string(), 0), ty), val)
}

fn add_lt(env: &mut Env, nat_ref: &Rc<Term>) {
    let prop = Rc::new(Term::Sort(Level::Zero));
    let lt_ty = Rc::new(Term::Pi(
        nat_ref.clone(),
        Rc::new(Term::Pi(
            nat_ref.clone(),
            prop,
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    env.add_definition(Definition::axiom("lt".to_string(), lt_ty))
        .expect("Failed to add lt axiom");
}

fn add_acc(env: &mut Env) -> Rc<Term> {
    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let acc_ind = Rc::new(Term::Ind("Acc".to_string(), vec![]));

    let a_var = Term::var(0);
    let r_ty = Term::pi(
        a_var.clone(),
        Term::pi(a_var.shift(0, 1), prop.clone(), BinderInfo::Default),
        BinderInfo::Default,
    );
    let acc_ty = Term::pi(
        type0.clone(),
        Term::pi(
            r_ty,
            Term::pi(Term::var(1), prop.clone(), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let acc_app = |a: Rc<Term>, r: Rc<Term>, x: Rc<Term>| {
        Term::app(Term::app(Term::app(acc_ind.clone(), a), r), x)
    };

    let intro_ty = Term::pi(
        type0.clone(),
        Term::pi(
            Term::pi(
                Term::var(0),
                Term::pi(Term::var(1), prop.clone(), BinderInfo::Default),
                BinderInfo::Default,
            ),
            Term::pi(
                Term::var(1),
                Term::pi(
                    Term::pi(
                        Term::var(2),
                        Term::pi(
                            Term::app(Term::app(Term::var(2), Term::var(0)), Term::var(1)),
                            acc_app(Term::var(4), Term::var(3), Term::var(1)),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    acc_app(Term::var(3), Term::var(2), Term::var(1)),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    env.add_inductive(InductiveDecl {
        name: "Acc".to_string(),
        univ_params: vec![],
        num_params: 2,
        ty: acc_ty,
        ctors: vec![Constructor {
            name: "intro".to_string(),
            ty: intro_ty,
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    })
    .expect("Acc inductive should be accepted");
    acc_ind
}

#[test]
fn readme_total_defs_normalize() {
    let mut env = Env::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let id_body = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let id_ty = Rc::new(Term::Pi(
        prop.clone(),
        prop.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    env.add_definition(Definition::total("id".to_string(), id_ty, id_body.clone()))
        .expect("Failed to add total id");

    let id_const = Rc::new(Term::Const("id".to_string(), vec![]));
    let reduced = whnf(&env, id_const.clone(), Transparency::Reducible)
        .expect("whnf should succeed for total def");
    match &*reduced {
        Term::Lam(_, _, _, FunctionKind::Fn) => {}
        other => panic!("Expected total def to normalize to lambda, got {:?}", other),
    }
    assert!(
        is_def_eq(&env, id_const, id_body, Transparency::Reducible),
        "Total definition should be defeq to its body"
    );
}

#[test]
fn readme_defeq_transparency_boundaries() {
    // README promise: Defeq respects transparency levels and keeps opaque defs closed unless forced.
    let mut env = Env::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let id_body = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let id_ty = Rc::new(Term::Pi(
        prop.clone(),
        prop.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    env.add_definition(Definition::total(
        "id".to_string(),
        id_ty.clone(),
        id_body.clone(),
    ))
    .expect("Failed to add id");

    let id_const = Rc::new(Term::Const("id".to_string(), vec![]));
    assert!(
        !is_def_eq(&env, id_const.clone(), id_body.clone(), Transparency::None),
        "Transparency::None should not unfold definitions"
    );
    assert!(
        is_def_eq(
            &env,
            id_const.clone(),
            id_body.clone(),
            Transparency::Reducible
        ),
        "Transparency::Reducible should unfold transparent definitions"
    );
    assert!(
        is_def_eq(&env, id_const, id_body.clone(), Transparency::All),
        "Transparency::All should unfold transparent definitions"
    );

    let mut opaque = Definition::total("opaque_id".to_string(), id_ty, id_body);
    opaque.transparency = Transparency::None;
    env.add_definition(opaque).expect("Failed to add opaque_id");

    let opaque_const = Rc::new(Term::Const("opaque_id".to_string(), vec![]));
    assert!(
        !is_def_eq(
            &env,
            opaque_const.clone(),
            Rc::new(Term::Lam(
                prop.clone(),
                Rc::new(Term::Var(0)),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            Transparency::Reducible
        ),
        "Opaque definitions should stay closed under Transparency::Reducible"
    );
    assert!(
        is_def_eq(
            &env,
            opaque_const,
            Rc::new(Term::Lam(
                prop,
                Rc::new(Term::Var(0)),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            Transparency::All
        ),
        "Transparency::All should unfold opaque definitions"
    );
}

#[test]
fn readme_defeq_zeta_nested_respects_transparency() {
    // README promise: Zeta reduces let-bound terms in nested lambdas, delta unfolding still obeys transparency.
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));
    let fn_ty = Rc::new(Term::Pi(
        prop.clone(),
        prop.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let secret_body = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let mut secret = Definition::total("secret".to_string(), fn_ty.clone(), secret_body);
    secret.transparency = Transparency::None;
    env.add_definition(secret).expect("Failed to add secret");

    let secret_const = Rc::new(Term::Const("secret".to_string(), vec![]));
    let let_nested = Rc::new(Term::Lam(
        prop.clone(),
        Rc::new(Term::LetE(
            fn_ty,
            secret_const.clone(),
            Term::app(Rc::new(Term::Var(0)), Rc::new(Term::Var(1))),
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let zeta_only = Rc::new(Term::Lam(
        prop.clone(),
        Term::app(secret_const.clone(), Rc::new(Term::Var(0))),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let eta_target = Rc::new(Term::Lam(
        prop,
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    assert!(
        is_def_eq(&env, let_nested.clone(), zeta_only, Transparency::None),
        "Zeta should reduce lets under lambdas even with Transparency::None"
    );
    assert!(
        !is_def_eq(
            &env,
            let_nested.clone(),
            eta_target.clone(),
            Transparency::Reducible
        ),
        "Opaque defs inside zeta should not unfold under Transparency::Reducible"
    );
    assert!(
        is_def_eq(&env, let_nested, eta_target, Transparency::All),
        "Transparency::All should allow delta after zeta in nested terms"
    );
}

#[test]
fn readme_defeq_eta_dependent_function() {
    // README promise: Eta holds for dependent functions in context.
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let b_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    env.add_definition(Definition::axiom("B".to_string(), b_ty))
        .expect("Failed to add B");

    let ctx = Context::new().push(type0.clone()); // A : Type0
    let dep_ty = Rc::new(Term::Pi(
        Rc::new(Term::Var(0)), // A
        Term::app(
            Rc::new(Term::Const("B".to_string(), vec![])),
            Rc::new(Term::Var(0)),
        ), // B x
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let ctx = ctx.push(dep_ty); // f : (x : A) -> B x

    let f = Rc::new(Term::Var(0));
    let eta = Rc::new(Term::Lam(
        Rc::new(Term::Var(1)),                                   // domain A
        Term::app(Rc::new(Term::Var(1)), Rc::new(Term::Var(0))), // f x
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let result = is_def_eq_in_ctx(&env, &ctx, eta, f, Transparency::All);
    assert!(
        matches!(result, Ok(true)),
        "Dependent eta should hold in context: {:?}",
        result
    );
}

#[test]
fn readme_defeq_fuel_exhaustion_context() {
    // README promise: Defeq fuel exhaustion reports context for debugging.
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));

    env.add_definition(Definition::axiom("zero".to_string(), prop.clone()))
        .expect("Failed to add zero");
    let mut one_def = Definition::total(
        "one".to_string(),
        prop,
        Rc::new(Term::Const("zero".to_string(), vec![])),
    );
    one_def.noncomputable = true;
    env.add_definition(one_def).expect("Failed to add one");

    let one = Rc::new(Term::Const("one".to_string(), vec![]));
    let result = is_def_eq_with_fuel(&env, one.clone(), one.clone(), Transparency::All, 0);

    match result {
        Err(TypeError::DefEqFuelExhausted { context }) => match context {
            DefEqFuelContext::DefEq {
                left,
                right,
                transparency,
                fuel: _,
                fuel_detail,
            } => {
                assert_eq!(left, one.clone());
                assert_eq!(right, one);
                assert_eq!(transparency, Transparency::All);
                let detail = fuel_detail.expect("Expected fuel detail");
                assert!(
                    detail.recent_defs.iter().any(|name| name == "one"),
                    "Expected fuel detail to mention unfolding 'one': {:?}",
                    detail
                );
            }
            other => panic!("Expected DefEq context, got {:?}", other),
        },
        other => panic!("Expected DefEqFuelExhausted, got {:?}", other),
    }
}

#[test]
fn readme_partial_defs_cannot_appear_in_types() {
    let mut env = Env::new();
    add_comp(&mut env);

    let prop = Rc::new(Term::Sort(Level::Zero));
    let nat_ref = add_nat(&mut env);

    env.add_definition(Definition::partial(
        "BadType".to_string(),
        comp_of(nat_ref.clone()),
        comp_ret(nat_ref.clone(), Term::ctor("Nat".to_string(), 0)),
    ))
    .expect("Failed to add partial BadType");

    let bad_ty = Rc::new(Term::Const("BadType".to_string(), vec![]));
    let total_def = Definition::total("use_bad".to_string(), bad_ty, prop);

    match env.add_definition(total_def) {
        Err(TypeError::PartialInType(name)) => assert_eq!(name, "BadType"),
        other => panic!("Expected PartialInType for BadType, got {:?}", other),
    }
}

#[test]
fn readme_total_cannot_call_partial() {
    let mut env = Env::new();
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    add_comp(&mut env);

    env.add_definition(Definition::axiom("U".to_string(), type1))
        .expect("Failed to add U axiom");
    env.add_definition(Definition::axiom(
        "u".to_string(),
        Rc::new(Term::Const("U".to_string(), vec![])),
    ))
    .expect("Failed to add u axiom");

    let u_ty = Rc::new(Term::Const("U".to_string(), vec![]));
    let u_val = Rc::new(Term::Const("u".to_string(), vec![]));
    let mut partial_val = Definition::partial(
        "partial_val".to_string(),
        comp_of(u_ty.clone()),
        comp_ret(u_ty.clone(), u_val.clone()),
    );
    partial_val.noncomputable = true;
    env.add_definition(partial_val)
        .expect("Failed to add partial definition");

    let total_def = Definition::total(
        "total_uses_partial".to_string(),
        comp_of(u_ty),
        Rc::new(Term::Const("partial_val".to_string(), vec![])),
    );
    match env.add_definition(total_def) {
        Err(TypeError::EffectError(from, to, name)) => {
            assert_eq!(from, "Total");
            assert_eq!(to, "Partial");
            assert_eq!(name, "partial_val");
        }
        other => panic!("Expected EffectError for total->partial, got {:?}", other),
    }
}

#[test]
fn readme_shared_refs_are_copy() {
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
    env.add_definition(Definition::axiom("A".to_string(), sort1))
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
fn readme_safe_code_cannot_call_unsafe() {
    let mut env = Env::new();
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    add_comp(&mut env);

    env.add_definition(Definition::axiom("U".to_string(), type1))
        .expect("Failed to add U axiom");
    env.add_definition(Definition::axiom(
        "u".to_string(),
        Rc::new(Term::Const("U".to_string(), vec![])),
    ))
    .expect("Failed to add u axiom");
    env.add_definition(Definition::unsafe_def(
        "danger".to_string(),
        Rc::new(Term::Const("U".to_string(), vec![])),
        Rc::new(Term::Const("u".to_string(), vec![])),
    ))
    .expect("Failed to add unsafe definition");

    let total_def = Definition::total(
        "safe_total".to_string(),
        Rc::new(Term::Const("U".to_string(), vec![])),
        Rc::new(Term::Const("danger".to_string(), vec![])),
    );
    match env.add_definition(total_def) {
        Err(TypeError::EffectError(from, to, name)) => {
            assert_eq!(from, "Total");
            assert_eq!(to, "Unsafe");
            assert_eq!(name, "danger");
        }
        other => panic!("Expected EffectError for total->unsafe, got {:?}", other),
    }

    let u_ty = Rc::new(Term::Const("U".to_string(), vec![]));
    let partial_def = Definition::partial(
        "safe_partial".to_string(),
        comp_of(u_ty.clone()),
        comp_ret(u_ty, Rc::new(Term::Const("danger".to_string(), vec![]))),
    );
    match env.add_definition(partial_def) {
        Err(TypeError::EffectError(from, to, name)) => {
            assert_eq!(from, "Partial");
            assert_eq!(to, "Unsafe");
            assert_eq!(name, "danger");
        }
        other => panic!("Expected EffectError for partial->unsafe, got {:?}", other),
    }
}

#[test]
fn readme_effect_boundaries_chain() {
    // README promise: effect boundaries are enforced across definition chains.
    let mut env = Env::new();
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    add_comp(&mut env);

    env.add_definition(Definition::axiom("U".to_string(), type1))
        .expect("Failed to add U axiom");
    env.add_definition(Definition::axiom(
        "u".to_string(),
        Rc::new(Term::Const("U".to_string(), vec![])),
    ))
    .expect("Failed to add u axiom");

    let u_ty = Rc::new(Term::Const("U".to_string(), vec![]));
    let u_val = Rc::new(Term::Const("u".to_string(), vec![]));

    let mut total_base = Definition::total(
        "total_base".to_string(),
        comp_of(u_ty.clone()),
        comp_ret(u_ty.clone(), u_val.clone()),
    );
    total_base.noncomputable = true;
    env.add_definition(total_base)
        .expect("Total base should register");
    let mut partial_base = Definition::partial(
        "partial_base".to_string(),
        comp_of(u_ty.clone()),
        comp_ret(u_ty.clone(), u_val.clone()),
    );
    partial_base.noncomputable = true;
    env.add_definition(partial_base)
        .expect("Partial base should register");
    env.add_definition(Definition::unsafe_def(
        "unsafe_base".to_string(),
        comp_of(u_ty.clone()),
        comp_ret(u_ty.clone(), u_val),
    ))
    .expect("Unsafe base should register");

    let mut total_mid = Definition::total(
        "total_mid".to_string(),
        comp_of(u_ty.clone()),
        Rc::new(Term::Const("total_base".to_string(), vec![])),
    );
    total_mid.noncomputable = true;
    env.add_definition(total_mid)
        .expect("Total should be allowed to call total");

    let total_uses_partial = Definition::total(
        "total_uses_partial".to_string(),
        comp_of(u_ty.clone()),
        Rc::new(Term::Const("partial_base".to_string(), vec![])),
    );
    match env.add_definition(total_uses_partial) {
        Err(TypeError::EffectError(from, to, name)) => {
            assert_eq!(from, "Total");
            assert_eq!(to, "Partial");
            assert_eq!(name, "partial_base");
        }
        other => panic!("Expected EffectError for total->partial, got {:?}", other),
    }

    let partial_uses_unsafe = Definition::partial(
        "partial_uses_unsafe".to_string(),
        comp_of(u_ty.clone()),
        Rc::new(Term::Const("unsafe_base".to_string(), vec![])),
    );
    match env.add_definition(partial_uses_unsafe) {
        Err(TypeError::EffectError(from, to, name)) => {
            assert_eq!(from, "Partial");
            assert_eq!(to, "Unsafe");
            assert_eq!(name, "unsafe_base");
        }
        other => panic!("Expected EffectError for partial->unsafe, got {:?}", other),
    }

    let total_uses_unsafe = Definition::total(
        "total_uses_unsafe".to_string(),
        comp_of(u_ty.clone()),
        Rc::new(Term::Const("unsafe_base".to_string(), vec![])),
    );
    match env.add_definition(total_uses_unsafe) {
        Err(TypeError::EffectError(from, to, name)) => {
            assert_eq!(from, "Total");
            assert_eq!(to, "Unsafe");
            assert_eq!(name, "unsafe_base");
        }
        other => panic!("Expected EffectError for total->unsafe, got {:?}", other),
    }
}

#[test]
fn readme_dependent_types_work() {
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let dep_ty = Rc::new(Term::Pi(
        type0.clone(),
        Rc::new(Term::Pi(
            Rc::new(Term::Var(0)),
            Rc::new(Term::Var(1)),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let dep_body = Rc::new(Term::Lam(
        type0,
        Rc::new(Term::Lam(
            Rc::new(Term::Var(0)),
            Rc::new(Term::Var(0)),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    env.add_definition(Definition::total(
        "id_prop_dep".to_string(),
        dep_ty,
        dep_body,
    ))
    .expect("Dependent identity in Prop should typecheck");
}

#[test]
fn readme_inductive_types_work() {
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let unit_ref = Rc::new(Term::Ind("Unit".to_string(), vec![]));
    let unit_decl = InductiveDecl {
        name: "Unit".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0,
        ctors: vec![Constructor {
            name: "unit".to_string(),
            ty: unit_ref.clone(),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(unit_decl)
        .expect("Unit inductive should be accepted");

    let ctx = Context::new();
    let unit_ctor = Rc::new(Term::Ctor("Unit".to_string(), 0, vec![]));
    let ctor_ty = infer(&env, &ctx, unit_ctor).expect("Failed to infer Unit.constructor");
    assert!(matches!(&*ctor_ty, Term::Ind(name, _) if name == "Unit"));
}

#[test]
fn readme_proof_terms_do_not_escape_to_data() {
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let proof_ind = Rc::new(Term::Ind("P".to_string(), vec![]));
    let proof_decl = InductiveDecl {
        name: "P".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop.clone(),
        ctors: vec![Constructor {
            name: "mkP".to_string(),
            ty: proof_ind.clone(),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(proof_decl).expect("Failed to add P");

    let data_ind = Rc::new(Term::Ind("Boxed".to_string(), vec![]));
    let data_decl = InductiveDecl {
        name: "Boxed".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(
                proof_ind,
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

    match env.add_inductive(data_decl) {
        Err(TypeError::PropFieldInData { ind, ctor, field }) => {
            assert_eq!(ind, "Boxed");
            assert_eq!(ctor, "mk");
            assert_eq!(field, 0);
        }
        other => panic!("Expected PropFieldInData for Boxed, got {:?}", other),
    }
}

#[test]
fn readme_prop_field_reduction_respects_opaque() {
    // README promise: data inductives cannot contain Prop fields under standard (opaque-respecting) reduction.
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let prop = Rc::new(Term::Sort(Level::Zero));

    // Transparent alias to Prop should be treated as Prop after unfolding.
    {
        let mut env = Env::new();

        env.add_definition(Definition::total(
            "PropAlias".to_string(),
            type0.clone(),
            prop.clone(),
        ))
        .expect("Failed to add transparent PropAlias");
        env.add_definition(Definition::axiom(
            "prop_witness".to_string(),
            Rc::new(Term::Const("PropAlias".to_string(), vec![])),
        ))
        .expect("Failed to add prop witness");

        let boxed_ref = Rc::new(Term::Ind("BoxedAlias".to_string(), vec![]));
        let boxed_decl = InductiveDecl {
            name: "BoxedAlias".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: type0.clone(),
            ctors: vec![Constructor {
                name: "mk".to_string(),
                ty: Rc::new(Term::Pi(
                    Rc::new(Term::Const("prop_witness".to_string(), vec![])),
                    boxed_ref.clone(),
                    BinderInfo::Default,
                    FunctionKind::Fn,
                )),
            }],
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };

        match env.add_inductive(boxed_decl) {
            Err(TypeError::PropFieldInData { ind, ctor, field }) => {
                assert_eq!(ind, "BoxedAlias");
                assert_eq!(ctor, "mk");
                assert_eq!(field, 0);
            }
            other => panic!(
                "Expected PropFieldInData for BoxedAlias (transparent), got {:?}",
                other
            ),
        }
    }

    // Opaque alias is treated as Prop for Prop-field restrictions (unfolded for safety).
    {
        let mut env = Env::new();

        let mut prop_alias = Definition::total("PropAlias".to_string(), type0.clone(), prop);
        prop_alias.mark_opaque();
        env.add_definition(prop_alias)
            .expect("Failed to add opaque PropAlias");
        env.add_definition(Definition::axiom(
            "prop_witness".to_string(),
            Rc::new(Term::Const("PropAlias".to_string(), vec![])),
        ))
        .expect("Failed to add prop witness");

        let boxed_ref = Rc::new(Term::Ind("BoxedAliasOpaque".to_string(), vec![]));
        let boxed_decl = InductiveDecl {
            name: "BoxedAliasOpaque".to_string(),
            univ_params: vec![],
            num_params: 0,
            ty: type0,
            ctors: vec![Constructor {
                name: "mk".to_string(),
                ty: Rc::new(Term::Pi(
                    Rc::new(Term::Const("prop_witness".to_string(), vec![])),
                    boxed_ref.clone(),
                    BinderInfo::Default,
                    FunctionKind::Fn,
                )),
            }],
            is_copy: false,
            markers: vec![],
            axioms: vec![],
            primitive_deps: vec![],
        };

        match env.add_inductive(boxed_decl) {
            Err(TypeError::PropFieldInData { ind, ctor, field }) => {
                assert_eq!(ind, "BoxedAliasOpaque");
                assert_eq!(ctor, "mk");
                assert_eq!(field, 0);
            }
            other => panic!(
                "Expected BoxedAliasOpaque to be rejected with PropFieldInData, got {:?}",
                other
            ),
        }
    }
}

#[test]
fn readme_pi_codomain_reduces_to_prop_is_prop() {
    // README promise: Pi codomain reducing to Prop keeps the whole function in Prop.
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let prop = Rc::new(Term::Sort(Level::Zero));

    env.add_definition(Definition::total(
        "PropAlias".to_string(),
        type0.clone(),
        prop,
    ))
    .expect("Failed to add PropAlias");

    let alias = Rc::new(Term::Const("PropAlias".to_string(), vec![]));
    let pi_term = Rc::new(Term::Pi(
        alias,
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let inferred = infer(&env, &Context::new(), pi_term.clone())
        .expect("Failed to infer Pi with Prop-reducing codomain");
    assert!(
        matches!(&*inferred, Term::Sort(Level::Zero)),
        "Expected Pi to live in Prop, got {:?}",
        inferred
    );

    // README promise: Prop terms cannot be used to extract data (Prop fields in data are rejected).
    let boxed_ref = Rc::new(Term::Ind("BoxedPi".to_string(), vec![]));
    let boxed_decl = InductiveDecl {
        name: "BoxedPi".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(
                pi_term,
                boxed_ref.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    match env.add_inductive(boxed_decl) {
        Err(TypeError::PropFieldInData { ind, ctor, field }) => {
            assert_eq!(ind, "BoxedPi");
            assert_eq!(ctor, "mk");
            assert_eq!(field, 0);
        }
        other => panic!("Expected PropFieldInData for BoxedPi, got {:?}", other),
    }
}

#[test]
fn readme_no_large_elim_from_prop() {
    let mut env = Env::new();
    let ctx = Context::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let pwrap = Rc::new(Term::Ind("PWrap".to_string(), vec![]));

    let decl = InductiveDecl {
        name: "PWrap".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(
                type0,
                pwrap.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        }],
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
        other => panic!("Expected LargeElimination for PWrap, got {:?}", other),
    }
}

#[test]
fn readme_no_large_elim_from_prop_with_indices() {
    // README promise: elimination from non-singleton Prop into Type is forbidden, even with params/indices.
    let mut env = Env::new();
    let ctx = Context::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let pidx_ref = Rc::new(Term::Ind("PIdx".to_string(), vec![]));
    let pidx_app = Term::app(
        Term::app(pidx_ref.clone(), Rc::new(Term::Var(1))),
        Rc::new(Term::Var(0)),
    );

    let decl = InductiveDecl {
        name: "PIdx".to_string(),
        univ_params: vec![],
        num_params: 1,
        ty: Rc::new(Term::Pi(
            type0.clone(),
            Rc::new(Term::Pi(
                type0.clone(),
                prop,
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        ctors: vec![
            Constructor {
                name: "mk_left".to_string(),
                ty: Rc::new(Term::Pi(
                    type0.clone(),
                    Rc::new(Term::Pi(
                        type0.clone(),
                        pidx_app.clone(),
                        BinderInfo::Default,
                        FunctionKind::Fn,
                    )),
                    BinderInfo::Default,
                    FunctionKind::Fn,
                )),
            },
            Constructor {
                name: "mk_right".to_string(),
                ty: Rc::new(Term::Pi(
                    type0.clone(),
                    Rc::new(Term::Pi(
                        type0.clone(),
                        pidx_app,
                        BinderInfo::Default,
                        FunctionKind::Fn,
                    )),
                    BinderInfo::Default,
                    FunctionKind::Fn,
                )),
            },
        ],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl)
        .expect("Failed to add indexed Prop inductive");

    let rec = Rc::new(Term::Rec(
        "PIdx".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));
    match infer(&env, &ctx, rec) {
        Err(TypeError::LargeElimination(name)) => assert_eq!(name, "PIdx"),
        other => panic!("Expected LargeElimination for PIdx, got {:?}", other),
    }
}

#[test]
fn readme_large_elim_allowed_for_prop_singleton() {
    let mut env = Env::new();
    let ctx = Context::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let unit_prop = Rc::new(Term::Ind("UnitProp".to_string(), vec![]));

    let decl = InductiveDecl {
        name: "UnitProp".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: unit_prop.clone(),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl).expect("Failed to add UnitProp");

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

#[test]
fn readme_large_elim_allowed_for_prop_singleton_prop_fields() {
    // README promise: singleton Prop with all fields in Prop may eliminate into Type.
    let mut env = Env::new();
    let ctx = Context::new();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let prop_ind = Rc::new(Term::Ind("P".to_string(), vec![]));

    let prop_decl = InductiveDecl {
        name: "P".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop.clone(),
        ctors: vec![Constructor {
            name: "mkP".to_string(),
            ty: prop_ind.clone(),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(prop_decl).expect("Failed to add P");

    let pair_ind = Rc::new(Term::Ind("PropPair".to_string(), vec![]));
    let pair_decl = InductiveDecl {
        name: "PropPair".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(
                prop_ind.clone(),
                Rc::new(Term::Pi(
                    prop_ind,
                    pair_ind.clone(),
                    BinderInfo::Default,
                    FunctionKind::Fn,
                )),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(pair_decl)
        .expect("Failed to add PropPair");

    let rec = Rc::new(Term::Rec(
        "PropPair".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));
    let result = infer(&env, &ctx, rec);
    assert!(
        result.is_ok(),
        "Large elimination for singleton Prop with Prop fields should be allowed: {:?}",
        result
    );
}

#[test]
fn readme_macros_cannot_hide_unsafe_or_classical() {
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    env.add_definition(Definition::axiom_classical(
        "Choice".to_string(),
        prop.clone(),
    ))
    .expect("Failed to add classical axiom");
    env.add_definition(Definition::axiom("TypeX".to_string(), type1))
        .expect("Failed to add TypeX axiom");
    env.add_definition(Definition::axiom_with_tags(
        "UnsafeAx".to_string(),
        Rc::new(Term::Const("TypeX".to_string(), vec![])),
        vec![AxiomTag::Unsafe],
    ))
    .expect("Failed to add unsafe axiom");

    let mut use_choice = Definition::total(
        "use_choice".to_string(),
        prop.clone(),
        Rc::new(Term::Const("Choice".to_string(), vec![])),
    );
    use_choice.noncomputable = true;
    env.add_definition(use_choice)
        .expect("Failed to add total def using classical axiom");

    let mut use_choice_via = Definition::total(
        "use_choice_via".to_string(),
        prop.clone(),
        Rc::new(Term::Const("use_choice".to_string(), vec![])),
    );
    use_choice_via.noncomputable = true;
    env.add_definition(use_choice_via)
        .expect("Failed to add total def using classical def");

    env.add_definition(Definition::unsafe_def(
        "use_unsafe".to_string(),
        Rc::new(Term::Const("TypeX".to_string(), vec![])),
        Rc::new(Term::Const("UnsafeAx".to_string(), vec![])),
    ))
    .expect("Failed to add unsafe def using unsafe axiom");

    env.add_definition(Definition::unsafe_def(
        "use_unsafe_via".to_string(),
        Rc::new(Term::Const("TypeX".to_string(), vec![])),
        Rc::new(Term::Const("use_unsafe".to_string(), vec![])),
    ))
    .expect("Failed to add unsafe def using unsafe def");

    let use_choice = env
        .get_definition("use_choice")
        .expect("Missing use_choice");
    let classical = axiom_dependencies_with_tag(&env, &use_choice.axioms, AxiomTag::Classical);
    assert_eq!(classical, vec!["Choice".to_string()]);

    let use_choice_via = env
        .get_definition("use_choice_via")
        .expect("Missing use_choice_via");
    let classical_via =
        axiom_dependencies_with_tag(&env, &use_choice_via.axioms, AxiomTag::Classical);
    assert_eq!(classical_via, vec!["Choice".to_string()]);

    let use_unsafe = env
        .get_definition("use_unsafe")
        .expect("Missing use_unsafe");
    let unsafe_deps = axiom_dependencies_with_tag(&env, &use_unsafe.axioms, AxiomTag::Unsafe);
    assert_eq!(unsafe_deps, vec!["UnsafeAx".to_string()]);

    let use_unsafe_via = env
        .get_definition("use_unsafe_via")
        .expect("Missing use_unsafe_via");
    let unsafe_via = axiom_dependencies_with_tag(&env, &use_unsafe_via.axioms, AxiomTag::Unsafe);
    assert_eq!(unsafe_via, vec!["UnsafeAx".to_string()]);
}

#[test]
fn readme_classical_axiom_propagates_through_prop_chain() {
    // README promise: classical Prop axioms must be tracked through definitional chains.
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));

    env.add_definition(Definition::axiom_classical(
        "ClassicalProp".to_string(),
        prop.clone(),
    ))
    .expect("Failed to add classical axiom");

    let mut use_classical_0 = Definition::total(
        "use_classical_0".to_string(),
        prop.clone(),
        Rc::new(Term::Const("ClassicalProp".to_string(), vec![])),
    );
    use_classical_0.noncomputable = true;
    env.add_definition(use_classical_0)
        .expect("Failed to add use_classical_0");

    let mut use_classical_1 = Definition::total(
        "use_classical_1".to_string(),
        prop.clone(),
        Rc::new(Term::Const("use_classical_0".to_string(), vec![])),
    );
    use_classical_1.noncomputable = true;
    env.add_definition(use_classical_1)
        .expect("Failed to add use_classical_1");

    let mut use_classical_2 = Definition::total(
        "use_classical_2".to_string(),
        prop,
        Rc::new(Term::Const("use_classical_1".to_string(), vec![])),
    );
    use_classical_2.noncomputable = true;
    env.add_definition(use_classical_2)
        .expect("Failed to add use_classical_2");

    let use_classical_2 = env
        .get_definition("use_classical_2")
        .expect("Missing use_classical_2");
    let deps = axiom_dependencies_with_tag(&env, &use_classical_2.axioms, AxiomTag::Classical);
    assert_eq!(deps, vec!["ClassicalProp".to_string()]);
}

#[test]
fn readme_axiom_tags_mix_in_defs_and_inductives() {
    // README promise: axiom tags are tracked and filtered independently.
    let mut env = Env::new();
    let type1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    env.add_definition(Definition::axiom("U".to_string(), type1.clone()))
        .expect("Failed to add U axiom");

    env.add_definition(Definition::axiom_classical(
        "ClassicalAx".to_string(),
        Rc::new(Term::Const("U".to_string(), vec![])),
    ))
    .expect("Failed to add classical axiom");
    env.add_definition(Definition::axiom_with_tags(
        "UnsafeAx".to_string(),
        Rc::new(Term::Const("U".to_string(), vec![])),
        vec![AxiomTag::Unsafe],
    ))
    .expect("Failed to add unsafe axiom");

    let mix_val = Rc::new(Term::LetE(
        Rc::new(Term::Const("U".to_string(), vec![])),
        Rc::new(Term::Const("ClassicalAx".to_string(), vec![])),
        Rc::new(Term::Const("UnsafeAx".to_string(), vec![])),
    ));

    env.add_definition(Definition::unsafe_def(
        "mix".to_string(),
        Rc::new(Term::Const("U".to_string(), vec![])),
        mix_val,
    ))
    .expect("Failed to add mixed-tag unsafe def");

    let mix_def = env.get_definition("mix").expect("Missing mix");
    let classical = axiom_dependencies_with_tag(&env, &mix_def.axioms, AxiomTag::Classical);
    assert_eq!(classical, vec!["ClassicalAx".to_string()]);
    let unsafe_deps = axiom_dependencies_with_tag(&env, &mix_def.axioms, AxiomTag::Unsafe);
    assert_eq!(unsafe_deps, vec!["UnsafeAx".to_string()]);

    let tagged_ref = Rc::new(Term::Ind("Tagged".to_string(), vec![]));
    let tagged_decl = InductiveDecl {
        name: "Tagged".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type1,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: tagged_ref.clone(),
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec!["ClassicalAx".to_string(), "UnsafeAx".to_string()],
        primitive_deps: vec![],
    };

    env.add_inductive(tagged_decl)
        .expect("Failed to add Tagged inductive");

    let tagged = env.get_inductive("Tagged").expect("Missing Tagged");
    let tagged_classical = axiom_dependencies_with_tag(&env, &tagged.axioms, AxiomTag::Classical);
    assert_eq!(tagged_classical, vec!["ClassicalAx".to_string()]);
    let tagged_unsafe = axiom_dependencies_with_tag(&env, &tagged.axioms, AxiomTag::Unsafe);
    assert_eq!(tagged_unsafe, vec!["UnsafeAx".to_string()]);
}

#[test]
fn readme_nonpositive_inductive_rejected() {
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));
    let bad_ref = Rc::new(Term::Ind("Bad".to_string(), vec![]));

    let bad_decl = InductiveDecl {
        name: "Bad".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop.clone(),
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: Rc::new(Term::Pi(
                Rc::new(Term::Pi(
                    bad_ref.clone(),
                    prop,
                    BinderInfo::Default,
                    FunctionKind::Fn,
                )),
                bad_ref,
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    match env.add_inductive(bad_decl) {
        Err(TypeError::NonPositiveOccurrence(ind, ctor, arg)) => {
            assert_eq!(ind, "Bad");
            assert_eq!(ctor, "mk");
            assert_eq!(arg, 0);
        }
        other => panic!("Expected NonPositiveOccurrence for Bad, got {:?}", other),
    }
}

#[test]
fn readme_nested_nonpositive_inductive_rejected() {
    // README promise: inductive constructors must be strictly positive, even under nested Pis/apps.
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let wrap_ref = Rc::new(Term::Ind("Wrap".to_string(), vec![]));
    let wrap_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let wrap_ctor_ty = Rc::new(Term::Pi(
        type0.clone(),
        Rc::new(Term::Pi(
            Rc::new(Term::Var(0)),
            Term::app(wrap_ref.clone(), Rc::new(Term::Var(1))),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let wrap_decl = InductiveDecl {
        name: "Wrap".to_string(),
        univ_params: vec![],
        num_params: 1,
        ty: wrap_ty,
        ctors: vec![Constructor {
            name: "wrap".to_string(),
            ty: wrap_ctor_ty,
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };
    env.add_inductive(wrap_decl)
        .expect("Wrap inductive should be accepted");

    let bad_ref = Rc::new(Term::Ind("BadNest".to_string(), vec![]));
    let nested_bad = Term::app(wrap_ref.clone(), Term::app(wrap_ref, bad_ref.clone()));
    let bad_arg_ty = Rc::new(Term::Pi(
        nested_bad,
        type0.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let bad_ctor_ty = Rc::new(Term::Pi(
        bad_arg_ty,
        bad_ref.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let bad_decl = InductiveDecl {
        name: "BadNest".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: type0,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: bad_ctor_ty,
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    match env.add_inductive(bad_decl) {
        Err(TypeError::NonPositiveOccurrence(ind, ctor, arg)) => {
            assert_eq!(ind, "BadNest");
            assert_eq!(ctor, "mk");
            assert_eq!(arg, 0);
        }
        other => panic!(
            "Expected NonPositiveOccurrence for BadNest, got {:?}",
            other
        ),
    }
}

#[test]
fn readme_ctor_param_index_arity_mismatch() {
    // README promise: constructors must return the inductive applied to all params and indices.
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    env.add_definition(Definition::axiom("Idx".to_string(), type0.clone()))
        .expect("Failed to add Idx");

    let idx_ty = Rc::new(Term::Const("Idx".to_string(), vec![]));
    let box_ref = Rc::new(Term::Ind("IxBox".to_string(), vec![]));
    let box_ty = Rc::new(Term::Pi(
        type0.clone(), // A
        Rc::new(Term::Pi(
            idx_ty.clone(), // i
            type0.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let ctor_ty = Rc::new(Term::Pi(
        type0.clone(), // A
        Rc::new(Term::Pi(
            idx_ty,
            Term::app(box_ref.clone(), Rc::new(Term::Var(1))),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let decl = InductiveDecl {
        name: "IxBox".to_string(),
        univ_params: vec![],
        num_params: 1,
        ty: box_ty,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: ctor_ty,
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    match env.add_inductive(decl) {
        Err(TypeError::CtorArityMismatch {
            ind,
            ctor,
            expected,
            got,
        }) => {
            assert_eq!(ind, "IxBox");
            assert_eq!(ctor, "mk");
            assert_eq!(expected, 2);
            assert_eq!(got, 1);
        }
        other => panic!("Expected CtorArityMismatch for IxBox, got {:?}", other),
    }
}

#[test]
fn readme_recursor_level_count_mismatch() {
    // README promise: recursors require explicit universe levels matching inductive parameters.
    let mut env = Env::new();
    let ctx = Context::new();

    let ubox_ref = Rc::new(Term::Ind("UBox".to_string(), vec![]));
    let ubox_decl = InductiveDecl {
        name: "UBox".to_string(),
        univ_params: vec!["u".to_string()],
        num_params: 0,
        ty: Rc::new(Term::Sort(Level::Param("u".to_string()))),
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: ubox_ref,
        }],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(ubox_decl)
        .expect("UBox inductive should be accepted");

    let rec = Rc::new(Term::Rec("UBox".to_string(), vec![Level::Zero]));
    match infer(&env, &ctx, rec) {
        Err(TypeError::RecursorLevelCount { ind, expected, got }) => {
            assert_eq!(ind, "UBox");
            assert_eq!(expected, 2);
            assert_eq!(got, 1);
        }
        other => panic!("Expected RecursorLevelCount for UBox, got {:?}", other),
    }
}

#[test]
fn readme_data_inductive_rejects_prop_field_via_def() {
    // README promise: data inductives cannot store Prop fields, even when Prop is hidden by defs.
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let prop = Rc::new(Term::Sort(Level::Zero));

    env.add_definition(Definition::total(
        "PropAliasTy".to_string(),
        type0.clone(),
        prop,
    ))
    .expect("Failed to add PropAliasTy");
    env.add_definition(Definition::axiom(
        "P".to_string(),
        Rc::new(Term::Const("PropAliasTy".to_string(), vec![])),
    ))
    .expect("Failed to add P");
    env.add_definition(Definition::axiom("Idx".to_string(), type0.clone()))
        .expect("Failed to add Idx");

    let idx_ty = Rc::new(Term::Const("Idx".to_string(), vec![]));
    let prop_term = Rc::new(Term::Const("P".to_string(), vec![]));
    let ind_ref = Rc::new(Term::Ind("IdxBox".to_string(), vec![]));

    let ind_ty = Rc::new(Term::Pi(
        type0.clone(), // A
        Rc::new(Term::Pi(
            idx_ty.clone(), // i
            type0.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let ctor_ty = Rc::new(Term::Pi(
        type0.clone(), // A
        Rc::new(Term::Pi(
            idx_ty,
            Rc::new(Term::Pi(
                prop_term,
                Term::app(
                    Term::app(ind_ref.clone(), Rc::new(Term::Var(2))),
                    Rc::new(Term::Var(1)),
                ),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let decl = InductiveDecl {
        name: "IdxBox".to_string(),
        univ_params: vec![],
        num_params: 1,
        ty: ind_ty,
        ctors: vec![Constructor {
            name: "mk".to_string(),
            ty: ctor_ty,
        }],
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    match env.add_inductive(decl) {
        Err(TypeError::PropFieldInData { ind, ctor, field }) => {
            assert_eq!(ind, "IdxBox");
            assert_eq!(ctor, "mk");
            assert_eq!(field, 1);
        }
        other => panic!("Expected PropFieldInData for IdxBox, got {:?}", other),
    }
}

#[test]
fn readme_type_mismatch_rejected() {
    let mut env = Env::new();
    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let bad_def = Definition::total("bad".to_string(), prop, type0);
    match env.add_definition(bad_def) {
        Err(TypeError::TypeMismatch { .. }) => {}
        other => panic!("Expected TypeMismatch for bad, got {:?}", other),
    }
}

#[test]
fn readme_reserved_primitives_require_opt_in() {
    // README promise: reserved primitives require explicit opt-in.
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let attempt = Definition::axiom("borrow_shared".to_string(), type0);
    match env.add_definition(attempt) {
        Err(TypeError::ReservedPrimitiveName(name)) => assert_eq!(name, "borrow_shared"),
        other => panic!(
            "Expected ReservedPrimitiveName for borrow_shared, got {:?}",
            other
        ),
    }
}

#[test]
fn readme_reserved_primitives_gated() {
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let missing_unsafe = Definition::axiom("index_array".to_string(), type0.clone());
    match env.add_definition(missing_unsafe) {
        Err(TypeError::ReservedPrimitiveName(name)) => {
            assert_eq!(name, "index_array");
        }
        other => panic!(
            "Expected ReservedPrimitiveName for index_array, got {:?}",
            other
        ),
    }

    let bad_sig = Definition::axiom("borrow_shared".to_string(), type0);
    match env.add_definition(bad_sig) {
        Err(TypeError::ReservedPrimitiveSignature(name)) => {
            assert_eq!(name, "borrow_shared");
        }
        other => panic!(
            "Expected ReservedPrimitiveSignature for borrow_shared, got {:?}",
            other
        ),
    }

    let bad_index_sig = Definition::axiom_with_tags(
        "index_slice".to_string(),
        Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero)))),
        vec![AxiomTag::Unsafe],
    );
    match env.add_definition(bad_index_sig) {
        Err(TypeError::ReservedPrimitiveSignature(name)) => {
            assert_eq!(name, "index_slice");
        }
        other => panic!(
            "Expected ReservedPrimitiveSignature for index_slice, got {:?}",
            other
        ),
    }
}

#[test]
fn readme_reserved_primitives_cannot_be_redefined() {
    // README promise: reserved primitive names are not shadowable.
    let mut env = Env::new();
    env.set_allow_reserved_primitives(true);

    let sort1 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    env.add_definition(Definition::axiom("Shared".to_string(), sort1.clone()))
        .expect("Failed to add Shared");
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

    let borrow_shared_ty = Rc::new(Term::Pi(
        sort1.clone(),
        Rc::new(Term::Pi(
            Rc::new(Term::Var(0)),
            Term::app_with_label(
                Term::app(
                    Rc::new(Term::Const("Ref".to_string(), vec![])),
                    Rc::new(Term::Const("Shared".to_string(), vec![])),
                ),
                Rc::new(Term::Var(1)),
                Some("r".to_string()),
            ),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    env.add_definition(Definition::axiom(
        "borrow_shared".to_string(),
        borrow_shared_ty.clone(),
    ))
    .expect("Failed to register borrow_shared");

    let shadow = Definition::axiom("borrow_shared".to_string(), borrow_shared_ty);
    match env.add_definition(shadow) {
        Err(TypeError::ReservedPrimitiveName(name)) => assert_eq!(name, "borrow_shared"),
        other => panic!(
            "Expected ReservedPrimitiveName for borrow_shared shadowing, got {:?}",
            other
        ),
    }
}

#[test]
fn readme_mutual_recursion_chain_rejected() {
    // README promise: mutual total recursion must decrease on a common structural argument.
    let mut env = Env::new();
    let nat_ref = add_nat(&mut env);
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    env.add_definition(Definition::axiom("A".to_string(), type0))
        .expect("Failed to add A");
    let a_ty = Rc::new(Term::Const("A".to_string(), vec![]));

    let f_ty = Rc::new(Term::Pi(
        nat_ref.clone(),
        Rc::new(Term::Pi(
            a_ty.clone(),
            nat_ref.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let g_ty = Rc::new(Term::Pi(
        a_ty.clone(),
        Rc::new(Term::Pi(
            nat_ref.clone(),
            nat_ref.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let h_ty = f_ty.clone();

    // f n a = g a n
    let f_body = Rc::new(Term::Lam(
        nat_ref.clone(),
        Rc::new(Term::Lam(
            a_ty.clone(),
            Term::app(
                Term::app(
                    Rc::new(Term::Const("g".to_string(), vec![])),
                    Rc::new(Term::Var(0)),
                ),
                Rc::new(Term::Var(1)),
            ),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    // g a n = h n a
    let g_body = Rc::new(Term::Lam(
        a_ty.clone(),
        Rc::new(Term::Lam(
            nat_ref.clone(),
            Term::app(
                Term::app(
                    Rc::new(Term::Const("h".to_string(), vec![])),
                    Rc::new(Term::Var(0)),
                ),
                Rc::new(Term::Var(1)),
            ),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    // h n a = f n a
    let h_body = Rc::new(Term::Lam(
        nat_ref.clone(),
        Rc::new(Term::Lam(
            a_ty,
            Term::app(
                Term::app(
                    Rc::new(Term::Const("f".to_string(), vec![])),
                    Rc::new(Term::Var(1)),
                ),
                Rc::new(Term::Var(0)),
            ),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let defs = vec![
        ("f".to_string(), f_ty, f_body),
        ("g".to_string(), g_ty, g_body),
        ("h".to_string(), h_ty, h_body),
    ];
    match check_mutual_termination(&env, &defs) {
        Err(TypeError::TerminationError {
            details: TerminationErrorDetails::MutualRecursionError { functions },
            ..
        }) => {
            assert!(functions.contains(&"f".to_string()));
            assert!(functions.contains(&"g".to_string()));
            assert!(functions.contains(&"h".to_string()));
        }
        other => panic!("Expected MutualRecursionError for f/g/h, got {:?}", other),
    }
}

#[test]
fn readme_mutual_recursion_common_measure_accepted() {
    // README promise: mutual recursion must decrease on a shared structural argument.
    let mut env = Env::new();
    let nat_ref = add_nat(&mut env);

    let f_ty = Rc::new(Term::Pi(
        nat_ref.clone(),
        Rc::new(Term::Pi(
            nat_ref.clone(),
            nat_ref.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let g_ty = f_ty.clone();

    let rec = Rc::new(Term::Rec(
        "Nat".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));
    let motive = Term::lam(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default);

    let f_step = Term::lam(
        nat_ref.clone(),
        Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(Rc::new(Term::Const("g".to_string(), vec![])), Term::var(1)),
                Term::var(2),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let f_body = Term::lam(
        nat_ref.clone(),
        Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(
                    Term::app(Term::app(rec.clone(), motive.clone()), Term::var(0)),
                    f_step,
                ),
                Term::var(1),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let g_step = Term::lam(
        nat_ref.clone(),
        Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(Rc::new(Term::Const("f".to_string(), vec![])), Term::var(1)),
                Term::var(2),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let g_body = Term::lam(
        nat_ref.clone(),
        Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(
                    Term::app(Term::app(rec.clone(), motive), Term::var(0)),
                    g_step,
                ),
                Term::var(1),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let defs = vec![
        ("f".to_string(), f_ty, f_body),
        ("g".to_string(), g_ty, g_body),
    ];

    let result = check_mutual_termination(&env, &defs);
    assert!(result.is_ok(), "Expected mutual recursion to pass");
}

#[test]
fn readme_mutual_recursion_mismatched_measure_rejected() {
    // README promise: mutual recursion must share a single decreasing argument.
    let mut env = Env::new();
    let nat_ref = add_nat(&mut env);

    let f_ty = Rc::new(Term::Pi(
        nat_ref.clone(),
        Rc::new(Term::Pi(
            nat_ref.clone(),
            nat_ref.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let g_ty = f_ty.clone();

    let rec = Rc::new(Term::Rec(
        "Nat".to_string(),
        vec![Level::Succ(Box::new(Level::Zero))],
    ));
    let motive = Term::lam(nat_ref.clone(), nat_ref.clone(), BinderInfo::Default);

    let f_step = Term::lam(
        nat_ref.clone(),
        Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(Rc::new(Term::Const("g".to_string(), vec![])), Term::var(1)),
                Term::var(2),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    // f recurses on the first argument (n)
    let f_body = Term::lam(
        nat_ref.clone(),
        Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(
                    Term::app(Term::app(rec.clone(), motive.clone()), Term::var(0)),
                    f_step,
                ),
                Term::var(1),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let g_step = Term::lam(
        nat_ref.clone(),
        Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(Rc::new(Term::Const("f".to_string(), vec![])), Term::var(3)),
                Term::var(1),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    // g recurses on the second argument (m), calling f with unchanged n
    let g_body = Term::lam(
        nat_ref.clone(),
        Term::lam(
            nat_ref.clone(),
            Term::app(
                Term::app(Term::app(Term::app(rec, motive), Term::var(0)), g_step),
                Term::var(0),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let defs = vec![
        ("f".to_string(), f_ty, f_body),
        ("g".to_string(), g_ty, g_body),
    ];

    let result = check_mutual_termination(&env, &defs);
    match result {
        Err(TypeError::TerminationError {
            details: TerminationErrorDetails::MutualRecursionError { functions },
            ..
        }) => {
            assert!(functions.contains(&"f".to_string()));
            assert!(functions.contains(&"g".to_string()));
        }
        other => panic!(
            "Expected MutualRecursionError for mismatched measures, got {:?}",
            other
        ),
    }
}

#[test]
fn readme_recursive_alias_chain_rejected() {
    // README promise: termination checking must detect recursion through alias chains.
    let mut env = Env::new();
    let nat_ref = add_nat(&mut env);
    let fn_ty = Rc::new(Term::Pi(
        nat_ref.clone(),
        nat_ref.clone(),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let alias_body = Rc::new(Term::Lam(
        nat_ref.clone(),
        Rc::new(Term::LetE(
            fn_ty.clone(),
            Rc::new(Term::Const("loop_alias".to_string(), vec![])),
            Term::app(Rc::new(Term::Var(0)), Rc::new(Term::Var(1))),
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let alias_def = Definition::total("loop_alias".to_string(), fn_ty.clone(), alias_body);
    match env.add_definition(alias_def) {
        Err(TypeError::TerminationError {
            details: TerminationErrorDetails::NonSmallerArgument { arg_position, .. },
            ..
        }) => assert_eq!(arg_position, 0),
        other => panic!(
            "Expected NonSmallerArgument for loop_alias, got {:?}",
            other
        ),
    }

    let chained_body = Rc::new(Term::Lam(
        nat_ref.clone(),
        Rc::new(Term::LetE(
            fn_ty.clone(),
            Rc::new(Term::Const("loop_alias_chain".to_string(), vec![])),
            Rc::new(Term::LetE(
                fn_ty.clone(),
                Rc::new(Term::Var(0)),
                Term::app(Rc::new(Term::Var(0)), Rc::new(Term::Var(2))),
            )),
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let chained_def = Definition::total("loop_alias_chain".to_string(), fn_ty, chained_body);
    match env.add_definition(chained_def) {
        Err(TypeError::TerminationError {
            details: TerminationErrorDetails::NonSmallerArgument { arg_position, .. },
            ..
        }) => assert_eq!(arg_position, 0),
        other => panic!(
            "Expected NonSmallerArgument for loop_alias_chain, got {:?}",
            other
        ),
    }
}

#[test]
fn readme_wellfounded_acc_target_mismatch_rejected() {
    // README promise: well-founded recursion must use Acc proofs for the actual decreasing target.
    let mut env = Env::new();
    let nat_ref = add_nat(&mut env);
    add_lt(&mut env, &nat_ref);
    let acc_ind = add_acc(&mut env);

    let lt_const = Rc::new(Term::Const("lt".to_string(), vec![]));
    let acc_app = |target: Rc<Term>| {
        Term::app(
            Term::app(
                Term::app(acc_ind.clone(), nat_ref.clone()),
                lt_const.clone(),
            ),
            target,
        )
    };

    let acc_n_ty = acc_app(Rc::new(Term::Var(1)));
    let wf_ty = Rc::new(Term::Pi(
        nat_ref.clone(),
        Rc::new(Term::Pi(
            nat_ref.clone(),
            Rc::new(Term::Pi(
                acc_n_ty.clone(),
                nat_ref.clone(),
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let acc_x_ty = acc_app(Rc::new(Term::Var(0)));
    let bad_rec_call = Term::app(
        Term::app(
            Term::app(
                Rc::new(Term::Const("wf_bad".to_string(), vec![])),
                Rc::new(Term::Var(3)),
            ),
            Rc::new(Term::Var(1)),
        ),
        Rc::new(Term::Var(0)),
    );
    let minor = Rc::new(Term::Lam(
        nat_ref.clone(),
        Rc::new(Term::Lam(
            acc_x_ty,
            bad_rec_call,
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let rec_acc = Rc::new(Term::Rec("Acc".to_string(), vec![Level::Zero]));
    let rec_app = Term::app(
        Term::app(
            Term::app(Term::app(rec_acc, nat_ref.clone()), lt_const),
            Rc::new(Term::Sort(Level::Zero)),
        ),
        minor,
    );

    let wf_body = Rc::new(Term::Lam(
        nat_ref.clone(),
        Rc::new(Term::Lam(
            nat_ref.clone(),
            Rc::new(Term::Lam(
                acc_n_ty,
                rec_app,
                BinderInfo::Default,
                FunctionKind::Fn,
            )),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let spec = WellFoundedSpec {
        relation: "lt".to_string(),
        value_type: nat_ref,
        wf_proof: None,
        decreasing_arg: 0,
    };

    match check_wellfounded_termination(&env, "wf_bad", &wf_ty, &wf_body, &spec) {
        Err(TypeError::TerminationError {
            details:
                TerminationErrorDetails::WellFoundedError(WellFoundedError::MismatchedAccTarget {
                    ..
                }),
            ..
        }) => {}
        other => panic!("Expected MismatchedAccTarget for wf_bad, got {:?}", other),
    }
}

#[test]
fn readme_wellfounded_requires_acc_parameter() {
    // README promise: well-founded recursion requires an explicit Acc parameter.
    let mut env = Env::new();
    let nat_ref = add_nat(&mut env);
    add_lt(&mut env, &nat_ref);
    add_acc(&mut env);

    let wf_ty = Rc::new(Term::Pi(
        nat_ref.clone(),
        Rc::new(Term::Pi(
            nat_ref.clone(),
            nat_ref.clone(),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    let wf_body = Rc::new(Term::Lam(
        nat_ref.clone(),
        Rc::new(Term::Lam(
            nat_ref.clone(),
            Rc::new(Term::Var(0)),
            BinderInfo::Default,
            FunctionKind::Fn,
        )),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    let spec = WellFoundedSpec {
        relation: "lt".to_string(),
        value_type: nat_ref,
        wf_proof: None,
        decreasing_arg: 0,
    };

    match check_wellfounded_termination(&env, "wf_missing_acc", &wf_ty, &wf_body, &spec) {
        Err(TypeError::TerminationError {
            details:
                TerminationErrorDetails::WellFoundedError(WellFoundedError::MissingAccParameter {
                    relation,
                }),
            ..
        }) => assert_eq!(relation, "lt"),
        other => panic!(
            "Expected MissingAccParameter for wf_missing_acc, got {:?}",
            other
        ),
    }
}
