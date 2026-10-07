//! Regression tests for typing rules of the core calculus that the kernel did not enforce
//! as stated (review of the JOT revision):
//!
//! * the elimination restriction for inductive propositions: large elimination is allowed only
//!   for propositions with no constructor, or with exactly one constructor all of whose FIELDS
//!   (the binders after the uniform parameters) are proofs, plus the equality exception. A field
//!   whose type is the sort `Prop` itself holds a proposition, not a proof; accepting it made
//!   `Prop` a definitional retract of a proposition (the setting of Hurkens' paradox);
//! * T-Pi / T-Lam / T-Fix / T-Let: binder types (and the codomain of a Pi) must be types;
//! * inductive declarations: the arity is a telescope of types ending in a sort (possibly
//!   through an alias, which no longer bypasses the universe check) and every constructor type
//!   is a type (an arity such as an empty proposition made `Ind` a closed proof of it);
//! * the universe rule for inductive declarations: in an inductive in `Sort u` (`u` not Prop)
//!   every constructor field has a type whose sort is at most `u`, computed from the field
//!   type's inferred sort (a field of type `Sort l` is at level `l + 1`; counting it at `l` made
//!   `Type` a retract of a type in `Type`); parameters and indices are not constrained;
//!   levels are compared for every assignment of the level parameters (Lean 4's `is_geq`), and
//!   `imax a u` is not normalised to `max a u` when `u` may be 0;
//! * strict positivity: no occurrence of the inductive in the domain of an arrow at any depth (an
//!   occurrence under two arrows used to count as positive: Coquand-Paulin), and a `let` cannot
//!   hide an occurrence (declarations are zeta-expanded); no occurrence of the inductive in the
//!   arguments (indices) of a constructor's result type;
//! * the elimination restriction also applies to inductives that MAY be propositions (an arity
//!   ending in `Sort u` or `Sort (imax 1 u)`), as in Lean 4;
//! * level comparison distributes `succ` over `max` (`u + 1 <= max u v + 2`);
//! * a failed inductive declaration (e.g. a failed Copy derivation) leaves no placeholder behind;
//! * the lifetime elision rule (`K0045`) applies once per complete signature (chain of Pis), not
//!   to each curried suffix;
//! * fixpoints: T-Fix lifts the annotation over the recursive binder, a fixpoint may not return
//!   a proof (`K0055`), and type checking never unfolds a fixpoint (`K0049`);
//! * normalisation: a recursive total definition unfolds only on a constructor (guarded δ), the
//!   budget counts every step (β, ζ, read-back binders too) and is shared by evaluation and
//!   read-back, and the nesting depth is limited (`K0056`);
//! * definitions: redefining a name others refer to is refused (`K0054`), a `Derived` Copy
//!   instance from the API is re-derived, only axioms lack values (`K0053`) and an axiom depends
//!   on itself.

use kernel::ast::{
    BinderInfo, Constructor, Definition, FunctionKind, InductiveDecl, Level, Term, Transparency,
};
use kernel::checker::{
    check_termination, compute_recursor_type, infer, validate_core_term, whnf, whnf_in_ctx,
    Context, Env, TerminationErrorDetails, TypeError,
};
use std::rc::Rc;

fn prop() -> Rc<Term> {
    Rc::new(Term::Sort(Level::Zero))
}

fn type0() -> Rc<Term> {
    Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))))
}

fn level1() -> Level {
    Level::Succ(Box::new(Level::Zero))
}

fn ind(name: &str) -> Rc<Term> {
    Rc::new(Term::Ind(name.to_string(), vec![]))
}

fn decl(name: &str, ty: Rc<Term>, ctors: Vec<(&str, Rc<Term>)>) -> InductiveDecl {
    InductiveDecl {
        name: name.to_string(),
        univ_params: vec![],
        num_params: 0,
        ty,
        ctors: ctors
            .into_iter()
            .map(|(name, ty)| Constructor {
                name: name.to_string(),
                ty,
            })
            .collect(),
        is_copy: false,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    }
}

/// `N : Type` with `zero` and `succ`, and `TrueP : Prop` with `tt`.
fn base_env() -> Env {
    let mut env = Env::new();
    env.add_inductive(decl(
        "N",
        type0(),
        vec![
            ("zero", ind("N")),
            ("succ", Term::pi(ind("N"), ind("N"), BinderInfo::Default)),
        ],
    ))
    .expect("add N");
    env.add_inductive(decl("TrueP", prop(), vec![("tt", ind("TrueP"))]))
        .expect("add TrueP");
    env
}

fn rec_into_type(name: &str) -> Rc<Term> {
    Rc::new(Term::Rec(name.to_string(), vec![level1()]))
}

fn assert_large_elimination_rejected(env: &Env, name: &str) {
    match infer(env, &Context::new(), rec_into_type(name)) {
        Err(TypeError::LargeElimination(found)) => assert_eq!(found, name),
        other => panic!("expected LargeElimination for {}, got {:?}", name, other),
    }
}

fn assert_large_elimination_allowed(env: &Env, name: &str) {
    let result = infer(env, &Context::new(), rec_into_type(name));
    assert!(
        result.is_ok(),
        "expected large elimination of {} to be allowed, got {:?}",
        name,
        result
    );
}

// =============================================================================
// Elimination restriction
// =============================================================================

/// `PW : Prop` with `mkpw : Prop -> PW`. Its field is a proposition, not a proof; large
/// elimination would give `up : PW -> Prop` with `up (mkpw P) ≡ P` (Prop a retract of PW).
#[test]
fn field_of_type_prop_does_not_allow_large_elimination() {
    let mut env = base_env();
    env.add_inductive(decl(
        "PW",
        prop(),
        vec![("mkpw", Term::pi(prop(), ind("PW"), BinderInfo::Default))],
    ))
    .expect("add PW");
    assert_large_elimination_rejected(&env, "PW");
    // Elimination into Prop stays allowed.
    let small = Rc::new(Term::Rec("PW".to_string(), vec![Level::Zero]));
    assert!(infer(&env, &Context::new(), small).is_ok());
}

/// `Wrap : Type -> Prop` with `mkw : (A : Type) -> TrueP -> Wrap A`: one constructor whose only
/// field is a proof; the Type parameter is not a field and does not block large elimination.
#[test]
fn type_parameter_with_proof_fields_allows_large_elimination() {
    let mut env = base_env();
    let wrap_a = Term::app(ind("Wrap"), Rc::new(Term::Var(1)));
    let mut wrap = decl(
        "Wrap",
        Term::pi(type0(), prop(), BinderInfo::Default),
        vec![(
            "mkw",
            Term::pi(
                type0(),
                Term::pi(ind("TrueP"), wrap_a, BinderInfo::Default),
                BinderInfo::Default,
            ),
        )],
    );
    wrap.num_params = 1;
    env.add_inductive(wrap).expect("add Wrap");
    assert_eq!(env.get_inductive("Wrap").map(|d| d.num_params), Some(1));
    assert_large_elimination_allowed(&env, "Wrap");
}

/// A field that is a proof of a universally quantified proposition (`N -> TrueP`) is a proof.
#[test]
fn proof_of_a_pi_proposition_is_a_proof_field() {
    let mut env = base_env();
    env.add_inductive(decl(
        "AllT",
        prop(),
        vec![(
            "mkall",
            Term::pi(
                Term::pi(ind("N"), ind("TrueP"), BinderInfo::Default),
                ind("AllT"),
                BinderInfo::Default,
            ),
        )],
    ))
    .expect("add AllT");
    assert_large_elimination_allowed(&env, "AllT");
}

/// And-like: `AndP : Prop -> Prop -> Prop` with `intro : (a b : Prop) -> a -> b -> AndP a b`.
#[test]
fn and_like_proposition_allows_large_elimination() {
    let mut env = base_env();
    let and_ab = Term::app(
        Term::app(ind("AndP"), Rc::new(Term::Var(3))),
        Rc::new(Term::Var(2)),
    );
    let mut and_decl = decl(
        "AndP",
        Term::pi(
            prop(),
            Term::pi(prop(), prop(), BinderInfo::Default),
            BinderInfo::Default,
        ),
        vec![(
            "intro",
            Term::pi(
                prop(),
                Term::pi(
                    prop(),
                    Term::pi(
                        Rc::new(Term::Var(1)),
                        Term::pi(Rc::new(Term::Var(1)), and_ab, BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        )],
    );
    and_decl.num_params = 2;
    env.add_inductive(and_decl).expect("add AndP");
    assert_large_elimination_allowed(&env, "AndP");
}

/// A data field (`N`) still blocks large elimination, with or without parameters.
#[test]
fn data_field_blocks_large_elimination() {
    let mut env = base_env();
    env.add_inductive(decl(
        "HasN",
        prop(),
        vec![("mkn", Term::pi(ind("N"), ind("HasN"), BinderInfo::Default))],
    ))
    .expect("add HasN");
    assert_large_elimination_rejected(&env, "HasN");
}

/// Empty propositions (False) may be eliminated into any sort.
#[test]
fn empty_proposition_allows_large_elimination() {
    let mut env = base_env();
    env.add_inductive(decl("FalseP", prop(), vec![]))
        .expect("add FalseP");
    assert_large_elimination_allowed(&env, "FalseP");
}

// =============================================================================
// Binder types must be types
// =============================================================================

fn zero() -> Rc<Term> {
    Rc::new(Term::Ctor("N".to_string(), 0, vec![]))
}

fn assert_expected_sort<T: std::fmt::Debug>(result: Result<T, TypeError>, what: &str) {
    match result {
        Err(TypeError::ExpectedSort(_)) => {}
        other => panic!("expected ExpectedSort for {}, got {:?}", what, other),
    }
}

/// The kernel-API example from the review: `Pi y:zero. zero` (neither side is a type) used to be
/// inferred to have type `N` and was admitted as a definition of type `N`.
#[test]
fn pi_with_non_type_domain_is_rejected() {
    let mut env = base_env();
    let weird = Term::pi(zero(), zero(), BinderInfo::Default);
    assert_expected_sort(
        infer(&env, &Context::new(), weird.clone()),
        "Pi y:zero. zero",
    );
    let def = Definition::total("weird".to_string(), ind("N"), weird);
    assert_expected_sort(env.add_definition(def), "def weird : N := Pi y:zero. zero");
}

#[test]
fn pi_with_non_type_codomain_is_rejected() {
    let env = base_env();
    let pi = Term::pi(ind("N"), zero(), BinderInfo::Default);
    assert_expected_sort(infer(&env, &Context::new(), pi), "Pi y:N. zero");
}

#[test]
fn lambda_with_non_type_binder_is_rejected() {
    let env = base_env();
    let lam = Term::lam(zero(), zero(), BinderInfo::Default);
    assert_expected_sort(infer(&env, &Context::new(), lam), "lam y:zero. zero");
}

#[test]
fn let_with_non_type_annotation_is_rejected() {
    let env = base_env();
    let let_term = Rc::new(Term::LetE(zero(), zero(), zero()));
    assert_expected_sort(
        infer(&env, &Context::new(), let_term),
        "let y:zero = zero in zero",
    );
}

#[test]
fn fix_with_non_type_binder_is_rejected() {
    let env = base_env();
    let fix = Rc::new(Term::Fix(zero(), Rc::new(Term::Var(0))));
    assert_expected_sort(infer(&env, &Context::new(), fix), "fix f:zero. f");
}

/// Well-formed binders are unaffected: `Pi y:N. N : Type`, `Pi P:Prop. P : Prop`,
/// `lam y:N. y : N -> N`.
#[test]
fn well_formed_binders_are_accepted() {
    let env = base_env();
    let pi = Term::pi(ind("N"), ind("N"), BinderInfo::Default);
    assert!(matches!(
        &*infer(&env, &Context::new(), pi).expect("Pi y:N. N"),
        Term::Sort(Level::Succ(_))
    ));
    let impredicative = Term::pi(prop(), Rc::new(Term::Var(0)), BinderInfo::Default);
    assert!(matches!(
        &*infer(&env, &Context::new(), impredicative).expect("Pi P:Prop. P"),
        Term::Sort(Level::Zero)
    ));
    let lam = Rc::new(Term::Lam(
        ind("N"),
        Rc::new(Term::Var(0)),
        BinderInfo::Default,
        FunctionKind::Fn,
    ));
    assert!(infer(&env, &Context::new(), lam).is_ok());
}

/// When the codomain's sort is an opaque alias of `Prop`, the Pi's type is that alias; the alias
/// was computed under the binder, so it must be lowered by one (it used to be returned as is:
/// `G Var(2)`, i.e. `G m` instead of `G n` below), and if it mentions the bound variable the Pi's
/// type is `Prop` itself.
#[test]
fn aliased_prop_sort_of_a_pi_is_well_scoped() {
    let mut env = base_env();
    // G : N -> Type := λ n. Prop (opaque)
    let mut g = Definition::total(
        "G".to_string(),
        Term::pi(ind("N"), type0(), BinderInfo::Default),
        Term::lam(ind("N"), prop(), BinderInfo::Default),
    );
    g.mark_opaque();
    env.add_definition(g).expect("add G");
    let g_of = |arg: Rc<Term>| Term::app(Rc::new(Term::Const("G".to_string(), vec![])), arg);
    let var = |i: usize| Rc::new(Term::Var(i));
    // In [m : N, n : N, b : G n]: Pi (x : N). b  has type  G n  (G Var(1)).
    let ctx = Context::new()
        .push(ind("N"))
        .push(ind("N"))
        .push(g_of(var(0)));
    let ty =
        infer(&env, &ctx, Term::pi(ind("N"), var(1), BinderInfo::Default)).expect("Pi (x : N). b");
    assert_eq!(ty, g_of(var(1)), "expected G n, got {:?}", ty);
    // Pi (x : N). Pi (c : G x). c : the codomain's sort G x mentions x, so the Pi is in Prop.
    let dependent = Term::pi(
        ind("N"),
        Term::pi(g_of(var(0)), var(0), BinderInfo::Default),
        BinderInfo::Default,
    );
    let ty = infer(&env, &Context::new(), dependent).expect("Pi (x : N). Pi (c : G x). c");
    assert!(
        matches!(&*ty, Term::Sort(Level::Zero)),
        "expected Prop, got {:?}",
        ty
    );
}

// =============================================================================
// Inductive declarations: the arity and the constructor types must be types
// =============================================================================

fn type_n(n: u32) -> Rc<Term> {
    let mut level = Level::Zero;
    for _ in 0..n {
        level = Level::Succ(Box::new(level));
    }
    Rc::new(Term::Sort(level))
}

/// An inductive whose arity is an empty proposition (`Bot : FalseP`) made `Ind Bot` a closed
/// proof of `FalseP` (`add_definition oops : FalseP := Bot` was accepted); an arity whose result
/// is a data type (`J : N`) made `Ind J` a non-canonical element of `N`. The arity must end in a
/// sort.
#[test]
fn inductive_arity_must_end_in_a_sort() {
    let mut env = base_env();
    env.add_inductive(decl("FalseP", prop(), vec![]))
        .expect("add FalseP");
    assert_expected_sort(
        env.add_inductive(decl("Bot", ind("FalseP"), vec![])),
        "inductive Bot : FalseP",
    );
    assert!(
        env.add_definition(Definition::total(
            "oops".to_string(),
            ind("FalseP"),
            ind("Bot")
        ))
        .is_err(),
        "a proof of FalseP must not be definable"
    );
    assert_expected_sort(
        env.add_inductive(decl("J", ind("N"), vec![])),
        "inductive J : N",
    );
    assert_expected_sort(
        env.add_inductive(decl(
            "J2",
            Term::pi(ind("N"), ind("N"), BinderInfo::Default),
            vec![],
        )),
        "inductive J2 : N -> N",
    );
}

/// Binder types in the arity and in constructor types must be types (T-Pi applies to them as to
/// any other Pi), for data and for Prop inductives.
#[test]
fn inductive_and_constructor_binder_types_must_be_types() {
    let mut env = base_env();
    assert_expected_sort(
        env.add_inductive(decl(
            "D",
            type0(),
            vec![("mk", Term::pi(zero(), ind("D"), BinderInfo::Default))],
        )),
        "constructor mk : Pi (y : zero). D",
    );
    assert_expected_sort(
        env.add_inductive(decl(
            "I",
            Term::pi(zero(), type0(), BinderInfo::Default),
            vec![],
        )),
        "inductive I : Pi (y : zero). Type",
    );
    assert_expected_sort(
        env.add_inductive(decl(
            "P0",
            prop(),
            vec![("mk", Term::pi(zero(), ind("P0"), BinderInfo::Default))],
        )),
        "constructor mk : Pi (y : zero). P0 (Prop inductive)",
    );
}

/// The constructor's result must apply the inductive to arguments of the arity's binder types.
#[test]
fn constructor_result_must_be_well_typed() {
    let mut env = base_env();
    let result = env.add_inductive(decl(
        "PJ",
        Term::pi(prop(), prop(), BinderInfo::Default),
        vec![("mkj", Term::app(ind("PJ"), zero()))],
    ));
    assert!(
        matches!(result, Err(TypeError::TypeMismatch { .. })),
        "expected TypeMismatch for mkj : PJ zero, got {:?}",
        result
    );
}

/// An arity written through an (opaque) alias of a sort is still allowed, but it no longer
/// bypasses the universe check: `UA : TypeAlias` (= Type) with a field of type `Type 2` is
/// rejected, like `UA : Type` with that field.
#[test]
fn aliased_arity_is_universe_checked() {
    let mut env = base_env();
    let mut alias = Definition::total("TypeAlias".to_string(), type_n(2), type_n(1));
    alias.mark_opaque();
    env.add_definition(alias).expect("add TypeAlias");
    let alias_term = Rc::new(Term::Const("TypeAlias".to_string(), vec![]));
    let result = env.add_inductive(decl(
        "UA",
        alias_term.clone(),
        vec![("mkua", Term::pi(type_n(3), ind("UA"), BinderInfo::Default))],
    ));
    assert!(
        matches!(result, Err(TypeError::UniverseLevelTooSmall(..))),
        "expected UniverseLevelTooSmall, got {:?}",
        result
    );
    // A small field is fine.
    env.add_inductive(decl(
        "UB",
        alias_term,
        vec![("mkub", Term::pi(ind("N"), ind("UB"), BinderInfo::Default))],
    ))
    .expect("UB : TypeAlias with a field of type N");
}

/// `V : Type -> N -> Type` with `vnil : (A : Type) -> V A zero` and
/// `vcons : (A : Type) -> (n : N) -> A -> V A n -> V A (succ n)`.
fn vec_family_decl() -> InductiveDecl {
    let v = |i: usize| Rc::new(Term::Var(i));
    let app = |f: Rc<Term>, a: Rc<Term>| Term::app(f, a);
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    let succ = Rc::new(Term::Ctor("N".to_string(), 1, vec![]));
    let vec_ty = pi(type0(), pi(ind("N"), type0()));
    let vnil = pi(type0(), app(app(ind("V"), v(0)), zero()));
    let vcons = pi(
        type0(),
        pi(
            ind("N"),
            pi(
                v(1),
                pi(
                    app(app(ind("V"), v(2)), v(1)),
                    app(app(ind("V"), v(3)), app(succ, v(2))),
                ),
            ),
        ),
    );
    decl("V", vec_ty, vec![("vnil", vnil), ("vcons", vcons)])
}

/// Well-formed declarations are unaffected: a vector family with a type parameter and an index.
#[test]
fn well_formed_indexed_family_is_accepted() {
    let mut env = base_env();
    env.add_inductive(vec_family_decl()).expect("vector family");
}

// =============================================================================
// Universe rule for inductive declarations (Lean 4 / Coq): in an inductive whose arity ends in
// `Sort u` with `u` not Prop, every constructor FIELD (binder after the uniform parameters)
// has a type whose own sort is at most `u`; parameters and indices are not constrained.
// =============================================================================

fn assert_universe_too_small(result: Result<(), TypeError>, what: &str, expected_detail: &str) {
    match result {
        Err(TypeError::UniverseLevelTooSmall(_, _, _, detail)) => assert!(
            detail.contains(expected_detail),
            "{}: expected the message to mention {:?}, got {:?}",
            what,
            expected_detail,
            detail
        ),
        other => panic!(
            "expected UniverseLevelTooSmall for {}, got {:?}",
            what, other
        ),
    }
}

fn var(i: usize) -> Rc<Term> {
    Rc::new(Term::Var(i))
}

/// `U : Type` with `mkU : Type -> U` (X_verify V1): a field of type `Type` has level 2 (`Type :
/// Type 1`), above `U`'s level 1. The old rule counted a field whose type is literally `Sort l`
/// at level `l`, accepted `U`, and `El : U -> Type` (`El (mkU A) ≡ A`) made `Type` a retract of a
/// type in `Type` (Hurkens' paradox for `Type : Type`).
#[test]
fn type_valued_field_in_a_small_inductive_is_rejected() {
    let mut env = base_env();
    assert_universe_too_small(
        env.add_inductive(decl(
            "U",
            type0(),
            vec![("mkU", Term::pi(type0(), ind("U"), BinderInfo::Default))],
        )),
        "U : Type with mkU : Type -> U",
        "constructor mkU field 0",
    );
    assert!(env.get_inductive("U").is_none(), "U must not be registered");
    // A field of type `Prop` is data too (a proposition, level 1): it is rejected in a data type
    // by the Prop-field rule; a field of type `Type 1` (level 3) by the universe rule.
    assert_universe_too_small(
        env.add_inductive(decl(
            "U1",
            type0(),
            vec![("mkU1", Term::pi(type_n(2), ind("U1"), BinderInfo::Default))],
        )),
        "U1 : Type with mkU1 : Type 1 -> U1",
        "constructor mkU1 field 0",
    );
}

/// The same declaration one universe up is fine: `U2 : Type 1` with `mkU2 : Type -> U2`, and it
/// may be eliminated into `Type 1` (`El : U2 -> Type` is a harmless large elimination).
#[test]
fn type_valued_field_in_a_large_inductive_is_accepted() {
    let mut env = base_env();
    env.add_inductive(decl(
        "U2",
        type_n(2),
        vec![("mkU2", Term::pi(type0(), ind("U2"), BinderInfo::Default))],
    ))
    .expect("U2 : Type 1 with a field of type Type");
    let ty = infer(&env, &Context::new(), ind("U2")).expect("infer U2");
    assert_eq!(ty, type_n(2));
    let rec = Rc::new(Term::Rec(
        "U2".to_string(),
        vec![Level::Succ(Box::new(level1()))],
    ));
    assert!(infer(&env, &Context::new(), rec).is_ok());
}

/// The level is computed from the field type's inferred sort, not from its syntax: a type family
/// `N -> Type` lives in `Type 1` (level 2) and does not fit in a `Type` inductive.
#[test]
fn type_family_field_in_a_small_inductive_is_rejected() {
    let mut env = base_env();
    let family = || Term::pi(ind("N"), type0(), BinderInfo::Default);
    assert_universe_too_small(
        env.add_inductive(decl(
            "F",
            type0(),
            vec![("mkF", Term::pi(family(), ind("F"), BinderInfo::Default))],
        )),
        "F : Type with mkF : (N -> Type) -> F",
        "constructor mkF field 0",
    );
    env.add_inductive(decl(
        "F2",
        type_n(2),
        vec![("mkF2", Term::pi(family(), ind("F2"), BinderInfo::Default))],
    ))
    .expect("F2 : Type 1 with a field of type N -> Type");
}

/// A field whose type's sort is an OPAQUE alias of a sort is checked at the unfolded level (the
/// old rule skipped every field whose sort was not syntactically a `Sort` after reducible
/// normalisation).
#[test]
fn field_whose_sort_is_an_opaque_alias_is_universe_checked() {
    let mut env = base_env();
    let mut big = Definition::total("BigT".to_string(), type_n(3), type_n(2));
    big.mark_opaque();
    env.add_definition(big).expect("add BigT");
    env.add_definition(Definition::axiom(
        "X".to_string(),
        Rc::new(Term::Const("BigT".to_string(), vec![])),
    ))
    .expect("add X : BigT");
    let x = || Rc::new(Term::Const("X".to_string(), vec![]));
    assert_universe_too_small(
        env.add_inductive(decl(
            "W",
            type0(),
            vec![("mkw", Term::pi(x(), ind("W"), BinderInfo::Default))],
        )),
        "W : Type with mkw : X -> W (X : BigT, BigT := Type 1 opaque)",
        "constructor mkw field 0",
    );
    env.add_inductive(decl(
        "W2",
        type_n(2),
        vec![("mkw2", Term::pi(x(), ind("W2"), BinderInfo::Default))],
    ))
    .expect("W2 : Type 1 with a field of type X");
}

/// Type parameters are not fields: List-, Pair- and Vec-style declarations in `Type` whose
/// constructors repeat their `Type` parameters as leading binders are accepted, and the fields
/// typed by a parameter (`A : Type`, level 1) fit.
#[test]
fn type_parameters_are_not_fields() {
    let mut env = base_env();
    let app = |f: Rc<Term>, a: Rc<Term>| Term::app(f, a);
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    // L : Type -> Type; lnil : (A : Type) -> L A; lcons : (A : Type) -> A -> L A -> L A
    let lnil = pi(type0(), app(ind("L"), var(0)));
    let lcons = pi(
        type0(),
        pi(var(0), pi(app(ind("L"), var(1)), app(ind("L"), var(2)))),
    );
    env.add_inductive(decl(
        "L",
        pi(type0(), type0()),
        vec![("lnil", lnil), ("lcons", lcons)],
    ))
    .expect("list-style inductive");
    assert_eq!(env.get_inductive("L").map(|d| d.num_params), Some(1));
    // P : Type -> Type -> Type; mkp : (A B : Type) -> A -> B -> P A B
    let mkp = pi(
        type0(),
        pi(
            type0(),
            pi(var(1), pi(var(1), app(app(ind("P"), var(3)), var(2)))),
        ),
    );
    env.add_inductive(decl(
        "P",
        pi(type0(), pi(type0(), type0())),
        vec![("mkp", mkp)],
    ))
    .expect("pair-style inductive");
    assert_eq!(env.get_inductive("P").map(|d| d.num_params), Some(2));
    env.add_inductive(vec_family_decl()).expect("vector family");
    assert_eq!(env.get_inductive("V").map(|d| d.num_params), Some(1));
    // A parameter in a larger universe than the inductive is not constrained either:
    // Ph : Type 1 -> Type; mkph : (A : Type 1) -> Ph A.
    env.add_inductive(decl(
        "Ph",
        pi(type_n(2), type0()),
        vec![("mkph", pi(type_n(2), app(ind("Ph"), var(0))))],
    ))
    .expect("phantom parameter in Type 1");
    assert_eq!(env.get_inductive("Ph").map(|d| d.num_params), Some(1));
}

/// Indices are not constrained: `T : Type -> Type` with `mkT : T N` (a type-valued index, as in
/// a type-indexed family) lives in `Type`, and so does `T2 : Type 1 -> Type` with `mkT2 : T2 Type`.
#[test]
fn type_valued_indices_are_not_constrained() {
    let mut env = base_env();
    env.add_inductive(decl(
        "T",
        Term::pi(type0(), type0(), BinderInfo::Default),
        vec![("mkT", Term::app(ind("T"), ind("N")))],
    ))
    .expect("type-indexed family");
    assert_eq!(env.get_inductive("T").map(|d| d.num_params), Some(0));
    env.add_inductive(decl(
        "T2",
        Term::pi(type_n(2), type0(), BinderInfo::Default),
        vec![("mkT2", Term::app(ind("T2"), type0()))],
    ))
    .expect("family indexed by Type 1");
}

/// Propositions are not universe-constrained (impredicative `Prop`): `PT : Prop` with
/// `mkPT : Type -> PT` is accepted, but it is not large-eliminable (its field is data, not a
/// proof), so no type can be extracted from a proof of it.
#[test]
fn proposition_with_a_type_valued_field_is_accepted_but_not_large_eliminable() {
    let mut env = base_env();
    env.add_inductive(decl(
        "PT",
        prop(),
        vec![("mkPT", Term::pi(type0(), ind("PT"), BinderInfo::Default))],
    ))
    .expect("PT : Prop with a field of type Type");
    assert_large_elimination_rejected(&env, "PT");
    let small = Rc::new(Term::Rec("PT".to_string(), vec![Level::Zero]));
    assert!(infer(&env, &Context::new(), small).is_ok());
}

// -----------------------------------------------------------------------------
// Level comparison in the universe rule: `v <= u` must hold for EVERY assignment of the level
// parameters (Lean 4's `is_geq`), and `imax a u` is not `max a u` (u may be 0).
// -----------------------------------------------------------------------------

fn lsucc(l: Level) -> Level {
    Level::Succ(Box::new(l))
}

fn lparam(name: &str) -> Level {
    Level::Param(name.to_string())
}

fn lmax(a: Level, b: Level) -> Level {
    Level::Max(Box::new(a), Box::new(b))
}

fn limax(a: Level, b: Level) -> Level {
    Level::IMax(Box::new(a), Box::new(b))
}

fn sort(l: Level) -> Rc<Term> {
    Rc::new(Term::Sort(l))
}

fn poly_decl(
    name: &str,
    univ_params: &[&str],
    ty: Rc<Term>,
    ctors: Vec<(&str, Rc<Term>)>,
) -> InductiveDecl {
    InductiveDecl {
        univ_params: univ_params.iter().map(|p| p.to_string()).collect(),
        ..decl(name, ty, ctors)
    }
}

/// Accepted as in Lean 4: `T.{u,v} : Sort (max u v + 1)` with a field of type `Sort u` (level
/// `u + 1 <= max u v + 1`), and `Prod.{u,v} : Type u -> Type v -> Type (max u v)` (also with the
/// arity written `Sort (max (u+1) (v+1))`). The comparison used to peel a `succ` off the right
/// side only, so it never compared `u + 1` with `max u v + 1` offset by offset.
#[test]
fn universe_rule_compares_levels_offset_by_offset() {
    let (u, v) = (|| lparam("u"), || lparam("v"));
    let mut env = base_env();
    env.add_inductive(poly_decl(
        "T1",
        &["u", "v"],
        sort(lsucc(lmax(u(), v()))),
        vec![("mk1", pi(sort(u()), ind("T1")))],
    ))
    .expect("T1.{u,v} : Sort (max u v + 1) with a field of type Sort u");
    for (name, ctor, result) in [
        ("P2", "mkp2", lsucc(lmax(u(), v()))),
        ("P3", "mkp3", lmax(lsucc(u()), lsucc(v()))),
    ] {
        let mk = pi(
            sort(lsucc(u())),
            pi(
                sort(lsucc(v())),
                pi(
                    var(1),
                    pi(var(1), Term::app(Term::app(ind(name), var(3)), var(2))),
                ),
            ),
        );
        env.add_inductive(poly_decl(
            name,
            &["u", "v"],
            pi(sort(lsucc(u())), pi(sort(lsucc(v())), sort(result))),
            vec![(ctor, mk)],
        ))
        .unwrap_or_else(|e| {
            panic!(
                "{}: Prod.{{u,v}} : Type u -> Type v -> Type (max u v): {:?}",
                name, e
            )
        });
        assert_eq!(env.get_inductive(name).map(|d| d.num_params), Some(2));
    }
}

/// Rejected as in Lean 4, because the inequality fails for some assignment: a `Sort u` field in a
/// `Sort u` inductive; an `N` field (level 1) in `Sort (imax 1 u)` and a `Type` field (level 2) in
/// `Sort (imax 2 u)` (both are `Sort 0` when `u = 0`; `imax` over a parameter used to be
/// normalised to `max`); a `Sort u` field in `Sort (max 1 u)` (fails for `u >= 1`).
#[test]
fn universe_rule_rejects_levels_that_fail_for_some_assignment() {
    let u = || lparam("u");
    let one = || lsucc(Level::Zero);
    let cases: Vec<(&str, Level, Rc<Term>, &str)> = vec![
        ("T4", u(), sort(u()), "field 0"),
        ("T5", limax(one(), u()), ind("N"), "field 0"),
        ("T6", limax(lsucc(one()), u()), type0(), "field 0"),
        ("T7", lmax(one(), u()), sort(u()), "field 0"),
    ];
    for (name, level, field, detail) in cases {
        let mut env = base_env();
        assert_universe_too_small(
            env.add_inductive(poly_decl(
                name,
                &["u"],
                sort(level),
                vec![("mk", pi(field, ind(name)))],
            )),
            name,
            detail,
        );
        assert!(
            env.get_inductive(name).is_none(),
            "{} must not be registered",
            name
        );
    }
}

/// `normalize_level` is exact for every parameter assignment: `imax a u` stays an `imax` when `u`
/// may be 0, and becomes `max` only when the right side is provably nonzero.
#[test]
fn imax_over_a_parameter_is_not_max() {
    use kernel::ast::{level_eq, normalize_level};
    let u = || lparam("u");
    let one = || lsucc(Level::Zero);
    assert!(matches!(
        normalize_level(limax(one(), u())),
        Level::IMax(_, _)
    ));
    assert!(!level_eq(&limax(one(), u()), &lmax(one(), u())));
    assert!(level_eq(
        &limax(one(), lsucc(u())),
        &lmax(one(), lsucc(u()))
    ));
    assert!(level_eq(&limax(u(), Level::Zero), &Level::Zero));
    assert!(level_eq(&limax(Level::Zero, u()), &u()));
    assert!(level_eq(&limax(u(), u()), &u()));
    assert!(level_eq(&limax(one(), one()), &one()));
}

/// Y2_recheck L1: `normalize_level` writes `max (succ a) (succ b)` as `succ (max a b)` (Lean's
/// normal form distributes `succ` over `max`), and the offset comparison then compared
/// `succ^2 (max u v)` with `succ u` base by base and failed. Accepted as in Lean 4:
/// `T.{u,v} : Sort (max u v + 2)` with a field of type `Sort u` (level `u + 1`) or `Sort v`, and
/// `Sort (max u v + 1)` with a field of type `Sort (max u v)`. Still rejected (fails for some
/// assignment): `Sort (max u v + 1)` with a field of type `Sort (v + 1)` (level `v + 2`).
#[test]
fn universe_rule_distributes_succ_over_max() {
    let (u, v) = (|| lparam("u"), || lparam("v"));
    let mut env = base_env();
    for (name, field) in [("L1u", sort(u())), ("L1v", sort(v()))] {
        env.add_inductive(poly_decl(
            name,
            &["u", "v"],
            sort(lsucc(lsucc(lmax(u(), v())))),
            vec![("mk", pi(field, ind(name)))],
        ))
        .unwrap_or_else(|e| panic!("{}: Sort (max u v + 2) with a Sort field: {:?}", name, e));
    }
    env.add_inductive(poly_decl(
        "L1m",
        &["u", "v"],
        sort(lsucc(lmax(u(), v()))),
        vec![("mk", pi(sort(lmax(u(), v())), ind("L1m")))],
    ))
    .expect("Sort (max u v + 1) with a field of type Sort (max u v)");
    assert_universe_too_small(
        env.add_inductive(poly_decl(
            "L6",
            &["u", "v"],
            sort(lsucc(lmax(u(), v()))),
            vec![("mk", pi(sort(lsucc(v())), ind("L6")))],
        )),
        "L6",
        "field 0",
    );
    assert!(
        env.get_inductive("L6").is_none(),
        "L6 must not be registered"
    );
}

// -----------------------------------------------------------------------------
// Elimination restriction for inductives that MAY be propositions: an arity ending in a sort
// whose level is not provably nonzero (`Sort u`, `Sort (imax 1 u)`) is `Prop` for some
// assignment of the level parameters, so (as in Lean 4) the inductive eliminates only into
// `Prop` unless it is empty, has one constructor whose fields are all proofs, or is equality.
// -----------------------------------------------------------------------------

fn rec_poly(name: &str, levels: Vec<Level>) -> Rc<Term> {
    Rc::new(Term::Rec(name.to_string(), levels))
}

/// Y2_recheck H1f/H1g: `I.{u} : Sort (imax 1 u)` and `PU.{u} : Sort u` with two field-less
/// constructors were large-eliminable (`Rec I [0, 1]` was accepted); for `u = 0` they are
/// propositions with two constructors.
#[test]
fn inductive_that_may_be_a_proposition_has_the_elimination_restriction() {
    let u = || lparam("u");
    let one = || lsucc(Level::Zero);
    let mut env = base_env();
    for (name, level) in [("I6", limax(one(), u())), ("PU", u())] {
        env.add_inductive(poly_decl(
            name,
            &["u"],
            sort(level),
            vec![("c1", ind(name)), ("c2", ind(name))],
        ))
        .unwrap_or_else(|e| panic!("add {}: {:?}", name, e));
        for inst in [Level::Zero, one(), u()] {
            match infer(
                &env,
                &Context::new(),
                rec_poly(name, vec![inst.clone(), one()]),
            ) {
                Err(TypeError::LargeElimination(found)) => assert_eq!(found, name),
                other => panic!(
                    "expected LargeElimination for Rec {} [{:?}, 1], got {:?}",
                    name, inst, other
                ),
            }
        }
        let into_prop = infer(
            &env,
            &Context::new(),
            rec_poly(name, vec![u(), Level::Zero]),
        );
        assert!(
            into_prop.is_ok(),
            "elimination of {} into Prop stays allowed: {:?}",
            name,
            into_prop
        );
    }
    // `W.{u} (A : Sort u) : Sort u` with `mk : A -> W A`: one constructor, but its field is not
    // a proof for every u.
    env.add_inductive(InductiveDecl {
        num_params: 1,
        ..poly_decl(
            "W",
            &["u"],
            pi(sort(u()), sort(u())),
            vec![("mk", pi(sort(u()), pi(var(0), Term::app(ind("W"), var(1)))))],
        )
    })
    .expect("add W");
    match infer(&env, &Context::new(), rec_poly("W", vec![u(), one()])) {
        Err(TypeError::LargeElimination(found)) => assert_eq!(found, "W"),
        other => panic!("expected LargeElimination for W, got {:?}", other),
    }
}

/// Controls: an arity whose level is provably nonzero (`Sort (max 1 u)`, `Sort (u + 1)`) is not
/// a proposition, and a may-be-proposition with one field-less constructor or with no
/// constructor eliminates into any sort.
#[test]
fn provably_nonzero_or_subsingleton_inductives_eliminate_into_types() {
    let u = || lparam("u");
    let one = || lsucc(Level::Zero);
    let mut env = base_env();
    for (name, level) in [("M1", lmax(one(), u())), ("S1", lsucc(u()))] {
        env.add_inductive(poly_decl(
            name,
            &["u"],
            sort(level),
            vec![("c1", ind(name)), ("c2", ind(name))],
        ))
        .unwrap_or_else(|e| panic!("add {}: {:?}", name, e));
    }
    env.add_inductive(poly_decl("U1", &["u"], sort(u()), vec![("tt1", ind("U1"))]))
        .expect("add U1");
    env.add_inductive(poly_decl("E0", &["u"], sort(u()), vec![]))
        .expect("add E0");
    for name in ["M1", "S1", "U1", "E0"] {
        let r = infer(&env, &Context::new(), rec_poly(name, vec![u(), one()]));
        assert!(
            r.is_ok(),
            "expected large elimination of {} to be allowed, got {:?}",
            name,
            r
        );
    }
}

// =============================================================================
// Strict positivity (Lean 4 / Coq): the inductive may occur in a constructor field only as the
// head of the field type or of a Pi codomain in it, applied to its parameters; never inside the
// domain of a Pi, at any depth, and a `let` cannot hide an occurrence.
// =============================================================================

fn false_p() -> Rc<Term> {
    ind("FalseP")
}

fn env_with_false() -> Env {
    let mut env = base_env();
    env.add_inductive(decl("FalseP", prop(), vec![]))
        .expect("add FalseP");
    env
}

fn assert_non_positive(result: Result<(), TypeError>, what: &str) {
    match result {
        Err(TypeError::NonPositiveOccurrence(_, _, _)) => {}
        other => panic!(
            "expected NonPositiveOccurrence for {}, got {:?}",
            what, other
        ),
    }
}

/// Verifier finding (Y2 soundness F1): `mk : (let X : Prop := Bad in X -> False) -> Bad` is
/// `mk : (Bad -> False) -> Bad`. The positivity check used to check the let's value at the
/// current polarity and its body with `X` as an ordinary variable, so it accepted `Bad`, and
/// `boom := omega (mk omega)` with `omega := fun b => unroll b b` was a closed proof of False.
#[test]
fn negative_occurrence_behind_a_let_is_rejected() {
    let mut env = env_with_false();
    // control: the same field without the let
    assert_non_positive(
        env.add_inductive(decl(
            "Bad0",
            prop(),
            vec![("mk0", pi(pi(ind("Bad0"), false_p()), ind("Bad0")))],
        )),
        "Bad0 (plain negative field)",
    );
    let let_field = Rc::new(Term::LetE(prop(), ind("Bad"), pi(var(0), false_p())));
    assert_non_positive(
        env.add_inductive(decl("Bad", prop(), vec![("mk", pi(let_field, ind("Bad")))])),
        "Bad (negative field behind a let)",
    );
    assert!(
        env.get_inductive("Bad").is_none(),
        "Bad must not be registered"
    );
    // deeper: under a Pi codomain, behind two lets
    let deep_field = pi(
        ind("N"),
        Rc::new(Term::LetE(
            prop(),
            ind("Bad2"),
            Rc::new(Term::LetE(prop(), pi(var(0), false_p()), var(0))),
        )),
    );
    assert_non_positive(
        env.add_inductive(decl(
            "Bad2",
            prop(),
            vec![("mk2", pi(deep_field, ind("Bad2")))],
        )),
        "Bad2 (negative field behind two lets under a Pi)",
    );
}

/// Positive but not strictly positive occurrences: `((Bad -> False) -> False) -> Bad` and the
/// Coquand-Paulin type `intro : ((A -> Prop) -> Prop) -> A`, which with an impredicative Prop
/// gives a proof of False (the CLI test `non_strictly_positive_inductive_is_rejected` builds
/// it). The check used to flip the polarity at every arrow, so two arrows made it positive.
#[test]
fn non_strictly_positive_occurrence_is_rejected() {
    let mut env = env_with_false();
    assert_non_positive(
        env.add_inductive(decl(
            "DN",
            prop(),
            vec![("mk", pi(pi(pi(ind("DN"), false_p()), false_p()), ind("DN")))],
        )),
        "DN : Prop with mk : ((DN -> False) -> False) -> DN",
    );
    let powerset = pi(pi(pi(ind("A"), prop()), prop()), ind("A"));
    assert_non_positive(
        env.add_inductive(decl("A", type0(), vec![("intro", powerset)])),
        "A : Type with intro : ((A -> Prop) -> Prop) -> A",
    );
    assert!(env.get_inductive("A").is_none(), "A must not be registered");
}

/// Controls: strictly positive occurrences are accepted: an infinitary field `N -> Tr`, and a
/// recursive field written through a `let` (the declaration is stored zeta-expanded, so the
/// field is a recursive argument: the recursor's minor premise for `lcons` takes its induction
/// hypothesis).
#[test]
fn strictly_positive_occurrences_are_accepted() {
    let mut env = base_env();
    env.add_inductive(decl(
        "Tr",
        type0(),
        vec![
            ("lf", ind("Tr")),
            ("nd", pi(pi(ind("N"), ind("Tr")), ind("Tr"))),
        ],
    ))
    .expect("infinitary tree");
    let let_tail = Rc::new(Term::LetE(type0(), ind("L"), var(0)));
    env.add_inductive(decl(
        "L",
        type0(),
        vec![
            ("lnil", ind("L")),
            ("lcons", pi(ind("N"), pi(let_tail, ind("L")))),
        ],
    ))
    .expect("list with a let-bound tail type");
    let stored = env.get_inductive("L").expect("L registered");
    assert_eq!(
        stored.ctors[1].ty,
        pi(ind("N"), pi(ind("L"), ind("L"))),
        "the constructor type is stored zeta-expanded"
    );
    // Rec L [1] (fun _ => N) zero (fun h t ih => succ ih) is well typed (the minor premise for
    // lcons takes an ih), and a minor premise without the ih is not.
    let succ = || Rc::new(Term::Ctor("N".to_string(), 1, vec![]));
    let zero_n = || Rc::new(Term::Ctor("N".to_string(), 0, vec![]));
    // (the motive is an ordinary function, the minor premises are once-only)
    let lam = |ty: Rc<Term>, body: Rc<Term>| {
        Rc::new(Term::Lam(
            ty,
            body,
            BinderInfo::Default,
            FunctionKind::FnOnce,
        ))
    };
    let rec_with = |minor_cons: Rc<Term>| {
        Term::app(
            Term::app(
                Term::app(
                    rec_into_type("L"),
                    Term::lam(ind("L"), ind("N"), BinderInfo::Default),
                ),
                zero_n(),
            ),
            minor_cons,
        )
    };
    let with_ih = lam(
        ind("N"),
        lam(ind("L"), lam(ind("N"), Term::app(succ(), var(0)))),
    );
    let r = infer(&env, &Context::new(), rec_with(with_ih));
    assert!(
        r.is_ok(),
        "the recursor's minor premise for lcons takes the induction hypothesis: {:?}",
        r
    );
    let without_ih = lam(ind("N"), lam(ind("L"), zero_n()));
    assert!(infer(&env, &Context::new(), rec_with(without_ih)).is_err());
}

/// A nested occurrence hidden behind a let (`let X := T in Box X`) is still nested.
#[test]
fn nested_occurrence_behind_a_let_is_rejected() {
    let mut env = base_env();
    env.add_inductive(decl(
        "Box",
        pi(type0(), type0()),
        vec![(
            "box",
            pi(type0(), pi(var(0), Term::app(ind("Box"), var(1)))),
        )],
    ))
    .expect("Box");
    let field = Rc::new(Term::LetE(type0(), ind("T"), Term::app(ind("Box"), var(0))));
    match env.add_inductive(decl(
        "T",
        type0(),
        vec![("leaf", ind("T")), ("node", pi(field, ind("T")))],
    )) {
        Err(TypeError::NestedInductive { .. }) => {}
        other => panic!("expected NestedInductive, got {:?}", other),
    }
}

/// Y2_recheck z04: the inductive being declared in an index of a constructor's result type,
/// `base : T (T TrueP -> FalseP)` for `T : Prop -> Prop`, was accepted. Lean 4 and Coq reject
/// any occurrence of the inductive in the arguments of a constructor's result type (K0015).
/// Indices that do not mention the inductive are still accepted.
#[test]
fn inductive_in_a_result_index_is_rejected() {
    let mut env = env_with_false();
    let bad_index = pi(Term::app(ind("T"), ind("TrueP")), false_p());
    match env.add_inductive(decl(
        "T",
        pi(prop(), prop()),
        vec![("base", Term::app(ind("T"), bad_index))],
    )) {
        Err(err @ TypeError::InductiveInCtorResultArg { .. }) => {
            assert_eq!(err.diagnostic_code(), "K0015");
            match err {
                TypeError::InductiveInCtorResultArg { ind, ctor, arg } => {
                    assert_eq!((ind.as_str(), ctor.as_str(), arg), ("T", "base", 0));
                }
                _ => unreachable!(),
            }
        }
        other => panic!("expected InductiveInCtorResultArg, got {:?}", other),
    }
    assert!(env.get_inductive("T").is_none(), "T must not be registered");
    // the same occurrence behind a let in the result index
    let let_index = Rc::new(Term::LetE(
        pi(prop(), prop()),
        ind("T2"),
        pi(Term::app(var(0), ind("TrueP")), false_p()),
    ));
    match env.add_inductive(decl(
        "T2",
        pi(prop(), prop()),
        vec![("base2", Term::app(ind("T2"), let_index))],
    )) {
        Err(TypeError::InductiveInCtorResultArg { .. }) => {}
        other => panic!("expected InductiveInCtorResultArg for T2, got {:?}", other),
    }
    // control: an index that does not mention the inductive
    env.add_inductive(decl(
        "T3",
        pi(prop(), prop()),
        vec![("base3", Term::app(ind("T3"), pi(ind("TrueP"), false_p())))],
    ))
    .expect("index without the inductive");
}

// =============================================================================
// A failed inductive declaration leaves nothing behind
// =============================================================================

/// Verifier finding (Y2 soundness F2): a `copy` inductive whose Copy derivation fails was
/// reported as failed but its zero-constructor placeholder stayed in the environment (only a
/// failed soundness check removed it): later terms could use `CF` as an empty type and a
/// corrected re-declaration failed with "already exists".
#[test]
fn failed_copy_derivation_leaves_no_placeholder() {
    let mut env = base_env();
    let copy_cf = InductiveDecl {
        is_copy: true,
        ..decl(
            "CF",
            type0(),
            vec![("cf", pi(pi(ind("N"), ind("N")), ind("CF")))],
        )
    };
    match env.add_inductive(copy_cf) {
        Err(TypeError::CopyDeriveFailure { .. }) => {}
        other => panic!("expected CopyDeriveFailure, got {:?}", other),
    }
    assert!(env.get_inductive("CF").is_none(), "no placeholder for CF");
    assert!(infer(&env, &Context::new(), ind("CF")).is_err());
    env.add_inductive(decl("CF", type0(), vec![("cf2", ind("CF"))]))
        .expect("corrected re-declaration");
    assert_eq!(env.get_inductive("CF").map(|d| d.ctors.len()), Some(1));
}

// =============================================================================
// Lifetime elision: once per complete signature
// =============================================================================

fn ref_shared_nat(label: Option<&str>) -> Rc<Term> {
    let ref_const = Rc::new(Term::Const("Ref".to_string(), vec![]));
    let shared_const = Rc::new(Term::Const("Shared".to_string(), vec![]));
    Term::app_with_label(
        Term::app(ref_const, shared_const),
        ind("N"),
        label.map(|l| l.to_string()),
    )
}

fn pi(dom: Rc<Term>, cod: Rc<Term>) -> Rc<Term> {
    Term::pi(dom, cod, BinderInfo::Default)
}

/// `(pi a (Ref Shared N) (pi n N (Ref Shared N)))`: one input lifetime in the whole signature.
/// The check used to run on the suffix `(pi n N (Ref Shared N))` too, which has none.
#[test]
fn one_input_reference_followed_by_a_value_argument_is_unambiguous() {
    let sig = pi(ref_shared_nat(None), pi(ind("N"), ref_shared_nat(None)));
    assert!(
        validate_core_term(&sig).is_ok(),
        "{:?}",
        validate_core_term(&sig)
    );
    let labelled = pi(
        ref_shared_nat(Some("a")),
        pi(ind("N"), ref_shared_nat(None)),
    );
    assert!(validate_core_term(&labelled).is_ok());
    let last = pi(ind("N"), pi(ref_shared_nat(None), ref_shared_nat(None)));
    assert!(validate_core_term(&last).is_ok());
}

#[test]
fn ambiguous_signatures_are_still_rejected() {
    let two = pi(
        ref_shared_nat(None),
        pi(ref_shared_nat(None), ref_shared_nat(None)),
    );
    assert!(matches!(
        validate_core_term(&two),
        Err(TypeError::AmbiguousRefLifetime)
    ));
    let none = pi(ind("N"), ref_shared_nat(None));
    assert!(matches!(
        validate_core_term(&none),
        Err(TypeError::AmbiguousRefLifetime)
    ));
    // A function-typed argument is a signature of its own: the outer signature is unambiguous
    // (its result is labelled), but the argument's signature `(pi n N (Ref Shared N))` has no
    // input lifetime.
    let higher_order = pi(
        ref_shared_nat(Some("a")),
        pi(
            pi(ind("N"), ref_shared_nat(None)),
            ref_shared_nat(Some("a")),
        ),
    );
    assert!(matches!(
        validate_core_term(&higher_order),
        Err(TypeError::AmbiguousRefLifetime)
    ));
}

// =============================================================================
// Recursor minor premises: a constructor field that follows a recursive field, and whose type
// depends on an earlier field, must keep its declared type. The minor-premise builder inserts an
// induction-hypothesis binder after every recursive field; it used to shift EVERY later field
// type / index by the total number of induction hypotheses, which mis-indexed references to the
// fields that follow a recursive field. The kernel then demanded the wrong type for such a
// field, so a minor premise binding it at a different type was accepted while iota reduction
// applied the correctly typed field value — subject reduction failed, and a closed proof of an
// empty inductive could be built. (K_repair, from H_inductives #1 / H_universes_elim #1.)
// =============================================================================

fn lam1(ty: Rc<Term>, body: Rc<Term>) -> Rc<Term> {
    Term::lam_with_kind(ty, body, BinderInfo::Default, FunctionKind::FnOnce)
}

/// `N`, plus `Tg : N -> Type` (`tgm : (k : N) -> Tg k`) and `T : Type` with `leaf : T` and
/// `node : (r : T) -> (a : N) -> (w : Tg a) -> T`: `w` follows the recursive field `r` and
/// depends on the earlier field `a`.
fn env_with_dep_field_after_rec() -> Env {
    let mut env = base_env();
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    let app = |f: Rc<Term>, a: Rc<Term>| Term::app(f, a);
    // Tg : N -> Type, tgm : (k : N) -> Tg k
    env.add_inductive(decl(
        "Tg",
        pi(ind("N"), type0()),
        vec![("tgm", pi(ind("N"), app(ind("Tg"), var(0))))],
    ))
    .expect("add Tg");
    // node : (r : T) -> (a : N) -> (w : Tg a) -> T
    let node_ty = pi(ind("T"), pi(ind("N"), pi(app(ind("Tg"), var(0)), ind("T"))));
    env.add_inductive(decl(
        "T",
        type0(),
        vec![("leaf", ind("T")), ("node", node_ty)],
    ))
    .expect("add T");
    env
}

/// Walk `n` leading `Pi` binders of `ty`, returning the domain of binder `n` (0-based).
fn nth_pi_domain(ty: &Rc<Term>, n: usize) -> Rc<Term> {
    let mut curr = ty.clone();
    let mut i = 0;
    while let Term::Pi(dom, body, _, _) = &*curr.clone() {
        if i == n {
            return dom.clone();
        }
        curr = body.clone();
        i += 1;
    }
    panic!("type has fewer than {} Pi binders: {:?}", n + 1, ty);
}

#[test]
fn dependent_field_after_a_recursive_field_keeps_its_declared_type() {
    let env = env_with_dep_field_after_rec();
    let decl_t = env.get_inductive("T").expect("T");
    // Recursor type for a motive into `Type`. Binders: [motive] [leaf minor] [node minor] ...
    let rec_ty = compute_recursor_type(decl_t, &[level1()]);
    let node_minor = nth_pi_domain(&rec_ty, 2);
    // node minor telescope: [r : T] [ih : C r] [a : N] [w : Tg a]. In the context [r, ih, a],
    // the earlier field `a` is Var(0), so the declared type of `w` is `Tg (Var 0)`.
    let w_binder = nth_pi_domain(&node_minor, 3);
    let expected = Term::app(ind("Tg"), var(0));
    assert_eq!(
        w_binder, expected,
        "w must be bound at Tg a = Tg (Var 0); the buggy shift gave Tg (Var 1) = Tg ih"
    );
}

/// A motive `C : T -> N` by `Rec T`, whose `node` minor binds `w` at its declared type `Tg a`,
/// is accepted; binding `w` at `Tg ih` (the type the buggy recursor demanded) is rejected, since
/// that is not the type `Rec T` gives the minor premise.
#[test]
fn minor_premise_binding_a_field_at_the_wrong_type_is_rejected() {
    let env = env_with_dep_field_after_rec();
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    let app = |f: Rc<Term>, a: Rc<Term>| Term::app(f, a);
    let rec_t = Rc::new(Term::Rec("T".to_string(), vec![level1()]));
    // Motive C : T -> Type, taken as the constant family `lam _ : T. N`.
    let motive = Term::lam(ind("T"), ind("N"), BinderInfo::Default);

    // leaf minor : C leaf = N
    let leaf_minor = zero();

    // honest node minor : (r : T) -> (ih : N) -> (a : N) -> (w : Tg a) -> N, body = a (Var 1).
    let honest_node = lam1(
        ind("T"),
        lam1(
            ind("N"),
            lam1(ind("N"), lam1(app(ind("Tg"), var(0)), var(1))),
        ),
    );
    let honest_body = Term::lam(
        ind("T"),
        Term::app(
            Term::app(
                Term::app(Term::app(rec_t.clone(), motive.clone()), leaf_minor.clone()),
                honest_node,
            ),
            var(0),
        ),
        BinderInfo::Default,
    );
    let honest = Definition::total("size_ok".to_string(), pi(ind("T"), ind("N")), honest_body);
    assert!(
        Env::add_definition(&mut env.clone(), honest).is_ok(),
        "the minor premise binding w at its declared type Tg a must be accepted"
    );

    // bogus node minor : binds w at Tg ih (ih = Var 2 in [r, ih, a, w]); body = ih (Var 2).
    let bogus_node = lam1(
        ind("T"),
        lam1(
            ind("N"),
            lam1(ind("N"), lam1(app(ind("Tg"), var(2)), var(2))),
        ),
    );
    let bogus_body = Term::lam(
        ind("T"),
        Term::app(
            Term::app(Term::app(Term::app(rec_t, motive), leaf_minor), bogus_node),
            var(0),
        ),
        BinderInfo::Default,
    );
    let bogus = Definition::total("size_bad".to_string(), pi(ind("T"), ind("N")), bogus_body);
    match Env::add_definition(&mut env.clone(), bogus) {
        Err(TypeError::TypeMismatch { .. }) => {}
        other => panic!(
            "binding w at Tg ih must be rejected (TypeMismatch), got {:?}",
            other
        ),
    }
}

// =============================================================================
// Recursor type for a family with a dependent index telescope: each index binder's type is
// written over [params] [earlier indices]; in the recursor it must still refer to the earlier
// indices, not to the motive or a minor. The binder used to be shifted at cutoff 0 by
// `1 + #minors`, which moved references to earlier indices onto the motive, so the recursor type
// was not even well-formed and such a family could not be eliminated. (K_repair, H_universes_elim #3.)
// =============================================================================

#[test]
fn recursor_of_a_dependent_index_family_is_well_formed() {
    let mut env = base_env();
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    // D : (A : Type) -> (x : A) -> Type, dmk : D N zero
    env.add_inductive(decl(
        "D",
        pi(type0(), pi(var(0), type0())),
        vec![("dmk", Term::app(Term::app(ind("D"), ind("N")), zero()))],
    ))
    .expect("add D");
    let decl_d = env.get_inductive("D").expect("D");
    let rec_ty = compute_recursor_type(decl_d, &[level1()]);
    // Binders: [motive] [dmk minor] [A : Type] [x : A] [major]. The type of `x` is the earlier
    // index `A`, which in the context [motive, minor, A] is Var(0) — not the motive (Var 2).
    let x_binder = nth_pi_domain(&rec_ty, 3);
    assert_eq!(
        x_binder,
        var(0),
        "index x must be typed by the earlier index A"
    );
    // The recursor type is well-formed: inferring its own type returns a sort.
    let rec_term = Rc::new(Term::Rec("D".to_string(), vec![level1()]));
    let computed = infer(&env, &Context::new(), rec_term).expect("Rec D infers");
    assert!(
        infer(&env, &Context::new(), computed).is_ok(),
        "the recursor type of D must be well-formed (a sort)"
    );
}

// =============================================================================
// Termination: the recursor's induction-hypothesis binders are the recursor's result on a field,
// not subterms of the major premise, so a recursive call on an IH is not structural; the fields
// of a recursor are smaller only when the major premise is the decreasing argument (or already
// smaller); and a recursive call must supply the decreasing argument. Each hole below let a
// non-terminating definition be accepted as total, from which a closed proof of an empty
// inductive followed. (K_repair, H_universes_elim #4 and related.)
// =============================================================================

/// `B` (`bt`, `bf`), `W : B -> Type` (`base : W bt`, `step : W bt -> W bf`), `Empty1 : Type`.
fn env_with_w() -> Env {
    let mut env = base_env();
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    let app = |f: Rc<Term>, a: Rc<Term>| Term::app(f, a);
    env.add_inductive(decl("B", type0(), vec![("bt", ind("B")), ("bf", ind("B"))]))
        .expect("add B");
    let bt = Rc::new(Term::Ctor("B".to_string(), 0, vec![]));
    let bf = Rc::new(Term::Ctor("B".to_string(), 1, vec![]));
    env.add_inductive(decl(
        "W",
        pi(ind("B"), type0()),
        vec![
            ("base", app(ind("W"), bt.clone())),
            ("step", pi(app(ind("W"), bt), app(ind("W"), bf))),
        ],
    ))
    .expect("add W");
    env.add_inductive(decl("Empty1", type0(), vec![]))
        .expect("add Empty1");
    env
}

fn assert_termination_error(result: Result<Option<usize>, TypeError>, what: &str) {
    match result {
        Err(TypeError::TerminationError { .. }) => {}
        other => panic!("expected a TerminationError for {}, got {:?}", what, other),
    }
}

#[test]
fn recursion_on_an_induction_hypothesis_is_not_structural() {
    let env = env_with_w();
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    let app = |f: Rc<Term>, a: Rc<Term>| Term::app(f, a);
    let bf = Rc::new(Term::Ctor("B".to_string(), 1, vec![]));
    let base = Rc::new(Term::Ctor("W".to_string(), 0, vec![]));
    let step = Rc::new(Term::Ctor("W".to_string(), 1, vec![]));
    // f : (b : B) -> (w : W b) -> Empty1
    //   := fun b w => Rec W [1] (fun _ _ => Empty1) (step base) (fun l ih => f bf ih) b w
    let f_ty = pi(ind("B"), pi(app(ind("W"), var(0)), ind("Empty1")));
    let motive = Term::lam(
        ind("B"),
        Term::lam(app(ind("W"), var(0)), ind("Empty1"), BinderInfo::Default),
        BinderInfo::Default,
    );
    let rec_w = Rc::new(Term::Rec("W".to_string(), vec![level1()]));
    let step_minor = lam1(
        app(ind("W"), Rc::new(Term::Ctor("B".to_string(), 0, vec![]))),
        lam1(
            ind("Empty1"),
            Term::app(
                Term::app(Rc::new(Term::Const("f".to_string(), vec![])), bf.clone()),
                var(0),
            ),
        ),
    );
    let f_body = Term::lam(
        ind("B"),
        Term::lam(
            app(ind("W"), var(0)),
            {
                let mut t = rec_w;
                t = Term::app(t, motive);
                t = Term::app(t, Term::app(step, base));
                t = Term::app(t, step_minor);
                t = Term::app(t, var(1)); // b
                Term::app(t, var(0)) // w
            },
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    assert_termination_error(
        check_termination(&env, "f", &f_ty, &f_body),
        "recursion on the IH",
    );
}

#[test]
fn recursor_whose_major_is_not_the_decreasing_argument_does_not_make_fields_smaller() {
    // q : N -> N := fun n => Rec N (fun _ => N) zero (fun m ih => q m) (succ n)
    // The recursor's major is `succ n`, not `n`, so the field `m` is not smaller than `n`.
    let env = base_env();
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    let succ = Rc::new(Term::Ctor("N".to_string(), 1, vec![]));
    let rec_n = Rc::new(Term::Rec("N".to_string(), vec![level1()]));
    let motive = Term::lam(ind("N"), ind("N"), BinderInfo::Default);
    let step_minor = lam1(
        ind("N"),
        lam1(
            ind("N"),
            Term::app(Rc::new(Term::Const("q".to_string(), vec![])), var(1)),
        ),
    );
    let q_body = Term::lam(
        ind("N"),
        {
            let mut t = rec_n;
            t = Term::app(t, motive);
            t = Term::app(t, zero());
            t = Term::app(t, step_minor);
            Term::app(t, Term::app(succ, var(0)))
        },
        BinderInfo::Default,
    );
    assert_termination_error(
        check_termination(&env, "q", &pi(ind("N"), ind("N")), &q_body),
        "recursor major is succ n",
    );
}

#[test]
fn recursion_on_a_structural_field_is_still_accepted() {
    // g : N -> N := fun n => Rec N (fun _ => N) zero (fun m ih => g m) n   (decreases on the field)
    let env = base_env();
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    let rec_n = Rc::new(Term::Rec("N".to_string(), vec![level1()]));
    let motive = Term::lam(ind("N"), ind("N"), BinderInfo::Default);
    let step_minor = lam1(
        ind("N"),
        lam1(
            ind("N"),
            Term::app(Rc::new(Term::Const("g".to_string(), vec![])), var(1)),
        ),
    );
    let g_body = Term::lam(
        ind("N"),
        {
            let mut t = rec_n;
            t = Term::app(t, motive);
            t = Term::app(t, zero());
            t = Term::app(t, step_minor);
            Term::app(t, var(0))
        },
        BinderInfo::Default,
    );
    assert_eq!(
        check_termination(&env, "g", &pi(ind("N"), ind("N")), &g_body).expect("g terminates"),
        Some(0),
        "structural recursion on the recursor's field decreases on argument 0"
    );
}

#[test]
fn recursive_call_must_supply_the_decreasing_argument() {
    // f : N -> N -> N := fun a n => (fun (g : N -> N) => g n) (f a)
    // The recursive call `f a` stops before the second (decreasing) argument.
    let env = base_env();
    let pi = |a: Rc<Term>, b: Rc<Term>| Term::pi(a, b, BinderInfo::Default);
    let n_to_n = pi(ind("N"), ind("N"));
    // body under [a, n]: (fun (g : N -> N) => g n) (f a)
    let applied = Term::lam(
        n_to_n.clone(),
        Term::app(var(0), var(1)), // g n  (g = Var 0, n = Var 1 under the new binder)
        BinderInfo::Default,
    );
    let f_partial = Term::app(Rc::new(Term::Const("f".to_string(), vec![])), var(1)); // f a
    let body = Term::lam(
        ind("N"),
        Term::lam(ind("N"), Term::app(applied, f_partial), BinderInfo::Default),
        BinderInfo::Default,
    );
    match check_termination(&env, "f", &pi(ind("N"), n_to_n), &body) {
        Err(TypeError::TerminationError {
            details: TerminationErrorDetails::MissingDecreasingArgument { .. },
            ..
        }) => {}
        other => panic!(
            "a recursive call missing the decreasing argument must be rejected, got {:?}",
            other
        ),
    }
}

// =============================================================================
// K_repair round 2 (verifier-confirmed findings on conversion, definitions and fixpoints):
// * T-Fix checks the body against the annotation lifted over the recursive binder;
// * a fixpoint may not return a proof (proofs are erased, so a looping fixpoint stood for a
//   proof of anything and transport along it re-typed values at run time);
// * type checking never unfolds a fixpoint (T-App did, although conversion does not);
// * a recursive total definition is unfolded only when its decreasing argument is a
//   constructor (a stuck call such as `add n zero` had an infinite normal form: stack overflow);
// * the normalisation budget counts every step (β, ζ and the binders opened by read-back, not
//   only δ/ι/fix), is shared by evaluation and read-back, and the nesting depth is limited;
// * redefinition (allow_redefinition) of a name that other entries refer to is refused;
// * a `Derived` Copy instance submitted through the API is re-derived by the kernel;
// * only an axiom may lack a value, and an axiom always depends on itself.
// =============================================================================

fn konst(name: &str) -> Rc<Term> {
    Rc::new(Term::Const(name.to_string(), vec![]))
}

fn succ_n(t: Rc<Term>) -> Rc<Term> {
    Term::app(Rc::new(Term::Ctor("N".to_string(), 1, vec![])), t)
}

fn lam(ty: Rc<Term>, body: Rc<Term>) -> Rc<Term> {
    Term::lam(ty, body, BinderInfo::Default)
}

fn apps(f: Rc<Term>, args: Vec<Rc<Term>>) -> Rc<Term> {
    args.into_iter().fold(f, Term::app)
}

/// `base_env` plus `EqP : (A : Type) -> A -> A -> Prop` (prelude shape) and `FalseP : Prop`.
fn env_with_eq() -> Env {
    let mut env = base_env();
    env.add_inductive(decl(
        "EqP",
        pi(type0(), pi(var(0), pi(var(1), prop()))),
        vec![(
            "refl",
            pi(
                type0(),
                pi(var(0), apps(ind("EqP"), vec![var(1), var(0), var(0)])),
            ),
        )],
    ))
    .expect("add EqP");
    env.add_inductive(decl("FalseP", prop(), vec![]))
        .expect("add FalseP");
    env
}

fn eq_p(a: Rc<Term>, x: Rc<Term>, y: Rc<Term>) -> Rc<Term> {
    apps(ind("EqP"), vec![a, x, y])
}

fn refl_p(a: Rc<Term>, x: Rc<Term>) -> Rc<Term> {
    apps(
        Rc::new(Term::Ctor("EqP".to_string(), 0, vec![])),
        vec![a, x],
    )
}

/// T-Fix is `Γ, f : A ⊢ t : A`: `A` is read in the extended context, i.e. lifted by one. The
/// kernel checked the body against the unlifted annotation, so every free variable of the
/// annotation was read as the next binder inward: in `[A, B, a : A, b : B]` the fixpoint
/// `fix go : Prop -> A. fun _ => b` (returning `b : B`) was accepted at type `Prop -> A` and the
/// well-typed `fix go : Prop -> A. fun _ => a` was rejected.
#[test]
fn fixpoint_body_is_checked_against_the_lifted_annotation() {
    let env = Env::new();
    // ctx = [A : Type, B : Type, a : A, b : B]  (b = Var 0, a = Var 1, B = Var 2, A = Var 3)
    let ctx = Context::new()
        .push(type0())
        .push(type0())
        .push(var(1))
        .push(var(1));
    // annotation `(_ : Prop) -> A`: A is Var 4 under the Pi binder
    let ann = Term::pi_with_kind(prop(), var(4), BinderInfo::Default, FunctionKind::FnOnce);
    // body context [A, B, a, b, go, _]: a = Var 3, b = Var 2
    let returns_a = Rc::new(Term::Fix(ann.clone(), lam1(prop(), var(3))));
    let returns_b = Rc::new(Term::Fix(ann.clone(), lam1(prop(), var(2))));
    assert_eq!(
        infer(&env, &ctx, returns_a).expect("a fixpoint returning a : A has type Prop -> A"),
        ann
    );
    match infer(&env, &ctx, returns_b) {
        Err(TypeError::TypeMismatch { .. }) => {}
        other => panic!(
            "a fixpoint returning b : B must not have type Prop -> A, got {:?}",
            other
        ),
    }
}

/// `fix go : N -> FalseP. fun m => go m` is a looping "proof" of the empty proposition. Proofs
/// are erased at run time, so the loop never runs; transport along such a proof made compiled
/// partial code use `true` as a natural number. The codomain at the end of a fixpoint's Pi
/// telescope may not be a proposition (`FixProofCodomain`, K0055).
#[test]
fn fixpoint_returning_a_proof_is_rejected() {
    let env = env_with_eq();
    let ctx = Context::new();
    let looping = |codomain: Rc<Term>| {
        Rc::new(Term::Fix(
            pi(ind("N"), codomain),
            lam(ind("N"), Term::app(var(1), var(0))),
        ))
    };
    match infer(&env, &ctx, Term::app(looping(ind("FalseP")), zero())) {
        Err(TypeError::FixProofCodomain { .. }) => {}
        other => panic!(
            "a fixpoint returning a proof must be rejected, got {:?}",
            other
        ),
    }
    let false_eq = eq_p(ind("N"), zero(), succ_n(zero()));
    match infer(&env, &ctx, looping(false_eq)) {
        Err(TypeError::FixProofCodomain { .. }) => {}
        other => panic!(
            "a fixpoint returning a proof must be rejected, got {:?}",
            other
        ),
    }
    // A fixpoint returning data is still a well-typed (partial) term.
    assert!(infer(&env, &ctx, Term::app(looping(ind("N")), zero())).is_ok());
}

/// Conversion never unfolds a fixpoint (K0049), and neither does the normalisation the type
/// checker uses to expose a Pi (T-App) or a sort: with `T := fix T : N -> Type. fun m => N`, the
/// argument `zero : N` was accepted at the domain `T zero` only because `whnf_in_ctx` unfolded
/// `T`. (The same unfolding made the checker loop until the stack overflowed when the fixpoint
/// never stops, e.g. inside a stuck recursor.)
#[test]
fn type_checking_never_unfolds_a_fixpoint() {
    let env = base_env();
    let ctx = Context::new();
    let family = Rc::new(Term::Fix(pi(ind("N"), type0()), lam(ind("N"), ind("N"))));
    match whnf_in_ctx(
        &env,
        &ctx,
        Term::app(family.clone(), zero()),
        Transparency::Reducible,
    ) {
        Err(TypeError::DefEqFixUnfold) => {}
        other => panic!("whnf must not unfold a fixpoint, got {:?}", other),
    }
    // consumer : (F : N -> Type) -> F zero -> N := fun F x => zero
    let consumer = lam(
        pi(ind("N"), type0()),
        lam(Term::app(var(0), zero()), zero()),
    );
    match infer(&env, &ctx, apps(consumer, vec![family, zero()])) {
        Err(TypeError::DefEqFixUnfold) => {}
        other => panic!(
            "zero : T zero must not type-check by unfolding the fixpoint T, got {:?}",
            other
        ),
    }
}

/// `add := fun n m => Rec N (fun _ => N) m (fun k ih => succ (add k m)) n` refers to itself
/// (kernel API; structurally recursive, `rec_arg = 0`). The normal form of the stuck call
/// `add n zero` used to be infinite: the recursor is stuck on `n`, and reading back its minor
/// premise unfolded `add` again under a fresh binder, forever, so admitting
/// `t1 : (n : N) -> EqP N (add n zero) (add n zero)` overflowed the stack. A recursive definition
/// is now unfolded only when its decreasing argument is a constructor (guarded δ).
#[test]
fn stuck_call_of_a_recursive_definition_stays_stuck() {
    let mut env = env_with_eq();
    let n = ind("N");
    let rec_n = Rc::new(Term::Rec("N".to_string(), vec![level1()]));
    // minor premise under [n, m, k, ih]: k = Var 1, m = Var 2
    let minor = lam1(
        n.clone(),
        lam1(n.clone(), succ_n(apps(konst("add"), vec![var(1), var(2)]))),
    );
    let body = lam(
        n.clone(),
        lam(
            n.clone(),
            apps(
                rec_n,
                vec![lam(n.clone(), n.clone()), var(0), minor, var(1)],
            ),
        ),
    );
    env.add_definition(Definition::total(
        "add".to_string(),
        pi(n.clone(), pi(n.clone(), n.clone())),
        body,
    ))
    .expect("add is structurally recursive");
    assert_eq!(env.get_definition("add").and_then(|d| d.rec_arg), Some(0));
    let two = succ_n(succ_n(zero()));
    assert_eq!(
        whnf(
            &env,
            apps(konst("add"), vec![two.clone(), zero()]),
            Transparency::Reducible
        )
        .expect("closed call reduces"),
        two
    );
    let call = apps(konst("add"), vec![var(0), zero()]);
    let ctx = Context::new().push(n.clone());
    assert_eq!(
        whnf_in_ctx(&env, &ctx, call.clone(), Transparency::Reducible).expect("stuck call"),
        call
    );
    env.add_definition(Definition::total(
        "t1".to_string(),
        pi(n.clone(), eq_p(n.clone(), call.clone(), call.clone())),
        lam(n.clone(), refl_p(n.clone(), call)),
    ))
    .expect("t1 is well-typed and its type has a finite normal form");
}

/// Church numerals as plain λ-terms (no constants, so no δ steps):
/// `pow m n = fun X => n (X -> X) (m X)`; `iter c = c N (fun k => k) zero` iterates the identity
/// `c` times (normal form `zero`). Before, only δ, ι and fixpoint unfolding were charged, so
/// `iter (2^(2^2))` (sixteen iterations, dozens of β steps) was decided with a budget of 1.
fn church_identity_iteration(levels: usize) -> Rc<Term> {
    let c_ty = || pi(type0(), pi(pi(var(0), var(1)), pi(var(1), var(2))));
    // two = fun X f x => f (f x)
    let two = || {
        lam(
            type0(),
            lam(
                pi(var(0), var(1)),
                lam(var(1), Term::app(var(1), Term::app(var(1), var(0)))),
            ),
        )
    };
    // pow = fun m n X => n (X -> X) (m X)
    let pow = || {
        lam(
            c_ty(),
            lam(
                c_ty(),
                lam(
                    type0(),
                    apps(var(1), vec![pi(var(0), var(1)), Term::app(var(2), var(0))]),
                ),
            ),
        )
    };
    let mut num = two();
    for _ in 0..levels {
        num = apps(pow(), vec![two(), num]);
    }
    apps(num, vec![ind("N"), lam(ind("N"), var(0)), zero()])
}

#[test]
fn normalisation_budget_counts_beta_and_zeta_steps() {
    let env = base_env();
    let iterations = church_identity_iteration(2); // 2^(2^2) = 16
    assert_eq!(
        kernel::nbe::is_def_eq_result(
            iterations.clone(),
            zero(),
            &env,
            Transparency::Reducible,
            100_000
        ),
        Ok(true)
    );
    match kernel::nbe::is_def_eq_result(iterations, zero(), &env, Transparency::Reducible, 10) {
        Err(kernel::nbe::NbeError::FuelExhausted(_)) => {}
        other => panic!("10 steps cannot decide 16 iterations, got {:?}", other),
    }
    // 40 nested lets: each is a ζ step.
    let mut lets = zero();
    for _ in 0..40 {
        lets = Rc::new(Term::LetE(ind("N"), zero(), lets));
    }
    match kernel::nbe::is_def_eq_result(lets.clone(), zero(), &env, Transparency::Reducible, 10) {
        Err(kernel::nbe::NbeError::FuelExhausted(_)) => {}
        other => panic!("10 steps cannot evaluate 40 lets, got {:?}", other),
    }
    assert_eq!(
        kernel::nbe::is_def_eq_result(lets, zero(), &env, Transparency::Reducible, 1_000),
        Ok(true)
    );
}

/// Read-back (quote) re-enters every closure under its binder. It used to restart the budget at
/// each binder; now one budget covers the whole read-back and each opened binder is charged.
#[test]
fn read_back_shares_one_budget() {
    let env = base_env();
    let mut nested = zero();
    for _ in 0..40 {
        nested = lam(ind("N"), nested);
    }
    let value = kernel::nbe::eval(&nested, &vec![], &env, Transparency::Reducible)
        .expect("a lambda evaluates to a closure");
    match kernel::nbe::quote_with_fuel(value.clone(), 0, &env, Transparency::Reducible, 10) {
        Err(kernel::nbe::NbeError::FuelExhausted(_)) => {}
        other => panic!(
            "reading back 40 binders costs more than 10 steps, got {:?}",
            other
        ),
    }
    assert_eq!(
        kernel::nbe::quote_with_fuel(value, 0, &env, Transparency::Reducible, 1_000)
            .expect("enough fuel"),
        nested
    );
}

/// The budget bounds the work; the depth limit bounds the recursion, so a deep (but affordable)
/// normalisation reports `NormalizationDepthExceeded` (K0056) instead of overflowing the stack.
/// Runs on a 1 GiB stack, like the CLI (`COMPILER_STACK_SIZE`).
#[test]
fn normalisation_depth_is_limited() {
    let handle = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            let env = base_env();
            let mut numeral = zero();
            for _ in 0..(kernel::nbe::MAX_EVAL_DEPTH + 10) {
                numeral = succ_n(numeral);
            }
            // (Rc terms are not Send: report the outcome as data.)
            match whnf_in_ctx(&env, &Context::new(), numeral, Transparency::Reducible) {
                Err(TypeError::NormalizationDepthExceeded { limit }) => Ok(limit),
                Err(other) => Err(format!("{:?}", other)),
                Ok(_) => Err("normalised without reaching the depth limit".to_string()),
            }
        })
        .expect("spawn");
    match handle.join().expect("no stack overflow") {
        Ok(limit) => assert_eq!(limit, kernel::nbe::MAX_EVAL_DEPTH),
        Err(other) => panic!("expected NormalizationDepthExceeded, got {}", other),
    }
}

/// Under `allow_redefinition` (CLI `--allow-redefine`) a redefinition replaced the entry and kept
/// everything checked against the old meaning: with `c := zero`, `p : EqP N zero c` proved
/// `EqP N zero (succ zero)` after `c := succ zero` (δ uses the current body), and a value of an
/// inductive redeclared empty inhabited the empty type — closed proofs of `False`, no axiom.
/// A name that other entries refer to can no longer be redefined (K0054).
#[test]
fn redefining_a_referenced_name_is_rejected() {
    let mut env = env_with_eq();
    env.set_allow_redefinition(true);
    let n = ind("N");
    env.add_definition(Definition::total("c".to_string(), n.clone(), zero()))
        .expect("c");
    env.add_definition(Definition::total(
        "p".to_string(),
        eq_p(n.clone(), zero(), konst("c")),
        refl_p(n.clone(), zero()),
    ))
    .expect("p");
    match env.add_definition(Definition::total(
        "c".to_string(),
        n.clone(),
        succ_n(zero()),
    )) {
        Err(TypeError::RedefinitionWithDependents { name, dependents }) => {
            assert_eq!(name, "c");
            assert_eq!(dependents, vec!["p".to_string()]);
        }
        other => panic!("redefining c under p must be rejected, got {:?}", other),
    }
    assert_eq!(
        env.get_definition("c").and_then(|d| d.value.clone()),
        Some(zero()),
        "the rejected redefinition leaves c unchanged"
    );
    // A name nothing refers to may still be redefined.
    env.add_definition(Definition::total("d".to_string(), n.clone(), zero()))
        .expect("d");
    env.add_definition(Definition::total(
        "d".to_string(),
        n.clone(),
        succ_n(zero()),
    ))
    .expect("redefining an unreferenced name is allowed");
    // Inductives: B with one constructor, x : B := mk, then B redeclared empty.
    env.add_inductive(decl("B1", type0(), vec![("mk", ind("B1"))]))
        .expect("B1");
    env.add_definition(Definition::total(
        "x".to_string(),
        ind("B1"),
        Rc::new(Term::Ctor("B1".to_string(), 0, vec![])),
    ))
    .expect("x");
    match env.add_inductive(decl("B1", type0(), vec![])) {
        Err(TypeError::RedefinitionWithDependents { name, dependents }) => {
            assert_eq!(name, "B1");
            assert_eq!(dependents, vec!["x".to_string()]);
        }
        other => panic!("redeclaring B1 under x must be rejected, got {:?}", other),
    }
    // The elaborator's placeholder route (used by the CLI) is guarded the same way.
    match env.insert_inductive_placeholder(decl("B1", type0(), vec![])) {
        Err(TypeError::RedefinitionWithDependents { .. }) => {}
        other => panic!(
            "placeholder over a referenced inductive must be rejected, got {:?}",
            other
        ),
    }
    assert_eq!(
        env.get_inductive("B1").map(|d| d.ctors.len()),
        Some(1),
        "B1 keeps its constructor"
    );
}

/// `Env::add_copy_instance` registered a `Derived` instance unchecked (only `Explicit` ones were
/// validated), so an API client could make a closure-carrying type Copy with no axiom recorded.
/// A submitted `Derived` instance must be exactly the kernel's own derivation.
#[test]
fn derived_copy_instance_from_the_api_is_rederived() {
    let mut env = base_env();
    // Res : Type with mk : (N -> N) -> Res (a function field: not Copy)
    env.add_inductive(decl(
        "Res",
        type0(),
        vec![("mk", pi(pi(ind("N"), ind("N")), ind("Res")))],
    ))
    .expect("Res");
    let forged = kernel::ast::CopyInstance {
        ind_name: "Res".to_string(),
        param_count: 0,
        requirements: vec![],
        source: kernel::ast::CopyInstanceSource::Derived,
        is_unsafe: false,
    };
    match env.add_copy_instance(forged.clone()) {
        Err(TypeError::CopyDeriveFailure { ind, .. }) => assert_eq!(ind, "Res"),
        other => panic!(
            "a forged derived instance must be rejected, got {:?}",
            other
        ),
    }
    assert!(!env.copy_instances().contains_key("Res"));
    let unknown = kernel::ast::CopyInstance {
        ind_name: "Nope".to_string(),
        ..forged
    };
    match env.add_copy_instance(unknown) {
        Err(TypeError::UnknownInductive(name)) => assert_eq!(name, "Nope"),
        other => panic!(
            "an instance for an unknown type must be rejected, got {:?}",
            other
        ),
    }
    // Resubmitting the kernel's own derivation for N is accepted.
    let derived_n = env
        .copy_instances()
        .get("N")
        .and_then(|v| v.first())
        .cloned();
    let derived_n = derived_n.expect("N derives Copy");
    env.add_copy_instance(derived_n)
        .expect("the kernel's own derived instance is accepted");
}

/// Only an axiom may come without a value (a Total definition without one was an unchecked,
/// untracked postulate), and an axiom's dependency on itself is recorded by the kernel, not taken
/// from the client's `axioms` list (clearing it gave an axiom-free inhabitant of `FalseP`).
#[test]
fn only_axioms_lack_values_and_axioms_depend_on_themselves() {
    let mut env = env_with_eq();
    let mut no_value = Definition::total("t_noval".to_string(), ind("FalseP"), zero());
    no_value.value = None;
    match env.add_definition(no_value) {
        Err(TypeError::MissingDefinitionValue { name, .. }) => assert_eq!(name, "t_noval"),
        other => panic!(
            "a Total definition without a value must be rejected, got {:?}",
            other
        ),
    }
    let mut cleared = Definition::axiom("ax_cleared".to_string(), ind("FalseP"));
    cleared.axioms.clear();
    env.add_definition(cleared).expect("an axiom is admitted");
    assert_eq!(
        env.get_definition("ax_cleared").map(|d| d.axioms.clone()),
        Some(vec!["ax_cleared".to_string()])
    );
    match env.add_definition(Definition::total(
        "use_b".to_string(),
        ind("FalseP"),
        konst("ax_cleared"),
    )) {
        Err(TypeError::AxiomDependencyRequiresNoncomputable { axioms, .. }) => {
            assert_eq!(axioms, vec!["ax_cleared".to_string()])
        }
        other => panic!(
            "a use of the axiom must be tracked (K0023), got {:?}",
            other
        ),
    }
}

/// The CLI prints the value of a top-level expression with `normalize_for_display`. Display may
/// unfold fixpoints and has no step budget, but its nesting depth is limited: a looping term (here
/// the self-application `(λx. x x) (λx. x x)`) stops with `DepthLimitExceeded` instead of
/// overflowing the stack, while an ordinary closed value still normalises.
#[test]
fn display_normalisation_is_depth_limited() {
    let handle = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            let env = base_env();
            let self_app = lam(ind("N"), Term::app(Rc::new(Term::Var(0)), Rc::new(Term::Var(0))));
            let omega = Term::app(self_app.clone(), self_app);
            let looping = match kernel::nbe::normalize_for_display(&omega, &env, Transparency::All) {
                Err(kernel::nbe::NbeError::DepthLimitExceeded { limit }) => Ok(limit),
                Err(other) => Err(format!("{:?}", other)),
                Ok(_) => Err("the looping term normalised".to_string()),
            };
            let two = succ_n(succ_n(zero()));
            let value = Term::app(lam(ind("N"), Rc::new(Term::Var(0))), two.clone());
            let ordinary = match kernel::nbe::normalize_for_display(&value, &env, Transparency::All) {
                Ok(t) => t == two,
                Err(_) => false,
            };
            (looping, ordinary)
        })
        .expect("spawn");
    let (looping, ordinary) = handle.join().expect("no stack overflow");
    match looping {
        Ok(limit) => assert_eq!(limit, kernel::nbe::MAX_EVAL_DEPTH),
        Err(other) => panic!("expected DepthLimitExceeded, got {}", other),
    }
    assert!(ordinary, "a closed value should normalise for display");
}
