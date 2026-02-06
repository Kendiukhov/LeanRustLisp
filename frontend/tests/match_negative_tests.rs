use frontend::declaration_parser::DeclarationParser;
use frontend::elaborator::{ElabError, Elaborator};
use frontend::macro_expander::Expander;
use frontend::parser::Parser;
use frontend::surface::Declaration;
use kernel::ast::{
    BinderInfo, Constructor, FunctionKind, InductiveDecl, Level, Term, Transparency,
};
use kernel::checker::{whnf, Env};
use std::rc::Rc;

fn parse_single_def(
    source: &str,
) -> (
    String,
    frontend::surface::SurfaceTerm,
    frontend::surface::SurfaceTerm,
) {
    let mut parser = Parser::new(source);
    let syntax_nodes = parser.parse().expect("Parse should succeed");

    let mut expander = Expander::new();
    let mut decl_parser = DeclarationParser::new(&mut expander);
    let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

    for decl in decls {
        if let Declaration::Def { name, ty, val, .. } = decl {
            return (name, ty, val);
        }
    }

    panic!("Expected a single def declaration");
}

fn env_with_nat() -> Env {
    let mut env = Env::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
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
    env.set_allow_reserved_primitives(allow_reserved);
    env
}

fn env_with_bool() -> Env {
    let mut env = env_with_nat();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    let bool_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let bool_ind = Rc::new(Term::Ind("Bool".to_string(), vec![]));

    let ctors = vec![
        Constructor {
            name: "true".to_string(),
            ty: bool_ind.clone(),
        },
        Constructor {
            name: "false".to_string(),
            ty: bool_ind.clone(),
        },
    ];

    env.add_inductive(InductiveDecl::new_copy("Bool".to_string(), bool_ty, ctors))
        .expect("Failed to add Bool");
    env.set_allow_reserved_primitives(allow_reserved);
    env
}

fn env_with_eq() -> Env {
    let mut env = env_with_nat();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);

    let type0 = Term::sort(Level::Succ(Box::new(Level::Zero)));
    let prop = Term::sort(Level::Zero);
    let eq_ind = Term::ind("Eq".to_string());

    let eq_ty = Term::pi(
        type0.clone(),
        Term::pi(
            Term::var(0),
            Term::pi(Term::var(1), prop.clone(), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let eq_app = Term::app(
        Term::app(Term::app(eq_ind, Term::var(1)), Term::var(0)),
        Term::var(0),
    );

    let refl_ty = Term::pi(
        type0,
        Term::pi(Term::var(0), eq_app, BinderInfo::Default),
        BinderInfo::Default,
    );

    env.add_inductive(InductiveDecl::new_copy(
        "Eq".to_string(),
        eq_ty,
        vec![Constructor {
            name: "refl".to_string(),
            ty: refl_ty,
        }],
    ))
    .expect("Failed to add Eq");
    env.set_allow_reserved_primitives(allow_reserved);

    env
}

#[test]
fn elaboration_match_case_type_mismatch_rejected() {
    let env = env_with_bool();
    let source = r#"
        (def bad_match (pi b Bool Nat)
          (lam b Bool
            (match b Nat
              (case (true) false)
              (case (false) true))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::Reducible).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Case bodies should be checked against the motive");
    assert!(matches!(
        err,
        ElabError::UnificationError(_, _) | ElabError::TypeMismatch { .. }
    ));
}

#[test]
fn elaboration_match_non_inductive_scrutinee_rejected() {
    let env = env_with_nat();
    let source = r#"
        (def bad_scrut (pi n Nat Nat)
          (lam n Nat
            (match Nat Nat
              (case (zero) zero)
              (case (succ m ih) zero))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::Reducible).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Match scrutinee must be an inductive");
    match err {
        ElabError::TypeMismatch { expected, .. } => {
            assert_eq!(expected, "inductive type");
        }
        other => panic!(
            "Expected TypeMismatch for inductive scrutinee, got {:?}",
            other
        ),
    }
}

#[test]
fn elaboration_match_motive_not_sort_rejected() {
    let env = env_with_nat();
    let source = r#"
        (def bad_motive (pi n Nat Nat)
          (lam n Nat
            (match n zero
              (case (zero) zero)
              (case (succ m ih) zero))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::Reducible).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Match motive must be a Sort");
    match err {
        ElabError::TypeMismatch { expected, .. } => {
            assert_eq!(expected, "Sort");
        }
        other => panic!("Expected TypeMismatch for match motive, got {:?}", other),
    }
}

#[test]
fn elaboration_match_missing_case_rejected() {
    let env = env_with_bool();
    let source = r#"
        (def bad_missing (pi b Bool Nat)
          (lam b Bool
            (match b Nat
              (case (true) zero))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::Reducible).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Match should be rejected as non-exhaustive");
    match err {
        ElabError::NonExhaustiveMatch { ind, missing, .. } => {
            assert_eq!(ind, "Bool");
            assert!(missing.contains(&"false".to_string()));
        }
        other => panic!(
            "Expected NonExhaustiveMatch for missing case, got {:?}",
            other
        ),
    }
}

#[test]
fn elaboration_match_duplicate_case_rejected() {
    let env = env_with_bool();
    let source = r#"
        (def bad_duplicate (pi b Bool Nat)
          (lam b Bool
            (match b Nat
              (case (true) zero)
              (case (true) (succ zero))
              (case (false) zero))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::Reducible).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Match should be rejected as duplicate");
    match err {
        ElabError::DuplicateMatchCase { ind, ctor, .. } => {
            assert_eq!(ind, "Bool");
            assert_eq!(ctor, "true");
        }
        other => panic!(
            "Expected DuplicateMatchCase for duplicate case, got {:?}",
            other
        ),
    }
}

#[test]
fn elaboration_match_unknown_case_rejected() {
    let env = env_with_bool();
    let source = r#"
        (def bad_unknown (pi b Bool Nat)
          (lam b Bool
            (match b Nat
              (case (maybe) zero)
              (case (true) zero)
              (case (false) zero))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::Reducible).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Match should be rejected for unknown constructor");
    match err {
        ElabError::UnknownMatchCase { ind, ctor, .. } => {
            assert_eq!(ind, "Bool");
            assert_eq!(ctor, "maybe");
        }
        other => panic!(
            "Expected UnknownMatchCase for unknown case, got {:?}",
            other
        ),
    }
}

#[test]
fn elaboration_prop_to_type_elim_eq_allowed() {
    let env = env_with_eq();
    let source = r#"
        (def proof_to_nat
          (pi A Type
            (pi a A
              (pi b A
                (pi p (Eq A a b) Nat))))
          (lam A Type
            (lam a A
              (lam b A
                (lam p (Eq A a b)
                  (match p Nat
                    (case (refl A' a') (succ zero))))))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::Reducible).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    elab.check(val, &ty_core)
        .expect("Eq elimination into Type should be accepted");
}
