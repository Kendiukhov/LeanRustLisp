use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use frontend::declaration_parser::DeclarationParser;
use frontend::surface::Declaration;
use frontend::elaborator::{Elaborator, ElabError};
use kernel::ast::{Term, Level, InductiveDecl, Constructor, BinderInfo, Transparency};
use kernel::checker::{Env, whnf};
use std::rc::Rc;

fn parse_single_def(source: &str) -> (String, frontend::surface::SurfaceTerm, frontend::surface::SurfaceTerm) {
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
    let nat_ty = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let nat_ind = Rc::new(Term::Ind("Nat".to_string(), vec![]));

    let ctors = vec![
        Constructor {
            name: "zero".to_string(),
            ty: nat_ind.clone(),
        },
        Constructor {
            name: "succ".to_string(),
            ty: Rc::new(Term::Pi(nat_ind.clone(), nat_ind.clone(), BinderInfo::Default)),
        },
    ];

    env.inductives.insert(
        "Nat".to_string(),
        InductiveDecl::new_copy("Nat".to_string(), nat_ty, ctors),
    );
    env
}

fn env_with_bool() -> Env {
    let mut env = env_with_nat();
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

    env.inductives.insert(
        "Bool".to_string(),
        InductiveDecl::new_copy("Bool".to_string(), bool_ty, ctors),
    );
    env
}

fn env_with_eq() -> Env {
    let mut env = env_with_nat();

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

    env.inductives.insert(
        "Eq".to_string(),
        InductiveDecl::new_copy(
            "Eq".to_string(),
            eq_ty,
            vec![Constructor {
                name: "refl".to_string(),
                ty: refl_ty,
            }],
        ),
    );

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
    assert!(matches!(&*ty_ty_whnf, Term::Sort(_)), "Definition type must be a Sort");

    let err = elab.check(val, &ty_core).expect_err("Case bodies should be checked against the motive");
    assert!(matches!(err, ElabError::UnificationError(_, _) | ElabError::TypeMismatch { .. }));
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
    assert!(matches!(&*ty_ty_whnf, Term::Sort(_)), "Definition type must be a Sort");

    elab
        .check(val, &ty_core)
        .expect("Eq elimination into Type should be accepted");
}
