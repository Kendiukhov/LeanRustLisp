use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use frontend::declaration_parser::DeclarationParser;
use frontend::surface::{Declaration, SurfaceTerm};
use frontend::elaborator::{Elaborator, ElabError};
use kernel::ast::{Term, Level, InductiveDecl, Constructor, BinderInfo, Transparency, Totality};
use kernel::checker::{Env, whnf, TypeError};
use insta::assert_snapshot;
use std::rc::Rc;

fn parse_single_def(source: &str) -> (String, SurfaceTerm, SurfaceTerm) {
    let mut parser = Parser::new(source);
    let syntax_nodes = parser.parse().expect("Parse should succeed");

    let mut expander = Expander::new();
    let mut decl_parser = DeclarationParser::new(&mut expander);
    let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

    for decl in decls {
        if let Declaration::Def { name, ty, val, totality, transparency } = decl {
            assert_eq!(totality, Totality::Total, "Expected total definition");
            assert_eq!(transparency, Transparency::Reducible, "Expected transparent definition");
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

    env.add_inductive(InductiveDecl::new_copy("Nat".to_string(), nat_ty, ctors))
        .expect("Failed to add Nat");
    env
}

fn env_with_prop_wrap() -> Env {
    let mut env = env_with_nat();

    let prop = Rc::new(Term::Sort(Level::Zero));
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let pwrap = Rc::new(Term::Ind("PWrap".to_string(), vec![]));

    let ctor = Constructor {
        name: "mk".to_string(),
        ty: Rc::new(Term::Pi(type0, pwrap.clone(), BinderInfo::Default)),
    };

    let decl = InductiveDecl {
        name: "PWrap".to_string(),
        univ_params: vec![],
        num_params: 0,
        ty: prop,
        ctors: vec![ctor],
        is_copy: true,
    };

    env.add_inductive(decl).expect("Failed to add PWrap");
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

    env.add_inductive(InductiveDecl::new_copy(
        "Eq".to_string(),
        eq_ty,
        vec![Constructor {
            name: "refl".to_string(),
            ty: refl_ty,
        }],
    ))
    .expect("Failed to add Eq");

    env
}

fn elaborate_def(env: &Env, source: &str) -> (String, Rc<Term>, Rc<Term>) {
    let (name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(matches!(&*ty_ty_whnf, Term::Sort(_)), "Definition type must be a Sort");

    let val_core = elab.check(val, &ty_core).expect("Value should elaborate");
    elab.solve_constraints().expect("Constraints should solve");

    let ty_core = elab.instantiate_metas(&ty_core);
    let val_core = elab.instantiate_metas(&val_core);

    (name, ty_core, val_core)
}

fn format_def_output(name: &str, ty: &Rc<Term>, val: &Rc<Term>) -> String {
    format!("ElaboratedDef {}\n  ty: {:?}\n  val: {:?}\n", name, ty, val)
}

fn contains_rec(term: &Rc<Term>) -> bool {
    match &**term {
        Term::Rec(_, _) => true,
        Term::App(f, a) => contains_rec(f) || contains_rec(a),
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => contains_rec(ty) || contains_rec(body),
        Term::LetE(ty, val, body) => contains_rec(ty) || contains_rec(val) || contains_rec(body),
        Term::Fix(ty, body) => contains_rec(ty) || contains_rec(body),
        Term::Var(_)
        | Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Meta(_) => false,
    }
}

fn contains_meta(term: &Rc<Term>) -> bool {
    match &**term {
        Term::Meta(_) => true,
        Term::App(f, a) => contains_meta(f) || contains_meta(a),
        Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => contains_meta(ty) || contains_meta(body),
        Term::LetE(ty, val, body) => contains_meta(ty) || contains_meta(val) || contains_meta(body),
        Term::Fix(ty, body) => contains_meta(ty) || contains_meta(body),
        Term::Var(_)
        | Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Rec(_, _) => false,
    }
}

#[test]
fn elaboration_snapshot_identity() {
    let env = Env::new();
    let source = r#"
        (def id (pi A Type (pi x A A))
          (lam A Type (lam x A x)))
    "#;

    let (name, ty, val) = elaborate_def(&env, source);
    let output = format_def_output(&name, &ty, &val);

    assert_snapshot!(output);
}

#[test]
fn elaboration_match_desugaring_snapshot() {
    let env = env_with_nat();
    let source = r#"
        (def match_nat (pi n Nat Nat)
          (lam n Nat
            (match n Nat
              (case (zero) zero)
              (case (succ k) (succ k)))))
    "#;

    let (name, ty, val) = elaborate_def(&env, source);
    assert!(contains_rec(&val), "Match should elaborate to a recursor application");

    let output = format_def_output(&name, &ty, &val);
    assert_snapshot!(output);
}

#[test]
fn elaboration_determinism() {
    let env = env_with_nat();
    let source = r#"
        (def add_one (pi n Nat Nat)
          (lam n Nat (succ n)))
    "#;

    let (name1, ty1, val1) = elaborate_def(&env, source);
    let (name2, ty2, val2) = elaborate_def(&env, source);

    assert_eq!(name1, name2);
    assert_eq!(format!("{:?}", ty1), format!("{:?}", ty2));
    assert_eq!(format!("{:?}", val1), format!("{:?}", val2));
}

#[test]
fn elaboration_infers_implicit_args() {
    let env = env_with_nat();
    let input = "((lam {A} Type (lam x A x)) zero)";

    let mut parser = Parser::new(input);
    let syntax_list = parser.parse().expect("Parse should succeed");

    let mut expander = Expander::new();
    let term = expander
        .expand(syntax_list[0].clone())
        .expect("Expansion should succeed")
        .expect("Expected a term");

    let mut elab = Elaborator::new(&env);
    let (core, ty) = elab.infer(term).expect("Elaboration should succeed");
    elab.solve_constraints().expect("Constraints should solve");

    let core = elab.instantiate_metas(&core);
    let ty = elab.instantiate_metas(&ty);

    assert!(!contains_meta(&core), "Implicit args should be solved in term");
    assert!(!contains_meta(&ty), "Implicit args should be solved in type");
}

#[test]
fn elaboration_prop_elim_rejected() {
    let env = env_with_prop_wrap();
    let source = r#"
        (def bad (pi p PWrap Nat)
          (lam p PWrap
            (match p Nat
              (case (mk n) n))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(matches!(&*ty_ty_whnf, Term::Sort(_)), "Definition type must be a Sort");

    let err = elab.check(val, &ty_core).expect_err("Prop elimination into Type should be rejected");
    match err {
        ElabError::InferenceError(TypeError::LargeElimination(name), _) => {
            assert_eq!(name, "PWrap");
        }
        other => panic!("Expected LargeElimination error, got {:?}", other),
    }
}

#[test]
fn elaboration_prop_elim_eq_allowed() {
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
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(matches!(&*ty_ty_whnf, Term::Sort(_)), "Definition type must be a Sort");

    elab
        .check(val, &ty_core)
        .expect("Eq elimination into Type should be accepted");
}

#[test]
fn elaboration_match_missing_case_rejected() {
    let env = env_with_nat();
    let source = r#"
        (def bad_match (pi n Nat Nat)
          (lam n Nat
            (match n Nat
              (case (zero) zero))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(matches!(&*ty_ty_whnf, Term::Sort(_)), "Definition type must be a Sort");

    let err = elab.check(val, &ty_core).expect_err("Missing match cases should be rejected");
    match err {
        ElabError::NonExhaustiveMatch { ind, missing, .. } => {
            assert_eq!(ind, "Nat");
            assert!(missing.iter().any(|c| c == "succ"));
        }
        other => panic!("Expected NonExhaustiveMatch error, got {:?}", other),
    }
}

#[test]
fn elaboration_match_duplicate_case_rejected() {
    let env = env_with_nat();
    let source = r#"
        (def dup_case (pi n Nat Nat)
          (lam n Nat
            (match n Nat
              (case (zero) zero)
              (case (zero) zero))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(matches!(&*ty_ty_whnf, Term::Sort(_)), "Definition type must be a Sort");

    let err = elab.check(val, &ty_core).expect_err("Duplicate match cases should be rejected");
    match err {
        ElabError::DuplicateMatchCase { ind, ctor, .. } => {
            assert_eq!(ind, "Nat");
            assert_eq!(ctor, "zero");
        }
        other => panic!("Expected DuplicateMatchCase error, got {:?}", other),
    }
}
