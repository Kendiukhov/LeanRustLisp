use frontend::declaration_parser::DeclarationParser;
use frontend::desugar::Desugarer;
use frontend::elaborator::{ElabError, Elaborator};
use frontend::macro_expander::Expander;
use frontend::parser::Parser;
use frontend::surface::{Declaration, SurfaceTerm};
use insta::assert_snapshot;
use kernel::ast::{
    BinderInfo, Constructor, Definition, FunctionKind, InductiveDecl, Level, Term, Totality,
    Transparency,
};
use kernel::checker::{whnf, Env, TypeError};
use std::rc::Rc;

fn parse_single_def(source: &str) -> (String, SurfaceTerm, SurfaceTerm) {
    let mut parser = Parser::new(source);
    let syntax_nodes = parser.parse().expect("Parse should succeed");

    let mut expander = Expander::new();
    let mut decl_parser = DeclarationParser::new(&mut expander);
    let decls = decl_parser.parse(syntax_nodes).expect("Parse decls");

    for decl in decls {
        if let Declaration::Def {
            name,
            ty,
            val,
            totality,
            transparency,
            noncomputable,
        } = decl
        {
            assert_eq!(totality, Totality::Total, "Expected total definition");
            assert_eq!(
                transparency,
                Transparency::Reducible,
                "Expected transparent definition"
            );
            assert!(!noncomputable, "Expected computable definition");
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

fn env_with_box() -> Env {
    let mut env = env_with_nat();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
    let box_ty = Rc::new(Term::Pi(
        type0.clone(),
        type0,
        BinderInfo::Default,
        FunctionKind::Fn,
    ));

    env.add_definition(Definition::axiom("Box".to_string(), box_ty))
        .expect("Failed to add Box");
    env
}

fn env_with_mut_ref() -> Env {
    let mut env = env_with_nat();
    env.set_allow_reserved_primitives(true);
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));
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

    env.add_definition(Definition::axiom("Mut".to_string(), type0.clone()))
        .expect("Failed to add Mut");
    env.add_definition(Definition::axiom("Ref".to_string(), ref_ty))
        .expect("Failed to add Ref");
    env
}

fn env_with_univ_param_unit() -> Env {
    let mut env = Env::new();
    let level_u = Level::Param("u".to_string());
    let unit_ty = Rc::new(Term::Sort(level_u));
    let unit_ind = Rc::new(Term::Ind("PUnit".to_string(), vec![]));

    let ctor = Constructor {
        name: "mk".to_string(),
        ty: unit_ind.clone(),
    };

    let decl = InductiveDecl {
        name: "PUnit".to_string(),
        univ_params: vec!["u".to_string()],
        num_params: 0,
        ty: unit_ty,
        ctors: vec![ctor],
        is_copy: true,
        markers: vec![],
        axioms: vec![],
        primitive_deps: vec![],
    };

    env.add_inductive(decl).expect("Failed to add PUnit");
    env
}

fn env_with_prop_wrap() -> Env {
    let mut env = env_with_nat();

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
    env
}

fn env_with_ambiguous_ctor() -> Env {
    let mut env = Env::new();
    let type0 = Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero))));

    let foo_ind = Rc::new(Term::Ind("Foo".to_string(), vec![]));
    env.add_inductive(InductiveDecl::new_copy(
        "Foo".to_string(),
        type0.clone(),
        vec![Constructor {
            name: "mk".to_string(),
            ty: foo_ind.clone(),
        }],
    ))
    .expect("Failed to add Foo");

    let bar_ind = Rc::new(Term::Ind("Bar".to_string(), vec![]));
    env.add_inductive(InductiveDecl::new_copy(
        "Bar".to_string(),
        type0,
        vec![Constructor {
            name: "mk".to_string(),
            ty: bar_ind.clone(),
        }],
    ))
    .expect("Failed to add Bar");

    env
}

fn env_with_qualified_defs() -> Env {
    let mut env = env_with_nat();
    let nat = Rc::new(Term::Ind("Nat".to_string(), vec![]));

    env.add_definition(Definition::axiom("Alpha.id".to_string(), nat.clone()))
        .expect("Failed to add Alpha.id");
    env.add_definition(Definition::axiom("Beta.id".to_string(), nat))
        .expect("Failed to add Beta.id");

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

fn elaborate_def(env: &Env, source: &str) -> (String, Rc<Term>, Rc<Term>) {
    let (name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

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
        Term::App(f, a, _) => contains_rec(f) || contains_rec(a),
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            contains_rec(ty) || contains_rec(body)
        }
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

fn rec_level_count(term: &Rc<Term>) -> Option<usize> {
    match &**term {
        Term::Rec(_, levels) => Some(levels.len()),
        Term::App(f, a, _) => rec_level_count(f).or_else(|| rec_level_count(a)),
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            rec_level_count(ty).or_else(|| rec_level_count(body))
        }
        Term::LetE(ty, val, body) => rec_level_count(ty)
            .or_else(|| rec_level_count(val))
            .or_else(|| rec_level_count(body)),
        Term::Fix(ty, body) => rec_level_count(ty).or_else(|| rec_level_count(body)),
        Term::Var(_)
        | Term::Sort(_)
        | Term::Const(_, _)
        | Term::Ind(_, _)
        | Term::Ctor(_, _, _)
        | Term::Meta(_) => None,
    }
}

fn contains_meta(term: &Rc<Term>) -> bool {
    match &**term {
        Term::Meta(_) => true,
        Term::App(f, a, _) => contains_meta(f) || contains_meta(a),
        Term::Lam(ty, body, _, _) | Term::Pi(ty, body, _, _) => {
            contains_meta(ty) || contains_meta(body)
        }
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
    assert!(
        contains_rec(&val),
        "Match should elaborate to a recursor application"
    );

    let output = format_def_output(&name, &ty, &val);
    assert_snapshot!(output);
}

#[test]
fn elaboration_snapshot_fnonce_inference() {
    let env = env_with_box();
    let source = r#"
        (def make_once
          (pi b (Box Nat) (pi #[once] _ Nat (Box Nat)))
          (lam b (Box Nat)
            (lam _ Nat b)))
    "#;

    let (name, ty, val) = elaborate_def(&env, source);
    let output = format_def_output(&name, &ty, &val);
    assert_snapshot!(output);
}

#[test]
fn elaboration_snapshot_fn_to_fnonce_coercion() {
    let env = env_with_nat();
    let source = r#"
        (def coerce_once
          (pi #[once] x Nat Nat)
          (lam x Nat x))
    "#;

    let (name, ty, val) = elaborate_def(&env, source);
    let output = format_def_output(&name, &ty, &val);
    assert_snapshot!(output);
}

#[test]
fn elaboration_snapshot_fn_to_fnmut_coercion() {
    let env = env_with_nat();
    let source = r#"
        (def coerce_mut
          (pi #[mut] x Nat Nat)
          (lam x Nat x))
    "#;

    let (name, ty, val) = elaborate_def(&env, source);
    let output = format_def_output(&name, &ty, &val);
    assert_snapshot!(output);
}

#[test]
fn elaboration_snapshot_fnmut_to_fnonce_coercion() {
    let env = env_with_nat();
    let source = r#"
        (def coerce_once_from_mut
          (pi #[once] x Nat Nat)
          (lam #[mut] x Nat x))
    "#;

    let (name, ty, val) = elaborate_def(&env, source);
    let output = format_def_output(&name, &ty, &val);
    assert_snapshot!(output);
}

#[test]
fn elaboration_snapshot_fn_readonly_capture() {
    let env = env_with_nat();
    let source = r#"
        (def make_const
          (pi x Nat (pi y Nat Nat))
          (lam x Nat
            (lam y Nat x)))
    "#;

    let (name, ty, val) = elaborate_def(&env, source);
    let output = format_def_output(&name, &ty, &val);
    assert_snapshot!(output);
}

#[test]
fn elaboration_snapshot_mutable_capture_fnmut() {
    let env = env_with_mut_ref();
    let source = r#"
        (def make_mut
          (pi r (Ref #[r] Mut Nat) (pi #[mut] _ Nat (Ref #[r] Mut Nat)))
          (lam r (Ref #[r] Mut Nat)
            (lam _ Nat r)))
    "#;

    let (name, ty, val) = elaborate_def(&env, source);
    let output = format_def_output(&name, &ty, &val);
    assert_snapshot!(output);
}

#[test]
fn elaboration_match_universe_params_levels() {
    let env = env_with_univ_param_unit();
    let source = r#"
        (def match_punit (pi x PUnit PUnit)
          (lam x PUnit
            (match x PUnit
              (case (mk) x))))
    "#;

    let (_name, _ty, val) = elaborate_def(&env, source);
    assert!(
        contains_rec(&val),
        "Match should elaborate to a recursor application"
    );
    let level_count = rec_level_count(&val).expect("Expected recursor levels");
    assert_eq!(
        level_count, 2,
        "Recursor should include universe params and motive level"
    );
}

#[test]
fn elaboration_rec_explicit_universe_params_levels() {
    let env = env_with_univ_param_unit();
    let source = r#"
        (def rec_punit (pi x PUnit PUnit)
          (lam x PUnit
            ((rec PUnit)
              (lam p PUnit PUnit)
              x
              x)))
    "#;

    let (_name, _ty, val) = elaborate_def(&env, source);
    assert!(
        contains_rec(&val),
        "Explicit recursor application should include a recursor term"
    );
    let level_count = rec_level_count(&val).expect("Expected recursor levels");
    assert_eq!(
        level_count, 2,
        "Recursor should include universe params and motive level"
    );
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
    let mut desugarer = Desugarer::new();
    let expanded = expander
        .expand(syntax_list[0].clone())
        .expect("Expansion should succeed")
        .expect("Expected expanded syntax");
    let term = desugarer.desugar(expanded).expect("Desugar should succeed");

    let mut elab = Elaborator::new(&env);
    let (core, ty) = elab.infer(term).expect("Elaboration should succeed");
    elab.solve_constraints().expect("Constraints should solve");

    let core = elab.instantiate_metas(&core);
    let ty = elab.instantiate_metas(&ty);

    assert!(
        !contains_meta(&core),
        "Implicit args should be solved in term"
    );
    assert!(
        !contains_meta(&ty),
        "Implicit args should be solved in type"
    );
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
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Prop elimination into Type should be rejected");
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
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    elab.check(val, &ty_core)
        .expect("Eq elimination into Type should be accepted");
}

#[test]
fn elaboration_implicit_noncopy_use_rejected() {
    let env = env_with_box();
    let source = r#"
        (def implicit_move
          (pi {b (Box Nat)} (Box Nat))
          (lam {b} (Box Nat) b))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Implicit non-Copy binder use should be rejected");
    match err {
        ElabError::ImplicitNonCopyUse { .. } => {}
        other => panic!("Expected ImplicitNonCopyUse error, got {:?}", other),
    }
}

#[test]
fn elaboration_type_mismatch_pretty_prints_core_terms() {
    let env = env_with_nat();
    let source = r#"
        (def bad_pretty (pi x Nat Nat)
          (lam x Nat
            (pi y zero Nat)))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Expected type mismatch in body");
    assert_eq!(err.to_string(), "Type mismatch: expected Sort, got Nat");
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
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Missing match cases should be rejected");
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
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Duplicate match cases should be rejected");
    match err {
        ElabError::DuplicateMatchCase { ind, ctor, .. } => {
            assert_eq!(ind, "Nat");
            assert_eq!(ctor, "zero");
        }
        other => panic!("Expected DuplicateMatchCase error, got {:?}", other),
    }
}

#[test]
fn elaboration_match_unknown_case_rejected() {
    let env = env_with_nat();
    let source = r#"
        (def bad_case (pi n Nat Nat)
          (lam n Nat
            (match n Nat
              (case (zero) zero)
              (case (bogus) zero))))
    "#;

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Unknown match cases should be rejected");
    match err {
        ElabError::UnknownMatchCase { ind, ctor, .. } => {
            assert_eq!(ind, "Nat");
            assert_eq!(ctor, "bogus");
        }
        other => panic!("Expected UnknownMatchCase error, got {:?}", other),
    }
}

#[test]
fn elaboration_ambiguous_constructor_rejected() {
    let env = env_with_ambiguous_ctor();
    let source = "(def use_mk Foo mk)";

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Ambiguous constructor should be rejected");
    match err {
        ElabError::AmbiguousConstructor {
            name, candidates, ..
        } => {
            assert_eq!(name, "mk");
            assert_eq!(candidates, vec!["Bar.mk".to_string(), "Foo.mk".to_string()]);
        }
        other => panic!("Expected AmbiguousConstructor error, got {:?}", other),
    }
}

#[test]
fn elaboration_module_qualified_name_resolves() {
    let env = env_with_qualified_defs();
    let source = "(def use_alpha Nat Alpha.id)";

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let value = elab
        .check(val, &ty_core)
        .expect("Qualified name should resolve");
    assert_eq!(&*value, &Term::Const("Alpha.id".to_string(), vec![]));
}

#[test]
fn elaboration_import_scope_resolves_unqualified_name() {
    let env = env_with_qualified_defs();
    let source = "(def use_alpha Nat id)";

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);
    elab.set_import_scopes(vec!["Alpha".to_string()]);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let value = elab
        .check(val, &ty_core)
        .expect("Unqualified name should resolve through import scope");
    assert_eq!(&*value, &Term::Const("Alpha.id".to_string(), vec![]));
}

#[test]
fn elaboration_ambiguous_import_scope_requires_qualification() {
    let env = env_with_qualified_defs();
    let source = "(def use_id Nat id)";

    let (_name, ty, val) = parse_single_def(source);
    let mut elab = Elaborator::new(&env);
    elab.set_import_scopes(vec!["Beta".to_string(), "Alpha".to_string()]);

    let (ty_core, ty_ty) = elab.infer(ty).expect("Type should elaborate");
    let ty_ty_whnf = whnf(&env, ty_ty, Transparency::All).expect("whnf failed");
    assert!(
        matches!(&*ty_ty_whnf, Term::Sort(_)),
        "Definition type must be a Sort"
    );

    let err = elab
        .check(val, &ty_core)
        .expect_err("Ambiguous import scopes should require qualification");
    match err {
        ElabError::AmbiguousName {
            name, candidates, ..
        } => {
            assert_eq!(name, "id");
            assert_eq!(
                candidates,
                vec!["Alpha.id".to_string(), "Beta.id".to_string()]
            );
        }
        other => panic!("Expected AmbiguousName, got {:?}", other),
    }
}
