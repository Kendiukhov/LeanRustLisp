use cli::driver::{process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::ast::Term;
use kernel::checker::Env;
use mir::lower::LoweringContext;
use mir::types::{IdRegistry, MirType, Region};
use mir::{Local, Place, Rvalue, Statement, Terminator};

const BORROW_LOWERING_PRELUDE: &str = r#"
    (inductive copy Nat (sort 1)
      (zero Nat)
      (succ (pi n Nat Nat)))

    (axiom Shared (sort 1))
    (axiom Mut (sort 1))
    (axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
    (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))
    (axiom borrow_mut (pi {A (sort 1)} (pi x A (Ref #[r] Mut A))))
"#;

#[test]
fn borrow_lowering_assigns_distinct_regions() {
    let mut env = Env::new();
    let mut expander = Expander::new();
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
    process_code(
        BORROW_LOWERING_PRELUDE,
        "prelude",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    )
    .expect("prelude processing failed");
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    env.set_allow_reserved_primitives(allow_reserved);
    assert!(
        !diagnostics.has_errors(),
        "prelude diagnostics contained errors"
    );

    let source = r#"
(unsafe borrow_twice (pi x Nat Nat)
  (lam x Nat
    (let r1 (Ref #[r] Shared Nat) (& x)
      (let r2 (Ref #[r] Shared Nat) (& x)
        zero))))
"#;

    diagnostics.diagnostics.clear();
    process_code(
        source,
        "borrow_twice",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    )
    .expect("test source processing failed");
    assert!(
        !diagnostics.has_errors(),
        "test source diagnostics contained errors: {:?}",
        diagnostics.diagnostics
    );

    let def = env
        .definitions()
        .get("borrow_twice")
        .expect("definition not found");
    let value = def.value.as_ref().expect("definition missing value");
    let (arg_ty, body) = match &**value {
        Term::Lam(arg_ty, body, _, _) => (arg_ty.clone(), body.clone()),
        other => panic!("expected lambda value, got {:?}", other),
    };
    let ret_ty = match &*def.ty {
        Term::Pi(_, cod, _, _) => cod.clone(),
        other => panic!("expected Pi type, got {:?}", other),
    };

    let ids = IdRegistry::from_env(&env);
    let mut ctx = LoweringContext::new(vec![("x".to_string(), arg_ty)], ret_ty, &env, &ids)
        .expect("context init should succeed");
    let return_block = ctx.new_block();
    ctx.body.basic_blocks[return_block.index()].terminator = Some(Terminator::Return);
    ctx.lower_term(&body, Place::from(Local(0)), return_block)
        .expect("lowering failed");
    let body = ctx.finish();

    let mut regions = Vec::new();
    for bb in &body.basic_blocks {
        for stmt in &bb.statements {
            if let Statement::Assign(place, Rvalue::Ref(_, _)) = stmt {
                match &body.local_decls[place.local.index()].ty {
                    MirType::Ref(region, _, _) => regions.push(*region),
                    other => panic!("expected ref type for borrow dest, got {:?}", other),
                }
            }
        }
    }

    assert_eq!(regions.len(), 2, "expected two borrow sites");
    assert_ne!(regions[0], regions[1], "borrow regions must be distinct");
    assert_ne!(
        regions[0],
        Region::STATIC,
        "borrow region must not be static"
    );
    assert_ne!(
        regions[1],
        Region::STATIC,
        "borrow region must not be static"
    );
}
