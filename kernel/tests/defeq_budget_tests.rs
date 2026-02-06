use kernel::ast::{Definition, Level, Term, Transparency};
use kernel::checker::Env;
use kernel::nbe::is_def_eq_with_fuel;
use std::rc::Rc;

fn build_def_chain(env: &mut Env, depth: usize) -> (Rc<Term>, Rc<Term>) {
    let ty = Rc::new(Term::Sort(Level::Zero));
    env.add_definition(Definition::axiom("base".to_string(), ty.clone()))
        .expect("Failed to add base axiom");

    let mut current = Rc::new(Term::Const("base".to_string(), vec![]));
    for i in 0..depth {
        let name = format!("d{}", i);
        let mut def = Definition::total(name.clone(), ty.clone(), current.clone());
        def.noncomputable = true;
        env.add_definition(def)
            .expect("Failed to add chained definition");
        current = Rc::new(Term::Const(name, vec![]));
    }

    (current, Rc::new(Term::Const("base".to_string(), vec![])))
}

/// Microbench-style guard: a linear delta chain should normalize within a modest fuel budget.
#[test]
fn defeq_microbench_linear_chain_budget() {
    let mut env = Env::new();
    let (deep, base) = build_def_chain(&mut env, 64);
    let budget = 128;

    for _ in 0..50 {
        assert!(
            is_def_eq_with_fuel(deep.clone(), base.clone(), &env, Transparency::All, budget),
            "Linear defeq chain should normalize within budget"
        );
    }
}

/// Regression guard: too-small fuel should fail on the same chain.
#[test]
fn defeq_budget_regression_guard() {
    let mut env = Env::new();
    let (deep, base) = build_def_chain(&mut env, 64);

    assert!(
        !is_def_eq_with_fuel(deep, base, &env, Transparency::All, 10),
        "Insufficient fuel should fail on linear defeq chain"
    );
}
