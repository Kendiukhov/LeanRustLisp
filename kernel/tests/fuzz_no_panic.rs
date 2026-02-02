use kernel::ast::{BinderInfo, Level, Term};
use kernel::checker::{infer, Context, Env};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::rc::Rc;

struct Lcg {
    state: u64,
}

impl Lcg {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.state
    }

    fn gen_range(&mut self, max: usize) -> usize {
        if max == 0 {
            return 0;
        }
        (self.next() as usize) % max
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TyKind {
    Prop,
    PropToProp,
}

fn prop_term() -> Rc<Term> {
    Rc::new(Term::Sort(Level::Zero))
}

fn var_of_kind(ctx: &[TyKind], kind: TyKind, rng: &mut Lcg) -> Option<Rc<Term>> {
    let mut indices = Vec::new();
    for (rev_idx, ty) in ctx.iter().rev().enumerate() {
        if *ty == kind {
            indices.push(rev_idx);
        }
    }

    if indices.is_empty() {
        None
    } else {
        let pick = indices[rng.gen_range(indices.len())];
        Some(Rc::new(Term::Var(pick)))
    }
}

fn gen_typed_term(rng: &mut Lcg, depth: usize, ctx: &mut Vec<TyKind>, target: TyKind) -> Rc<Term> {
    let mut choices = Vec::new();

    if var_of_kind(ctx, target, rng).is_some() {
        choices.push(0);
    }

    match target {
        TyKind::Prop => {
            if depth > 0 {
                choices.push(1); // app
                choices.push(2); // let
            }
        }
        TyKind::PropToProp => {
            choices.push(3); // lam
        }
    }

    let choice = choices[rng.gen_range(choices.len())];

    match (target, choice) {
        (_, 0) => var_of_kind(ctx, target, rng).expect("var exists"),
        (TyKind::Prop, 1) => {
            let func = gen_typed_term(rng, depth.saturating_sub(1), ctx, TyKind::PropToProp);
            let arg = gen_typed_term(rng, depth.saturating_sub(1), ctx, TyKind::Prop);
            Rc::new(Term::App(func, arg))
        }
        (TyKind::Prop, 2) => {
            let value = gen_typed_term(rng, depth.saturating_sub(1), ctx, TyKind::Prop);
            ctx.push(TyKind::Prop);
            let body = gen_typed_term(rng, depth.saturating_sub(1), ctx, TyKind::Prop);
            ctx.pop();
            Rc::new(Term::LetE(prop_term(), value, body))
        }
        (TyKind::PropToProp, _) => {
            ctx.push(TyKind::Prop);
            let body = gen_typed_term(rng, depth.saturating_sub(1), ctx, TyKind::Prop);
            ctx.pop();
            Rc::new(Term::Lam(prop_term(), body, BinderInfo::Default))
        }
        _ => prop_term(),
    }
}

#[test]
fn fuzz_infer_no_panic() {
    let env = Env::new();
    let mut rng = Lcg::new(0xDEAD_BEEF);

    for _ in 0..200 {
        let mut ty_ctx = vec![TyKind::Prop];
        let term = gen_typed_term(&mut rng, 4, &mut ty_ctx, TyKind::Prop);
        let mut ctx = Context::new();
        for _ in 0..ty_ctx.len() {
            ctx = ctx.push(prop_term());
        }
        let result = catch_unwind(AssertUnwindSafe(|| infer(&env, &ctx, term.clone())));

        assert!(result.is_ok(), "Kernel panicked on term: {:?}", term);
        let _ = result.unwrap();
    }
}
