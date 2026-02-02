use crate::surface::{SurfaceTerm, SurfaceTermKind, Span};
use kernel::ast::{Term, Level};
use kernel::checker::{Env, Context, infer as infer_type, TypeError, compute_recursor_type, check_elimination_restriction};
use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ElabError {
    #[error("Unbound variable: {0}")]
    UnboundVariable(String, Span),
    #[error("Unknown inductive type: {0}")]
    UnknownInductive(String, Span),
    #[error("Elaboration not implemented for this term")]
    NotImplemented(Span),
    #[error("Type inference failed during elaboration: {0:?}")]
    InferenceError(kernel::checker::TypeError, Span),
    #[error("Type mismatch: expected {expected}, got {got}")]
    TypeMismatch {
        expected: String,
        got: String,
        span: Span,
    },
    #[error("Non-exhaustive match on {ind}: missing cases {missing:?}")]
    NonExhaustiveMatch {
        ind: String,
        missing: Vec<String>,
        span: Span,
    },
    #[error("Duplicate case {ctor} in match on {ind}")]
    DuplicateMatchCase {
        ind: String,
        ctor: String,
        span: Span,
    },
    #[error("Unknown constructor {ctor} in match on {ind}")]
    UnknownMatchCase {
        ind: String,
        ctor: String,
        span: Span,
    },
    #[error("Unification failed: {0:?} vs {1:?}")]
    UnificationError(Rc<Term>, Rc<Term>),
    #[error("Occurs check failed: tried to solve {0} with {1:?}")]
    OccursCheck(usize, Rc<Term>),
    #[error("Metavariable solution {0:?} contains free variables")]
    SolutionContainsFreeVariables(Rc<Term>),
    #[error("Unsolved constraints remaining: {0}")]
    UnsolvedConstraints(String),
    #[error("Recursor requires a motive to infer universe level")]
    RecursorNeedsMotive(Span),
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Unification {
        t1: Rc<Term>,
        t2: Rc<Term>,
        span: Span,
        context: Vec<(String, Rc<Term>)>,
    }
}

#[derive(Debug, Clone)]
struct MetaContext {
    binders: Vec<(String, Rc<Term>)>,
}

impl MetaContext {
    fn len(&self) -> usize {
        self.binders.len()
    }
}

/// Result of attempting unification
#[derive(Debug)]
pub enum UnifyResult {
    /// Unification succeeded
    Success,
    /// Unification is stuck on unsolved metavariables - can be retried later
    Stuck(Rc<Term>, Rc<Term>),
    /// Unification definitively failed - types are incompatible
    Failed(Rc<Term>, Rc<Term>),
}

fn collect_app_spine(term: SurfaceTerm) -> (SurfaceTerm, Vec<(SurfaceTerm, bool)>) {
    let mut args = Vec::new();
    let mut head = term;
    loop {
        match head.kind {
            SurfaceTermKind::App(f, x, is_explicit) => {
                args.push((*x, is_explicit));
                head = *f;
            }
            _ => break,
        }
    }
    args.reverse();
    (head, args)
}

pub struct Elaborator<'a> {
    env: &'a Env,
    locals: Vec<(String, Rc<Term>)>,
    meta_counter: usize,
    meta_solutions: HashMap<usize, Rc<Term>>,
    meta_contexts: HashMap<usize, MetaContext>,
    constraints: Vec<Constraint>,
}

impl<'a> Elaborator<'a> {
    pub fn new(env: &'a Env) -> Self {
        Elaborator {
            env,
            locals: Vec::new(),
            meta_counter: 0,
            meta_solutions: HashMap::new(),
            meta_contexts: HashMap::new(),
            constraints: Vec::new(),
        }
    }

    fn defeq_transparency(&self) -> kernel::Transparency {
        kernel::Transparency::Reducible
    }

    fn whnf(&self, term: Rc<Term>) -> Result<Rc<Term>, ElabError> {
        let ctx = self.build_context();
        kernel::checker::whnf_in_ctx(self.env, &ctx, term, self.defeq_transparency())
            .map_err(|e| ElabError::InferenceError(e, Span { start: 0, end: 0, line: 0, col: 0 }))
    }

    fn is_def_eq_in_ctx(&self, t1: &Rc<Term>, t2: &Rc<Term>) -> Result<bool, ElabError> {
        let ctx = self.build_context();
        kernel::checker::is_def_eq_in_ctx(
            self.env,
            &ctx,
            t1.clone(),
            t2.clone(),
            self.defeq_transparency(),
        )
        .map_err(|e| ElabError::InferenceError(e, Span { start: 0, end: 0, line: 0, col: 0 }))
    }

    fn resolve_name(&self, name: &str) -> Option<Rc<Term>> {
        for (i, (local_name, _)) in self.locals.iter().rev().enumerate() {
            if local_name == name {
                return Some(Rc::new(Term::Var(i)));
            }
        }

        if name == "Type" {
            // "Type" in surface syntax is elaborated to kernel's Sort(Succ(Zero)) = Type 0
            return Some(Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero)))));
        }

        if let Some(_) = self.env.get_inductive(name) {
            return Some(Rc::new(Term::Ind(name.to_string(), vec![])));
        }
        
        if let Some(_) = self.env.get_definition(name) {
            // This branch would return an ElabError, but resolve_name returns Option<Rc<Term>>.
            // To maintain syntactic correctness and the existing return type, we must return Some or None.
            // Assuming the intent was to resolve to a Const if it's a definition, similar to get_def.
            // If the intent was to make resolve_name return a Result, that would be a larger change.
            return Some(Rc::new(Term::Const(name.to_string(), vec![])));
        }

        for (ind_name, decl) in &self.env.inductives {
            for (i, ctor) in decl.ctors.iter().enumerate() {
                if ctor.name == name {
                    return Some(Rc::new(Term::Ctor(ind_name.clone(), i, vec![])));
                }
            }
        }

        None
    }

    fn build_context(&self) -> Context {
        let mut ctx = Context::new();
        for (_, ty) in &self.locals {
            ctx = ctx.push(ty.clone());
        }
        ctx
    }

    fn recursor_type(&self, ind_name: &str, levels: &[Level]) -> Result<Rc<Term>, ElabError> {
        let decl = self.env.get_inductive(ind_name)
            .ok_or_else(|| ElabError::UnknownInductive(ind_name.to_string(), Span { start: 0, end: 0, line: 0, col: 0 }))?;
        Ok(compute_recursor_type(decl, levels))
    }

    fn extract_result_sort_level(&self, ty: Rc<Term>, span: Span) -> Result<Level, ElabError> {
        let mut current = self.whnf(ty)?;
        loop {
            match &*current {
                Term::Pi(_, body, _) => {
                    current = self.whnf(body.clone())?;
                }
                Term::Sort(level) => return Ok(level.clone()),
                _ => {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: format!("{:?}", current),
                        span,
                    });
                }
            }
        }
    }

    fn apply_pi_type(&self, ty: Rc<Term>, arg: &Rc<Term>, span: Span) -> Result<Rc<Term>, ElabError> {
        let ty_whnf = self.whnf(ty)?;
        if let Term::Pi(_, body, _) = &*ty_whnf {
            Ok(body.subst(0, arg))
        } else {
            Err(ElabError::InferenceError(TypeError::ExpectedFunction(ty_whnf), span))
        }
    }

    pub fn infer(&mut self, term: SurfaceTerm) -> Result<(Rc<Term>, Rc<Term>), ElabError> {
        let span = term.span;
        match term.kind {
            SurfaceTermKind::Var(name) => {
                let elab_term = self.resolve_name(&name).ok_or(ElabError::UnboundVariable(name, span))?;
                let ctx = self.build_context();
                let ty = infer_type(self.env, &ctx, elab_term.clone()).map_err(|e| ElabError::InferenceError(e, span))?;
                Ok((elab_term, ty))
            }
            SurfaceTermKind::Sort(l) => {
                let term = Rc::new(Term::Sort(l.clone()));
                let ty = Rc::new(Term::Sort(Level::Succ(Box::new(l))));
                Ok((term, ty))
            }
            SurfaceTermKind::App(f, x, is_explicit) => {
                let term = SurfaceTerm { kind: SurfaceTermKind::App(f, x, is_explicit), span };
                let (head, args) = collect_app_spine(term);
                if let SurfaceTermKind::Rec(ind_name) = head.kind {
                    return self.infer_rec_application(ind_name, args, span);
                }

                let (mut f_elab, mut f_ty) = self.infer(head)?;

                for (arg, is_explicit) in args {
                    let mut f_ty_whnf = self.whnf(f_ty.clone())?;

                    // Insert implicit arguments
                    loop {
                        match &*f_ty_whnf {
                            Term::Pi(_, ret_ty, info) => {
                                match info {
                                    kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit => {
                                        if is_explicit {
                                            let meta_id = self.meta_counter;
                                            self.meta_counter += 1;
                                            let meta_term = Rc::new(Term::Meta(meta_id));
                                            self.meta_contexts.insert(meta_id, MetaContext { binders: self.locals.clone() });

                                            f_elab = Rc::new(Term::App(f_elab, meta_term.clone()));
                                            f_ty = ret_ty.subst(0, &meta_term);
                                            f_ty_whnf = self.whnf(f_ty.clone())?;
                                        } else {
                                            break;
                                        }
                                    }
                                    kernel::ast::BinderInfo::Default => {
                                        if !is_explicit {
                                            return Err(ElabError::TypeMismatch {
                                                expected: "Implicit binder".to_string(),
                                                got: "Explicit argument".to_string(),
                                                span,
                                            });
                                        }
                                        break;
                                    }
                                }
                            }
                            _ => break,
                        }
                    }

                    if let Term::Pi(arg_ty, ret_ty, _) = &*f_ty_whnf {
                        let x_elab = self.check(arg, &arg_ty)?;
                        f_elab = Rc::new(Term::App(f_elab, x_elab.clone()));
                        f_ty = ret_ty.subst(0, &x_elab);
                    } else {
                        return Err(ElabError::InferenceError(TypeError::ExpectedFunction(f_ty_whnf), span));
                    }
                }

                Ok((f_elab, f_ty))
            }
            SurfaceTermKind::Pi(name, binder_info, ty, body) => {
                // Infer the domain type and check it's a Sort
                let (ty_elab, ty_ty) = self.infer(*ty)?;
                let ty_ty_whnf = self.whnf(ty_ty)?;
                if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: format!("{:?}", ty_ty_whnf),
                        span,
                    });
                }

                self.locals.push((name, ty_elab.clone()));
                let (body_elab, _body_ty) = self.infer(*body)?;
                self.locals.pop();

                let pi_term = Rc::new(Term::Pi(ty_elab, body_elab, binder_info));
                let ty_ty = infer_type(self.env, &self.build_context(), pi_term.clone()).map_err(|e| ElabError::InferenceError(e, span))?;

                Ok((pi_term, ty_ty))
            }
            SurfaceTermKind::Lam(name, binder_info, ty, body) => {
                // Infer the type annotation and check it's a Sort
                let (ty_elab, ty_ty) = self.infer(*ty)?;
                let ty_ty_whnf = self.whnf(ty_ty)?;
                if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: format!("{:?}", ty_ty_whnf),
                        span,
                    });
                }
                self.locals.push((name.clone(), ty_elab.clone()));
                let (body_elab, body_ty) = self.infer(*body)?;
                self.locals.pop();

                let lam_term = Rc::new(Term::Lam(ty_elab.clone(), body_elab, binder_info));
                let lam_ty = Rc::new(Term::Pi(ty_elab, body_ty, binder_info));
                Ok((lam_term, lam_ty))
            }
            SurfaceTermKind::Let(name, ty, val, body) => {
                // Infer the type annotation and check it's a Sort
                let (ty_elab, ty_ty) = self.infer(*ty)?;
                let ty_ty_whnf = self.whnf(ty_ty)?;
                if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: format!("{:?}", ty_ty_whnf),
                        span,
                    });
                }
                let val_elab = self.check(*val, &ty_elab)?;
                
                self.locals.push((name, ty_elab.clone()));
                let (body_elab, body_ty) = self.infer(*body)?;
                self.locals.pop();
                
                let let_term = Rc::new(Term::LetE(ty_elab, val_elab, body_elab));
                Ok((let_term, body_ty))
            }
            SurfaceTermKind::Hole => {
                let meta_id = self.meta_counter;
                self.meta_counter += 1;
                let meta_term = Rc::new(Term::Meta(meta_id));
                self.meta_contexts.insert(meta_id, MetaContext { binders: self.locals.clone() });

                let type_meta_id = self.meta_counter;
                self.meta_counter += 1;
                let type_meta_term = Rc::new(Term::Meta(type_meta_id));
                self.meta_contexts.insert(type_meta_id, MetaContext { binders: self.locals.clone() });

                Ok((meta_term, type_meta_term))
            }
            SurfaceTermKind::Ind(name) => {
                let decl = self.env.get_inductive(&name)
                    .ok_or_else(|| ElabError::UnknownInductive(name.clone(), span))?;
                let ind_term = Rc::new(Term::Ind(name, vec![]));
                let ty = decl.ty.clone();
                Ok((ind_term, ty))
            }
            SurfaceTermKind::Ctor(ind_name, idx) => {
                let decl = self.env.get_inductive(&ind_name)
                    .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?;
                let ctor = decl.ctors.get(idx)
                    .ok_or_else(|| ElabError::NotImplemented(span))?;
                let ctor_term = Rc::new(Term::Ctor(ind_name, idx, vec![]));
                let ty = ctor.ty.clone();
                Ok((ctor_term, ty))
            }
            SurfaceTermKind::Rec(ind_name) => {
                let _ = self.env.get_inductive(&ind_name)
                    .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?;
                Err(ElabError::RecursorNeedsMotive(span))
            }
            SurfaceTermKind::Match(scrutinee, ret_type, cases) => {
                self.elaborate_match(*scrutinee, *ret_type, cases, span)
            }
            SurfaceTermKind::Fix(name, ty, body) => {
                // Infer the type annotation and check it's a Sort
                let (ty_elab, ty_ty) = self.infer(*ty)?;
                let ty_ty_whnf = self.whnf(ty_ty)?;
                if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "Sort".to_string(),
                        got: format!("{:?}", ty_ty_whnf),
                        span,
                    });
                }
                
                // Fix f:T. body. body should have type T under f:T.
                self.locals.push((name, ty_elab.clone()));
                let body_elab = self.check(*body, &ty_elab)?;
                self.locals.pop();
                
                let fix_term = Rc::new(Term::Fix(ty_elab.clone(), body_elab));
                Ok((fix_term, ty_elab))
            }

            _ => Err(ElabError::NotImplemented(span)),
        }
    }

    fn infer_rec_application(
        &mut self,
        ind_name: String,
        args: Vec<(SurfaceTerm, bool)>,
        span: Span,
    ) -> Result<(Rc<Term>, Rc<Term>), ElabError> {
        let decl = self.env.get_inductive(&ind_name)
            .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?;

        let num_params = decl.num_params;
        if args.len() <= num_params {
            return Err(ElabError::RecursorNeedsMotive(span));
        }

        // Infer the motive argument to determine the universe level.
        let (motive_term, motive_ty) = self.infer(args[num_params].0.clone())?;
        let motive_level = self.extract_result_sort_level(motive_ty.clone(), span)?;
        let levels = vec![motive_level];

        check_elimination_restriction(self.env, &ind_name, &levels)
            .map_err(|e| ElabError::InferenceError(e, span))?;

        let mut f_elab = Rc::new(Term::Rec(ind_name.clone(), levels.clone()));
        let mut f_ty = self.recursor_type(&ind_name, &levels)?;

        for (idx, (arg, is_explicit)) in args.into_iter().enumerate() {
            let mut f_ty_whnf = self.whnf(f_ty.clone())?;

            // Insert implicit arguments
            loop {
                match &*f_ty_whnf {
                    Term::Pi(_, ret_ty, info) => {
                        match info {
                            kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit => {
                                if is_explicit {
                                    let meta_id = self.meta_counter;
                                    self.meta_counter += 1;
                                    let meta_term = Rc::new(Term::Meta(meta_id));
                                    self.meta_contexts.insert(meta_id, MetaContext { binders: self.locals.clone() });

                                    f_elab = Rc::new(Term::App(f_elab, meta_term.clone()));
                                    f_ty = ret_ty.subst(0, &meta_term);
                                    f_ty_whnf = self.whnf(f_ty.clone())?;
                                } else {
                                    break;
                                }
                            }
                            kernel::ast::BinderInfo::Default => {
                                if !is_explicit {
                                    return Err(ElabError::TypeMismatch {
                                        expected: "Implicit binder".to_string(),
                                        got: "Explicit argument".to_string(),
                                        span,
                                    });
                                }
                                break;
                            }
                        }
                    }
                    _ => break,
                }
            }

            if let Term::Pi(arg_ty, ret_ty, _) = &*f_ty_whnf {
                let x_elab = if idx == num_params {
                    self.unify_with_span(&motive_ty, &arg_ty, span)?;
                    motive_term.clone()
                } else {
                    self.check(arg, &arg_ty)?
                };
                f_elab = Rc::new(Term::App(f_elab, x_elab.clone()));
                f_ty = ret_ty.subst(0, &x_elab);
            } else {
                return Err(ElabError::InferenceError(TypeError::ExpectedFunction(f_ty_whnf), span));
            }
        }

        Ok((f_elab, f_ty))
    }

    pub fn check(&mut self, term: SurfaceTerm, expected_type: &Rc<Term>) -> Result<Rc<Term>, ElabError> {
        let span = term.span;
        let kind = term.kind;
        match (kind.clone(), &**expected_type) {
            (SurfaceTermKind::Lam(name, binder_info, ty, body), Term::Pi(expected_arg_ty, expected_ret_ty, expected_info)) => {
                 if binder_info == kernel::ast::BinderInfo::Default && *expected_info == kernel::ast::BinderInfo::Implicit {
                     // Insert implicit lambda
                     let implicit_name = format!("_imp_{}", self.locals.len());
                     self.locals.push((implicit_name, expected_arg_ty.clone()));
                     // Recursively check the SAME term against the body type
                     // We reconstruct the Lam term because we don't have ownership of the original text separate from destructuring
                     let inner = self.check(SurfaceTerm { kind: SurfaceTermKind::Lam(name, binder_info, ty, body), span }, expected_ret_ty)?;
                     self.locals.pop();
                     Ok(Rc::new(Term::Lam(expected_arg_ty.clone(), inner, *expected_info)))
                 } else {
                     // Standard checking - verify the type annotation is a Sort (any level)
                     let (ty_elab, ty_ty) = self.infer(*ty)?;
                     let ty_ty_whnf = self.whnf(ty_ty)?;
                     if !matches!(&*ty_ty_whnf, Term::Sort(_)) {
                         return Err(ElabError::TypeMismatch {
                             expected: "Sort".to_string(),
                             got: format!("{:?}", ty_ty_whnf),
                             span,
                         });
                     }
                     // Unify the provided type with the expected argument type
                     self.unify_with_span(&ty_elab, expected_arg_ty, span)?;

                     self.locals.push((name.clone(), expected_arg_ty.clone()));
                     let body_elab = self.check(*body, expected_ret_ty)?;
                     self.locals.pop();

                     Ok(Rc::new(Term::Lam(expected_arg_ty.clone(), body_elab, binder_info)))
                 }
            }
            _ => {
                let (mut elab_term, mut inferred_type) = self.infer(SurfaceTerm { kind, span })?;

                // Insert implicit arguments if inferred type has leading implicit Pis
                // This handles cases like checking `nil` against `List Nat`
                let mut inferred_whnf = self.whnf(inferred_type.clone())?;
                loop {
                    match &*inferred_whnf {
                        Term::Pi(_, ret_ty, info) if *info == kernel::ast::BinderInfo::Implicit || *info == kernel::ast::BinderInfo::StrictImplicit => {
                            // Insert a meta for this implicit argument
                            let meta_id = self.meta_counter;
                            self.meta_counter += 1;
                            let meta_term = Rc::new(Term::Meta(meta_id));
                            self.meta_contexts.insert(meta_id, MetaContext { binders: self.locals.clone() });

                            elab_term = Rc::new(Term::App(elab_term, meta_term.clone()));
                            inferred_type = ret_ty.subst(0, &meta_term);
                            inferred_whnf = self.whnf(inferred_type.clone())?;
                        }
                        _ => break,
                    }
                }

                self.unify_with_span(&inferred_type, expected_type, span)?;
                Ok(elab_term)
            }
        }
    }

    /// Elaborate a match expression to a recursor application
    fn elaborate_match(
        &mut self,
        scrutinee: SurfaceTerm,
        ret_type: SurfaceTerm,
        cases: Vec<(String, Vec<String>, SurfaceTerm)>,
        span: Span,
    ) -> Result<(Rc<Term>, Rc<Term>), ElabError> {
        // Infer the scrutinee type to get the inductive name
        let (scrut_elab, scrut_ty) = self.infer(scrutinee)?;

        // Extract the inductive name and args from the scrutinee type
        let scrut_ty_whnf = self.whnf(scrut_ty.clone())?;
        let (ind_name, ind_args) = self.extract_inductive_info(&scrut_ty_whnf)
            .ok_or_else(|| ElabError::TypeMismatch {
                expected: "inductive type".to_string(),
                got: format!("{:?}", scrut_ty_whnf),
                span,
            })?;

        // Get the inductive declaration
        let decl = self.env.get_inductive(&ind_name)
            .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?
            .clone();

        // Validate match cases: no unknown constructors, no duplicates, and exhaustive coverage.
        let ctor_names: HashSet<String> = decl.ctors.iter().map(|ctor| ctor.name.clone()).collect();
        let mut seen_cases: HashSet<String> = HashSet::new();
        for (case_name, _, _) in &cases {
            if !ctor_names.contains(case_name) {
                return Err(ElabError::UnknownMatchCase {
                    ind: ind_name.clone(),
                    ctor: case_name.clone(),
                    span,
                });
            }
            if !seen_cases.insert(case_name.clone()) {
                return Err(ElabError::DuplicateMatchCase {
                    ind: ind_name.clone(),
                    ctor: case_name.clone(),
                    span,
                });
            }
        }

        let mut missing = Vec::new();
        for ctor in &decl.ctors {
            if !seen_cases.contains(&ctor.name) {
                missing.push(ctor.name.clone());
            }
        }
        if !missing.is_empty() {
            return Err(ElabError::NonExhaustiveMatch {
                ind: ind_name.clone(),
                missing,
                span,
            });
        }

        // Elaborate the return type (motive body) and ensure it is a type
        let (ret_type_elab, ret_type_ty) = self.infer(ret_type)?;
        let ret_type_ty_whnf = self.whnf(ret_type_ty)?;
        if !matches!(&*ret_type_ty_whnf, Term::Sort(_)) {
            return Err(ElabError::TypeMismatch {
                expected: "Sort".to_string(),
                got: format!("{:?}", ret_type_ty_whnf),
                span,
            });
        }

        // Split params/indices from scrutinee type arguments
        let num_params = decl.num_params;
        let (param_args, index_args) = if ind_args.len() >= num_params {
            (ind_args[..num_params].to_vec(), ind_args[num_params..].to_vec())
        } else {
            return Err(ElabError::TypeMismatch {
                expected: format!("{} parameters", num_params),
                got: format!("{}", ind_args.len()),
                span,
            });
        };

        // Instantiate index binder types using parameters
        let mut index_types = Vec::new();
        let mut current = self.instantiate_params(decl.ty.clone(), &param_args);
        while let Term::Pi(dom, body, _) = &*current {
            index_types.push(dom.clone());
            current = body.clone();
        }

        // Build major type: Ind params indices (with index vars)
        let mut major_ty = Rc::new(Term::Ind(ind_name.clone(), vec![]));
        for param in &param_args {
            major_ty = Rc::new(Term::App(major_ty, param.shift(0, index_types.len())));
        }
        for i in 0..index_types.len() {
            let idx = index_types.len() - 1 - i;
            major_ty = Rc::new(Term::App(major_ty, Rc::new(Term::Var(idx))));
        }

        // Build motive as lambdas over indices then major.
        // Lift the return type into the index-binder context, then add major,
        // then wrap index binders without shifting (they're already accounted for).
        let index_count = index_types.len();
        let mut motive = ret_type_elab.shift(0, index_count);
        motive = Rc::new(Term::Lam(
            major_ty.clone(),
            motive.shift(0, 1),
            kernel::ast::BinderInfo::Default,
        ));
        for ty in index_types.iter().rev() {
            motive = Rc::new(Term::Lam(ty.clone(), motive, kernel::ast::BinderInfo::Default));
        }

        // Determine universe level from motive type
        let motive_ty = infer_type(self.env, &self.build_context(), motive.clone())
            .map_err(|e| ElabError::InferenceError(e, span))?;
        let motive_level = self.extract_result_sort_level(motive_ty, span)?;

        check_elimination_restriction(self.env, &ind_name, &[motive_level.clone()])
            .map_err(|e| ElabError::InferenceError(e, span))?;

        // Start building the recursor application: Ind.rec [params] motive
        let rec_term = Rc::new(Term::Rec(ind_name.clone(), vec![motive_level.clone()]));
        let mut result = rec_term;
        
        // Apply parameters first
        for arg in &param_args {
            result = Rc::new(Term::App(result, arg.clone()));
        }
        
        // Apply motive
        result = Rc::new(Term::App(result, motive.clone()));

        // Compute expected minor premise types from recursor type
        let mut rec_ty = self.recursor_type(&ind_name, &[motive_level])?;
        for arg in &param_args {
            rec_ty = self.apply_pi_type(rec_ty, arg, span)?;
        }
        rec_ty = self.apply_pi_type(rec_ty, &motive, span)?;

        // Elaborate each case and apply as a minor premise
        for ctor in decl.ctors.iter() {
            let current_whnf = self.whnf(rec_ty.clone())?;
            let minor_ty = if let Term::Pi(dom, _, _) = &*current_whnf {
                dom.clone()
            } else {
                return Err(ElabError::InferenceError(TypeError::ExpectedFunction(current_whnf), span));
            };

            let case = cases.iter().find(|(name, _, _)| name == &ctor.name);
            let case_elab = match case {
                Some((_, bindings, body)) => {
                    let (binders, result_ty) = self.split_minor_premise(&minor_ty);
                    self.elaborate_case(bindings, body, &binders, &result_ty)?
                }
                None => {
                    // Missing case - this is an error in a proper implementation
                    // For now, we use a hole (metavariable)
                    let meta_id = self.meta_counter;
                    self.meta_counter += 1;
                    let meta = Rc::new(Term::Meta(meta_id));
                    self.meta_contexts.insert(meta_id, MetaContext { binders: self.locals.clone() });
                    meta
                }
            };

            result = Rc::new(Term::App(result, case_elab.clone()));
            rec_ty = self.apply_pi_type(rec_ty, &case_elab, span)?;
        }

        // Apply indices (if any), then scrutinee
        for arg in &index_args {
            result = Rc::new(Term::App(result, arg.clone()));
        }
        result = Rc::new(Term::App(result, scrut_elab.clone()));

        // The result type is motive applied to indices and scrutinee
        let mut result_ty = motive.clone();
        for arg in &index_args {
            result_ty = Rc::new(Term::App(result_ty, arg.clone()));
        }
        result_ty = Rc::new(Term::App(result_ty, scrut_elab.clone()));

        Ok((result, result_ty))
    }

    /// Extract the inductive type name and arguments from a type
    fn extract_inductive_info(&self, ty: &Rc<Term>) -> Option<(String, Vec<Rc<Term>>)> {
        match &**ty {
            Term::Ind(name, _) => Some((name.clone(), Vec::new())),
            Term::App(f, a) => {
                let (name, mut args) = self.extract_inductive_info(f)?;
                args.push(a.clone());
                Some((name, args))
            }
            _ => None,
        }
    }

    /// Instantiate parameters in a constructor type
    fn instantiate_params(&self, mut ty: Rc<Term>, params: &[Rc<Term>]) -> Rc<Term> {
        for param in params {
            if let Term::Pi(_, body, _) = &*ty {
                ty = body.subst(0, param);
            } else {
                break;
            }
        }
        ty
    }

    /// Elaborate a single case branch against an expected minor premise type.
    fn elaborate_case(
        &mut self,
        bindings: &[String],
        body: &SurfaceTerm,
        binders: &[(Rc<Term>, kernel::ast::BinderInfo)],
        result_ty: &Rc<Term>,
    ) -> Result<Rc<Term>, ElabError> {
        let explicit_arg_count = binders.iter()
            .filter(|(_, info)| *info == kernel::ast::BinderInfo::Default)
            .count();

        let padded_bindings: Vec<String> = if bindings.len() < explicit_arg_count {
            let mut b = bindings.to_vec();
            for i in bindings.len()..explicit_arg_count {
                b.push(format!("_arg{}", i));
            }
            b
        } else {
            bindings[..explicit_arg_count.min(bindings.len())].to_vec()
        };

        let mut locals_added = 0;
        let mut binding_idx = 0;
        for (i, (arg_ty, info)) in binders.iter().enumerate() {
            let name = if *info == kernel::ast::BinderInfo::Default {
                let n = padded_bindings.get(binding_idx)
                    .cloned()
                    .unwrap_or_else(|| format!("_explicit{}", i));
                binding_idx += 1;
                n
            } else {
                format!("_implicit{}", i)
            };
            self.locals.push((name, arg_ty.clone()));
            locals_added += 1;
        }

        let result_ty = self.whnf(result_ty.clone())?;
        let body_elab = self.check(body.clone(), &result_ty)?;

        for _ in 0..locals_added {
            self.locals.pop();
        }

        let mut result = body_elab;
        for (arg_ty, info) in binders.iter().rev() {
            result = Rc::new(Term::Lam(arg_ty.clone(), result, *info));
        }

        Ok(result)
    }

    fn split_minor_premise(
        &self,
        minor_ty: &Rc<Term>,
    ) -> (Vec<(Rc<Term>, kernel::ast::BinderInfo)>, Rc<Term>) {
        let mut binders: Vec<(Rc<Term>, kernel::ast::BinderInfo)> = Vec::new();
        let mut current = minor_ty.clone();
        while let Term::Pi(arg_ty, body_ty, info) = &*current {
            binders.push((arg_ty.clone(), *info));
            current = body_ty.clone();
        }
        (binders, current)
    }

    /// Count the number of Pi arguments in a type
    fn count_pi_args(&self, ty: &Rc<Term>) -> usize {
        match &**ty {
            Term::Pi(_, body, _) => 1 + self.count_pi_args(body),
            _ => 0,
        }
    }

    /// Find indices of recursive arguments (arguments whose type is the inductive type)
    fn find_recursive_args(&self, ty: &Rc<Term>, ind_name: &str) -> Vec<usize> {
        let mut result = Vec::new();
        let mut current = ty;
        let mut idx = 0;

        while let Term::Pi(arg_ty, body, _) = &**current {
            if self.type_refers_to_ind(arg_ty, ind_name) {
                result.push(idx);
            }
            current = body;
            idx += 1;
        }

        result
    }

    /// Check if a type refers to an inductive type
    fn type_refers_to_ind(&self, ty: &Rc<Term>, ind_name: &str) -> bool {
        match &**ty {
            Term::Ind(name, _) => name == ind_name,
            Term::App(f, _) => self.type_refers_to_ind(f, ind_name),
            _ => false,
        }
    }

    /// Extract argument types from a Pi type
    fn extract_pi_arg_types(&self, ty: &Rc<Term>) -> Vec<Rc<Term>> {
        let mut result = Vec::new();
        let mut current = ty;

        while let Term::Pi(arg_ty, body, _) = &**current {
            result.push(arg_ty.clone());
            current = body;
        }

        result
    }

    /// Extract EXPLICIT argument types from a Pi type (skipping implicits)
    /// Also returns the count of implicit args that were skipped
    fn extract_explicit_pi_arg_types(&self, ty: &Rc<Term>) -> (Vec<Rc<Term>>, usize) {
        let mut result = Vec::new();
        let mut current = ty;
        let mut implicit_count = 0;

        while let Term::Pi(arg_ty, body, info) = &**current {
            match info {
                kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit => {
                    implicit_count += 1;
                }
                kernel::ast::BinderInfo::Default => {
                    result.push(arg_ty.clone());
                }
            }
            current = body;
        }

        (result, implicit_count)
    }

    /// Count only explicit Pi arguments
    fn count_explicit_pi_args(&self, ty: &Rc<Term>) -> usize {
        let mut count = 0;
        let mut current = ty;

        while let Term::Pi(_, body, info) = &**current {
            if *info == kernel::ast::BinderInfo::Default {
                count += 1;
            }
            current = body;
        }

        count
    }

    /// Attempt to unify two terms, with proper span tracking for error messages.
    /// If unification is stuck on metavariables, the constraint is postponed.
    fn unify_with_span(&mut self, t1: &Rc<Term>, t2: &Rc<Term>, span: Span) -> Result<(), ElabError> {
        match self.unify_core(t1, t2) {
            UnifyResult::Success => Ok(()),
            UnifyResult::Stuck(t1_stuck, t2_stuck) => {
                // Postpone the constraint with proper span
                self.constraints.push(Constraint::Unification {
                    t1: t1_stuck,
                    t2: t2_stuck,
                    span,
                    context: self.locals.clone(),
                });
                Ok(())
            }
            UnifyResult::Failed(t1_fail, t2_fail) => {
                Err(ElabError::UnificationError(t1_fail, t2_fail))
            }
        }
    }

    /// Legacy unify without span - uses a default span.
    /// Prefer `unify_with_span` when span is available.
    fn unify(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> Result<(), ElabError> {
        // Use a sentinel span to indicate "no span available"
        let default_span = Span { start: 0, end: 0, line: 0, col: 0 };
        self.unify_with_span(t1, t2, default_span)
    }

    /// Core unification logic that returns a detailed result.
    /// - Success: terms are definitionally equal or unification succeeded
    /// - Stuck: unification blocked on unsolved metavariables
    /// - Failed: terms are definitively incompatible
    fn unify_core(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> UnifyResult {
        // First resolve metas, then check definitional equality
        let ctx_len = self.locals.len();
        let t1 = self.resolve_metas_in_ctx(t1, ctx_len);
        let t2 = self.resolve_metas_in_ctx(t2, ctx_len);

        // Check definitional equality on resolved terms
        match self.is_def_eq_in_ctx(&t1, &t2) {
            Ok(true) => return UnifyResult::Success,
            Ok(false) => {}
            Err(_) => return UnifyResult::Failed(t1.clone(), t2.clone()),
        }

        match (&*t1, &*t2) {
            // Same metavariable
            (Term::Meta(id1), Term::Meta(id2)) if id1 == id2 => UnifyResult::Success,

            // Metavariable on one side - try to solve it
            (Term::Meta(id), term) | (term, Term::Meta(id)) => {
                let meta_ctx_len = match self.meta_contexts.get(id) {
                    Some(ctx) => ctx.len(),
                    None => return UnifyResult::Failed(t1.clone(), t2.clone()),
                };
                match self.solve_meta(*id, Rc::new(term.clone()), ctx_len, meta_ctx_len) {
                    Ok(()) => UnifyResult::Success,
                    Err(_) => {
                        // Occurs check or scope error - this is stuck, not failed
                        // because we might solve other metas first
                        UnifyResult::Stuck(t1.clone(), t2.clone())
                    }
                }
            }

            // Structural cases - recurse
            (Term::App(f1, a1), Term::App(f2, a2)) => {
                match self.unify_core(f1, f2) {
                    UnifyResult::Success => self.unify_core(a1, a2),
                    UnifyResult::Stuck(_, _) => UnifyResult::Stuck(t1.clone(), t2.clone()),
                    UnifyResult::Failed(_, _) => UnifyResult::Failed(t1.clone(), t2.clone()),
                }
            }
            (Term::Pi(ty1, b1, _), Term::Pi(ty2, b2, _)) => {
                match self.unify_core(ty1, ty2) {
                    UnifyResult::Success => self.unify_core(b1, b2),
                    UnifyResult::Stuck(_, _) => UnifyResult::Stuck(t1.clone(), t2.clone()),
                    UnifyResult::Failed(_, _) => UnifyResult::Failed(t1.clone(), t2.clone()),
                }
            }
            (Term::Lam(ty1, b1, _), Term::Lam(ty2, b2, _)) => {
                match self.unify_core(ty1, ty2) {
                    UnifyResult::Success => self.unify_core(b1, b2),
                    UnifyResult::Stuck(_, _) => UnifyResult::Stuck(t1.clone(), t2.clone()),
                    UnifyResult::Failed(_, _) => UnifyResult::Failed(t1.clone(), t2.clone()),
                }
            }

            // Check if either side contains unsolved metas - if so, it's stuck
            _ => {
                if self.contains_any_meta(&t1) || self.contains_any_meta(&t2) {
                    UnifyResult::Stuck(t1.clone(), t2.clone())
                } else {
                    // No metas, types are just incompatible
                    UnifyResult::Failed(t1.clone(), t2.clone())
                }
            }
        }
    }

    /// Solve all postponed constraints using fixed-point iteration.
    /// Returns an error immediately if any constraint definitively fails.
    /// Returns an error at the end if constraints remain stuck (unsolvable).
    pub fn solve_constraints(&mut self) -> Result<(), ElabError> {
        let mut progress = true;
        while progress {
            progress = false;
            let mut remaining_constraints = Vec::new();
            let constraints = std::mem::take(&mut self.constraints);

            for constraint in constraints {
                match constraint {
                    Constraint::Unification { t1, t2, span, context } => {
                        let saved_locals = std::mem::replace(&mut self.locals, context.clone());
                        let unify_result = self.unify_core(&t1, &t2);
                        self.locals = saved_locals;

                        match unify_result {
                            UnifyResult::Success => {
                                // Constraint solved! We made progress.
                                progress = true;
                            }
                            UnifyResult::Stuck(t1_stuck, t2_stuck) => {
                                // Still stuck - keep it for another iteration
                                // Use the resolved terms for better error messages
                                remaining_constraints.push(Constraint::Unification {
                                    t1: t1_stuck,
                                    t2: t2_stuck,
                                    span,
                                    context
                                });
                            }
                            UnifyResult::Failed(t1_fail, t2_fail) => {
                                // Definitively failed - report error immediately with span
                                return Err(ElabError::TypeMismatch {
                                    expected: format!("{:?}", t1_fail),
                                    got: format!("{:?}", t2_fail),
                                    span,
                                });
                            }
                        }
                    }
                }
            }
            self.constraints = remaining_constraints;
        }

        // If constraints remain, they are stuck (blocked on unsolved metas)
        if !self.constraints.is_empty() {
            let msg = self.constraints.iter().map(|c| {
                match c {
                    Constraint::Unification { t1, t2, span, .. } => {
                        format!("Cannot unify {:?} with {:?} at line {}:{}",
                            t1, t2, span.line, span.col)
                    }
                }
            }).collect::<Vec<_>>().join("; ");
            return Err(ElabError::UnsolvedConstraints(msg));
        }
        Ok(())
    }

    /// Attempt unification, postponing if stuck. Uses span for error reporting.
    #[allow(dead_code)]
    fn unify_postponed(&mut self, t1: Rc<Term>, t2: Rc<Term>, span: Span) -> Result<(), ElabError> {
        match self.unify_core(&t1, &t2) {
            UnifyResult::Success => Ok(()),
            UnifyResult::Stuck(t1_stuck, t2_stuck) => {
                // Postpone with proper span
                self.constraints.push(Constraint::Unification {
                    t1: t1_stuck,
                    t2: t2_stuck,
                    span,
                    context: self.locals.clone()
                });
                Ok(())
            }
            UnifyResult::Failed(t1_fail, t2_fail) => {
                Err(ElabError::UnificationError(t1_fail, t2_fail))
            }
        }
    }

    fn solve_meta(&mut self, id: usize, term: Rc<Term>, current_ctx_len: usize, meta_ctx_len: usize) -> Result<(), ElabError> {
        if self.contains_meta(&term, id) {
            return Err(ElabError::OccursCheck(id, term));
        }
        let adapted = self.adapt_term_to_ctx(term.clone(), current_ctx_len, meta_ctx_len)?;
        self.meta_solutions.insert(id, adapted);
        Ok(())
    }

    fn adapt_term_to_ctx(&self, term: Rc<Term>, current_len: usize, target_len: usize) -> Result<Rc<Term>, ElabError> {
        if current_len == target_len {
            return Ok(term);
        }
        if current_len > target_len {
            let drop = current_len - target_len;
            self.prune_term(&term, drop, 0)
        } else {
            Ok(term.shift(0, target_len - current_len))
        }
    }

    fn prune_term(&self, term: &Rc<Term>, drop: usize, depth: usize) -> Result<Rc<Term>, ElabError> {
        match &**term {
            Term::Var(idx) => {
                if *idx < depth {
                    Ok(Rc::new(Term::Var(*idx)))
                } else if *idx < depth + drop {
                    Err(ElabError::SolutionContainsFreeVariables(term.clone()))
                } else {
                    Ok(Rc::new(Term::Var(idx - drop)))
                }
            }
            Term::Sort(l) => Ok(Rc::new(Term::Sort(l.clone()))),
            Term::Const(n, ls) => Ok(Rc::new(Term::Const(n.clone(), ls.clone()))),
            Term::App(f, a) => Ok(Rc::new(Term::App(self.prune_term(f, drop, depth)?, self.prune_term(a, drop, depth)?))),
            Term::Lam(ty, body, info) => Ok(Rc::new(Term::Lam(
                self.prune_term(ty, drop, depth)?,
                self.prune_term(body, drop, depth + 1)?,
                *info,
            ))),
            Term::Pi(ty, body, info) => Ok(Rc::new(Term::Pi(
                self.prune_term(ty, drop, depth)?,
                self.prune_term(body, drop, depth + 1)?,
                *info,
            ))),
            Term::LetE(ty, val, body) => Ok(Rc::new(Term::LetE(
                self.prune_term(ty, drop, depth)?,
                self.prune_term(val, drop, depth)?,
                self.prune_term(body, drop, depth + 1)?,
            ))),
            Term::Ind(n, ls) => Ok(Rc::new(Term::Ind(n.clone(), ls.clone()))),
            Term::Ctor(n, idx, ls) => Ok(Rc::new(Term::Ctor(n.clone(), *idx, ls.clone()))),
            Term::Rec(n, ls) => Ok(Rc::new(Term::Rec(n.clone(), ls.clone()))),
            Term::Fix(ty, body) => Ok(Rc::new(Term::Fix(
                self.prune_term(ty, drop, depth)?,
                self.prune_term(body, drop, depth + 1)?,
            ))),
            Term::Meta(id) => Ok(Rc::new(Term::Meta(*id))),
        }
    }

    fn contains_meta(&self, term: &Rc<Term>, meta_id: usize) -> bool {
        match &**term {
            Term::Meta(id) => *id == meta_id,
            Term::App(f, a) => self.contains_meta(f, meta_id) || self.contains_meta(a, meta_id),
            Term::Lam(ty, body, _) | Term::Pi(ty, body, _) | Term::Fix(ty, body) => self.contains_meta(ty, meta_id) || self.contains_meta(body, meta_id),
            Term::LetE(ty, val, body) => self.contains_meta(ty, meta_id) || self.contains_meta(val, meta_id) || self.contains_meta(body, meta_id),
            _ => false,
        }
    }

    fn contains_any_meta(&self, term: &Rc<Term>) -> bool {
        match &**term {
            Term::Meta(_) => true,
            Term::App(f, a) => self.contains_any_meta(f) || self.contains_any_meta(a),
            Term::Lam(ty, body, _) | Term::Pi(ty, body, _) | Term::Fix(ty, body) => self.contains_any_meta(ty) || self.contains_any_meta(body),
            Term::LetE(ty, val, body) => self.contains_any_meta(ty) || self.contains_any_meta(val) || self.contains_any_meta(body),
            _ => false,
        }
    }

    fn resolve_metas_in_ctx(&self, term: &Rc<Term>, ctx_len: usize) -> Rc<Term> {
        match &**term {
            Term::Meta(id) => {
                if let Some(solution) = self.meta_solutions.get(id) {
                    let meta_ctx_len = self.meta_contexts.get(id).map(|c| c.len()).unwrap_or(0);
                    self.adapt_term_to_ctx(solution.clone(), meta_ctx_len, ctx_len)
                        .unwrap_or_else(|_| term.clone())
                } else {
                    term.clone()
                }
            }
            _ => term.clone(),
        }
    }

    pub fn instantiate_metas(&self, term: &Rc<Term>) -> Rc<Term> {
        self.zonk_with_ctx(term, self.locals.len())
    }

    fn zonk_with_ctx(&self, term: &Rc<Term>, ctx_len: usize) -> Rc<Term> {
        match &**term {
            Term::Meta(id) => {
                if let Some(solution) = self.meta_solutions.get(id) {
                    let meta_ctx_len = self.meta_contexts.get(id).map(|c| c.len()).unwrap_or(0);
                    if let Ok(adapted) = self.adapt_term_to_ctx(solution.clone(), meta_ctx_len, ctx_len) {
                        return self.zonk_with_ctx(&adapted, ctx_len);
                    }
                }
                term.clone()
            }
            Term::App(f, a) => Rc::new(Term::App(self.zonk_with_ctx(f, ctx_len), self.zonk_with_ctx(a, ctx_len))),
            Term::Lam(ty, body, i) => Rc::new(Term::Lam(
                self.zonk_with_ctx(ty, ctx_len),
                self.zonk_with_ctx(body, ctx_len + 1),
                *i,
            )),
            Term::Pi(ty, body, i) => Rc::new(Term::Pi(
                self.zonk_with_ctx(ty, ctx_len),
                self.zonk_with_ctx(body, ctx_len + 1),
                *i,
            )),
            Term::LetE(ty, val, body) => Rc::new(Term::LetE(
                self.zonk_with_ctx(ty, ctx_len),
                self.zonk_with_ctx(val, ctx_len),
                self.zonk_with_ctx(body, ctx_len + 1),
            )),
            Term::Ind(n, args) => Rc::new(Term::Ind(n.clone(), args.clone())),
            Term::Ctor(n, i, args) => Rc::new(Term::Ctor(n.clone(), *i, args.clone())),
            Term::Const(n, args) => Rc::new(Term::Const(n.clone(), args.clone())),
            Term::Fix(ty, body) => Rc::new(Term::Fix(
                self.zonk_with_ctx(ty, ctx_len),
                self.zonk_with_ctx(body, ctx_len + 1),
            )),
            Term::Sort(l) => Rc::new(Term::Sort(l.clone())),
            Term::Var(idx) => Rc::new(Term::Var(*idx)),
            Term::Rec(n, ls) => Rc::new(Term::Rec(n.clone(), ls.clone())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn meta_solution_prunes_extra_context() {
        let env = Env::new();
        let mut elab = Elaborator::new(&env);
        let ty = Rc::new(Term::Sort(Level::Zero));

        elab.locals.push(("a".to_string(), ty.clone()));
        let meta_id = elab.meta_counter;
        elab.meta_counter += 1;
        elab.meta_contexts.insert(meta_id, MetaContext { binders: elab.locals.clone() });

        elab.locals.push(("x".to_string(), ty.clone()));

        let meta_ctx_len = elab.meta_contexts.get(&meta_id).unwrap().len();
        let res = elab.solve_meta(meta_id, Rc::new(Term::Var(1)), elab.locals.len(), meta_ctx_len);
        assert!(res.is_ok(), "Expected meta solving to succeed with pruning");

        let solved = elab.meta_solutions.get(&meta_id).expect("Missing meta solution");
        assert!(matches!(&**solved, Term::Var(0)));
    }
}
