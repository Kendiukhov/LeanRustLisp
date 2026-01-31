use crate::surface::{SurfaceTerm, SurfaceTermKind, Span};
use kernel::ast::{Term, Level};
use kernel::checker::{Env, Context, infer as infer_type, is_def_eq, TypeError};
use std::rc::Rc;
use std::collections::HashMap;
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
    #[error("Unification failed: {0:?} vs {1:?}")]
    UnificationError(Rc<Term>, Rc<Term>),
    #[error("Occurs check failed: tried to solve {0} with {1:?}")]
    OccursCheck(usize, Rc<Term>),
    #[error("Metavariable solution {0:?} contains free variables")]
    SolutionContainsFreeVariables(Rc<Term>),
    #[error("Unsolved constraints remaining: {0}")]
    UnsolvedConstraints(String),
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

pub struct Elaborator<'a> {
    env: &'a Env,
    locals: Vec<(String, Rc<Term>)>,
    meta_counter: usize,
    meta_solutions: HashMap<usize, Rc<Term>>,
    meta_contexts: HashMap<usize, Vec<(String, Rc<Term>)>>,
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
        
        if let Some(_) = self.env.get_def(name) {
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
                let (mut f_elab, mut f_ty) = self.infer(*f)?;
                let mut f_ty_whnf = kernel::checker::whnf(self.env, f_ty.clone(), kernel::Transparency::All);

                // Insert implicit arguments
                loop {
                    match &*f_ty_whnf {
                        Term::Pi(arg_ty, ret_ty, info) => {
                            match info {
                                kernel::ast::BinderInfo::Implicit | kernel::ast::BinderInfo::StrictImplicit => {
                                    if is_explicit {
                                        // Insert meta
                                        let meta_id = self.meta_counter;
                                        self.meta_counter += 1;
                                        let meta_term = Rc::new(Term::Meta(meta_id));
                                        self.meta_contexts.insert(meta_id, self.locals.clone());
                                        
                                        f_elab = Rc::new(Term::App(f_elab, meta_term.clone()));
                                        f_ty = ret_ty.subst(0, &meta_term);
                                        f_ty_whnf = kernel::checker::whnf(self.env, f_ty.clone(), kernel::Transparency::All);
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
                    let x_elab = self.check(*x, arg_ty)?;
                    let final_ty = ret_ty.subst(0, &x_elab);
                    Ok((Rc::new(Term::App(f_elab, x_elab)), final_ty))
                } else {
                    Err(ElabError::InferenceError(TypeError::ExpectedFunction(f_ty_whnf), span))
                }
            }
            SurfaceTermKind::Pi(name, binder_info, ty, body) => {
                // Infer the domain type and check it's a Sort
                let (ty_elab, ty_ty) = self.infer(*ty)?;
                let ty_ty_whnf = kernel::checker::whnf(self.env, ty_ty, kernel::Transparency::All);
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
                let ty_ty_whnf = kernel::checker::whnf(self.env, ty_ty, kernel::Transparency::All);
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
                let ty_ty_whnf = kernel::checker::whnf(self.env, ty_ty, kernel::Transparency::All);
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
                self.meta_contexts.insert(meta_id, self.locals.clone());

                let type_meta_id = self.meta_counter;
                self.meta_counter += 1;
                let type_meta_term = Rc::new(Term::Meta(type_meta_id));
                self.meta_contexts.insert(type_meta_id, self.locals.clone());

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
                let decl = self.env.get_inductive(&ind_name)
                    .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?;
                let rec_term = Rc::new(Term::Rec(ind_name.clone(), vec![]));
                // Build recursor type: (C : ind -> Sort u) -> minor premises -> (x : ind) -> C x
                let rec_ty = self.build_recursor_type(&ind_name, &decl)?;
                Ok((rec_term, rec_ty))
            }
            SurfaceTermKind::Match(scrutinee, ret_type, cases) => {
                self.elaborate_match(*scrutinee, *ret_type, cases, span)
            }

            _ => Err(ElabError::NotImplemented(span)),
        }
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
                     let ty_ty_whnf = kernel::checker::whnf(self.env, ty_ty, kernel::Transparency::All);
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
                let (elab_term, inferred_type) = self.infer(SurfaceTerm { kind, span })?;
                self.unify_with_span(&inferred_type, expected_type, span)?;
                Ok(elab_term)
            }
        }
    }

    /// Build the type of a recursor for an inductive type
    fn build_recursor_type(&self, ind_name: &str, decl: &kernel::ast::InductiveDecl) -> Result<Rc<Term>, ElabError> {
        // Recursor type: (C : Ind -> Sort u) -> (minor premises) -> (x : Ind) -> C x
        // For simplicity, we return Sort 0 as a placeholder - the kernel will infer the actual type
        let ind_term = Rc::new(Term::Ind(ind_name.to_string(), vec![]));

        // Motive type: Ind -> Sort 0
        let motive_ty = Rc::new(Term::Pi(
            ind_term.clone(),
            Rc::new(Term::Sort(Level::Succ(Box::new(Level::Zero)))),
            kernel::ast::BinderInfo::Default
        ));

        // Build: (C : motive_ty) -> ... -> (x : Ind) -> C x
        // For now, we construct a simplified recursor type
        // The kernel checker will validate the actual type
        let mut result_ty = Rc::new(Term::App(
            Rc::new(Term::Var(decl.ctors.len())), // C
            Rc::new(Term::Var(0))  // x
        ));

        // Wrap with (x : Ind) -> ...
        result_ty = Rc::new(Term::Pi(ind_term.clone(), result_ty, kernel::ast::BinderInfo::Default));

        // Wrap with minor premises for each constructor
        for (i, ctor) in decl.ctors.iter().enumerate().rev() {
            let minor_ty = self.build_minor_premise_type(ind_name, decl, i)?;
            result_ty = Rc::new(Term::Pi(minor_ty, result_ty, kernel::ast::BinderInfo::Default));
        }

        // Wrap with motive: (C : Ind -> Sort) -> ...
        result_ty = Rc::new(Term::Pi(motive_ty, result_ty, kernel::ast::BinderInfo::Default));

        Ok(result_ty)
    }

    /// Build the type of a minor premise for a constructor
    fn build_minor_premise_type(&self, ind_name: &str, decl: &kernel::ast::InductiveDecl, ctor_idx: usize) -> Result<Rc<Term>, ElabError> {
        let ctor = &decl.ctors[ctor_idx];
        // For a constructor like (succ : Nat -> Nat), the minor premise is:
        // (n : Nat) -> C n -> C (succ n)
        // This is simplified - just return the constructor's result type applied to the motive
        // The kernel handles the actual typing
        let ind_term = Rc::new(Term::Ind(ind_name.to_string(), vec![]));
        Ok(ind_term)
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

        // Extract the inductive name from the scrutinee type
        let scrut_ty_whnf = kernel::checker::whnf(self.env, scrut_ty.clone(), kernel::Transparency::All);
        let ind_name = self.extract_inductive_name(&scrut_ty_whnf)
            .ok_or_else(|| ElabError::TypeMismatch {
                expected: "inductive type".to_string(),
                got: format!("{:?}", scrut_ty_whnf),
                span,
            })?;

        // Get the inductive declaration
        let decl = self.env.get_inductive(&ind_name)
            .ok_or_else(|| ElabError::UnknownInductive(ind_name.clone(), span))?
            .clone();

        // Elaborate the return type (motive)
        // The return type should be a function from the inductive to a type
        let (ret_type_elab, _) = self.infer(ret_type)?;

        // Build the motive as a lambda: (λ x : Ind. ret_type)
        let motive = Rc::new(Term::Lam(
            Rc::new(Term::Ind(ind_name.clone(), vec![])),
            ret_type_elab.clone(),
            kernel::ast::BinderInfo::Default
        ));

        // Start building the recursor application: Ind.rec motive
        let rec_term = Rc::new(Term::Rec(ind_name.clone(), vec![]));
        let mut result = Rc::new(Term::App(rec_term, motive.clone()));

        // Elaborate each case and apply as a minor premise
        for (i, ctor) in decl.ctors.iter().enumerate() {
            let case = cases.iter().find(|(name, _, _)| name == &ctor.name);

            match case {
                Some((_, bindings, body)) => {
                    // Build lambda for this case
                    let case_elab = self.elaborate_case(&ind_name, &decl, i, bindings, body, &ret_type_elab, span)?;
                    result = Rc::new(Term::App(result, case_elab));
                }
                None => {
                    // Missing case - this is an error in a proper implementation
                    // For now, we use a hole (metavariable)
                    let meta_id = self.meta_counter;
                    self.meta_counter += 1;
                    let meta = Rc::new(Term::Meta(meta_id));
                    self.meta_contexts.insert(meta_id, self.locals.clone());
                    result = Rc::new(Term::App(result, meta));
                }
            }
        }

        // Apply the scrutinee
        result = Rc::new(Term::App(result, scrut_elab));

        // The result type is the motive applied to the scrutinee
        // But since we've applied everything, we can just use ret_type_elab
        Ok((result, ret_type_elab))
    }

    /// Extract the inductive type name from a type
    fn extract_inductive_name(&self, ty: &Rc<Term>) -> Option<String> {
        match &**ty {
            Term::Ind(name, _) => Some(name.clone()),
            Term::App(f, _) => self.extract_inductive_name(f),
            _ => None,
        }
    }

    /// Elaborate a single case branch
    fn elaborate_case(
        &mut self,
        ind_name: &str,
        decl: &kernel::ast::InductiveDecl,
        ctor_idx: usize,
        bindings: &[String],
        body: &SurfaceTerm,
        ret_type: &Rc<Term>,
        span: Span,
    ) -> Result<Rc<Term>, ElabError> {
        let ctor = &decl.ctors[ctor_idx];

        // Count the constructor arguments (excluding the result type)
        let ctor_arg_count = self.count_pi_args(&ctor.ty);

        // We need to bind the constructor arguments and possibly IH arguments
        // For recursors, each recursive argument gets an IH
        let recursive_arg_indices = self.find_recursive_args(&ctor.ty, ind_name);

        // Total bindings needed = ctor args + IH args (one per recursive arg)
        let total_bindings_needed = ctor_arg_count + recursive_arg_indices.len();

        // Pad or truncate bindings as needed
        let padded_bindings: Vec<String> = if bindings.len() < total_bindings_needed {
            let mut b = bindings.to_vec();
            for i in bindings.len()..total_bindings_needed {
                b.push(format!("_arg{}", i));
            }
            b
        } else {
            bindings[..total_bindings_needed].to_vec()
        };

        // Push constructor argument bindings
        let mut arg_types = self.extract_pi_arg_types(&ctor.ty);
        let mut locals_added = 0;

        for (i, name) in padded_bindings.iter().take(ctor_arg_count).enumerate() {
            let ty = arg_types.get(i).cloned().unwrap_or_else(|| Rc::new(Term::Sort(Level::Zero)));
            self.locals.push((name.clone(), ty));
            locals_added += 1;
        }

        // Push IH bindings for recursive arguments
        // When the return type is constant (like Nat), the IH type is just the return type
        // For dependent matches, this would need the motive applied to the recursive arg
        for (ih_idx, _rec_arg_idx) in recursive_arg_indices.iter().enumerate() {
            let ih_name = padded_bindings.get(ctor_arg_count + ih_idx)
                .cloned()
                .unwrap_or_else(|| format!("_ih{}", ih_idx));
            // For simple (non-dependent) matches, IH type is just the return type
            let ih_ty = ret_type.clone();
            self.locals.push((ih_name, ih_ty));
            locals_added += 1;
        }

        // Elaborate the body
        let (body_elab, _) = self.infer(body.clone())?;

        // Pop the locals we added
        for _ in 0..locals_added {
            self.locals.pop();
        }

        // Wrap body in lambdas for each binding
        let mut result = body_elab;
        for i in (0..locals_added).rev() {
            let ty = if i < ctor_arg_count {
                arg_types.get(i).cloned().unwrap_or_else(|| Rc::new(Term::Sort(Level::Zero)))
            } else {
                // IH type is the return type (for non-dependent matches)
                ret_type.clone()
            };
            result = Rc::new(Term::Lam(ty, result, kernel::ast::BinderInfo::Default));
        }

        Ok(result)
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
        // First check definitional equality
        if is_def_eq(self.env, t1.clone(), t2.clone(), kernel::Transparency::All) {
            return UnifyResult::Success;
        }

        let t1 = self.resolve_metas(t1);
        let t2 = self.resolve_metas(t2);

        match (&*t1, &*t2) {
            // Same metavariable
            (Term::Meta(id1), Term::Meta(id2)) if id1 == id2 => UnifyResult::Success,

            // Metavariable on one side - try to solve it
            (Term::Meta(id), term) | (term, Term::Meta(id)) => {
                let meta_ctx = match self.meta_contexts.get(id) {
                    Some(ctx) => ctx.clone(),
                    None => return UnifyResult::Failed(t1.clone(), t2.clone()),
                };
                match self.solve_meta(*id, Rc::new(term.clone()), &meta_ctx) {
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
                        match self.unify_core(&t1, &t2) {
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

    fn solve_meta(&mut self, id: usize, term: Rc<Term>, ctx: &Vec<(String, Rc<Term>)>) -> Result<(), ElabError> {
        if self.contains_meta(&term, id) {
            return Err(ElabError::OccursCheck(id, term));
        }
        if self.has_free_variables(&term, ctx.len()) {
            return Err(ElabError::SolutionContainsFreeVariables(term));
        }
        self.meta_solutions.insert(id, term);
        Ok(())
    }

    fn has_free_variables(&self, term: &Rc<Term>, cutoff: usize) -> bool {
        match &**term {
            Term::Var(idx) => *idx >= cutoff,
            Term::App(f, a) => self.has_free_variables(f, cutoff) || self.has_free_variables(a, cutoff),
            Term::Lam(ty, body, _) => self.has_free_variables(ty, cutoff) || self.has_free_variables(body, cutoff + 1),
            Term::Pi(ty, body, _) => self.has_free_variables(ty, cutoff) || self.has_free_variables(body, cutoff + 1),
            Term::LetE(ty, val, body) => self.has_free_variables(ty, cutoff) || self.has_free_variables(val, cutoff) || self.has_free_variables(body, cutoff + 1),
            _ => false,
        }
    }

    fn contains_meta(&self, term: &Rc<Term>, meta_id: usize) -> bool {
        match &**term {
            Term::Meta(id) => *id == meta_id,
            Term::App(f, a) => self.contains_meta(f, meta_id) || self.contains_meta(a, meta_id),
            Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => self.contains_meta(ty, meta_id) || self.contains_meta(body, meta_id),
            Term::LetE(ty, val, body) => self.contains_meta(ty, meta_id) || self.contains_meta(val, meta_id) || self.contains_meta(body, meta_id),
            _ => false,
        }
    }

    fn contains_any_meta(&self, term: &Rc<Term>) -> bool {
        match &**term {
            Term::Meta(_) => true,
            Term::App(f, a) => self.contains_any_meta(f) || self.contains_any_meta(a),
            Term::Lam(ty, body, _) | Term::Pi(ty, body, _) => self.contains_any_meta(ty) || self.contains_any_meta(body),
            Term::LetE(ty, val, body) => self.contains_any_meta(ty) || self.contains_any_meta(val) || self.contains_any_meta(body),
            _ => false,
        }
    }

    fn resolve_metas(&self, term: &Rc<Term>) -> Rc<Term> {
        match &**term {
            Term::Meta(id) => {
                if let Some(solution) = self.meta_solutions.get(id) {
                    self.resolve_metas(solution)
                } else {
                    term.clone()
                }
            }
            _ => term.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    // Tests need to be rewritten
}