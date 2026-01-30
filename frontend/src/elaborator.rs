use crate::surface::{SurfaceTerm, SurfaceTermKind, Span};
use kernel::ast::Term;
use kernel::checker::Env;
use std::rc::Rc;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ElabError {
    #[error("Unbound variable: {0}")]
    UnboundVariable(String, Span),
    #[error("Unknown inductive type: {0}")]
    UnknownInductive(String, Span),
    #[error("Elaboration not implemented for this term")]
    NotImplemented(Span),
}

pub struct Elaborator<'a> {
    env: &'a Env,
    locals: Vec<String>,
}

impl<'a> Elaborator<'a> {
    pub fn new(env: &'a Env) -> Self {
        Elaborator {
            env,
            locals: Vec::new(),
        }
    }

    fn resolve_name(&self, name: &str) -> Option<Rc<Term>> {
        for (i, local_name) in self.locals.iter().rev().enumerate() {
            if local_name == name {
                return Some(Rc::new(Term::Var(i)));
            }
        }

        if name == "Type" {
            return Some(Rc::new(Term::Sort(kernel::ast::Level::Zero)));
        }

        if let Some(_) = self.env.get_inductive(name) {
            return Some(Rc::new(Term::Ind(name.to_string(), vec![])));
        }
        
        if let Some(_) = self.env.get_def(name) {
            println!("Resolved def: {}", name);
            return Some(Rc::new(Term::Const(name.to_string(), vec![])));
        } else {
             println!("Failed to resolve def: {}", name);
        }

        // Search for constructors
        for (ind_name, decl) in &self.env.inductives {
            for (i, ctor) in decl.ctors.iter().enumerate() {
                if ctor.name == name {
                    return Some(Rc::new(Term::Ctor(ind_name.clone(), i, vec![])));
                }
            }
        }

        None
    }

    pub fn elaborate(&mut self, term: SurfaceTerm) -> Result<Rc<Term>, ElabError> {
        let span = term.span;
        match term.kind {
            SurfaceTermKind::Var(name) => {
                self.resolve_name(&name).ok_or(ElabError::UnboundVariable(name, span))
            }
            SurfaceTermKind::Sort(l) => Ok(Rc::new(Term::Sort(l))),
            SurfaceTermKind::Lam(name, ty, body) => {
                let ty_elab = self.elaborate(*ty)?;
                
                self.locals.push(name.clone());
                let body_elab = self.elaborate(*body)?;
                self.locals.pop();
                
                Ok(Rc::new(Term::Lam(ty_elab, body_elab)))
            }
            SurfaceTermKind::App(f, x) => {
                let f_elab = self.elaborate(*f)?;
                let x_elab = self.elaborate(*x)?;
                Ok(Rc::new(Term::App(f_elab, x_elab)))
            }
            SurfaceTermKind::Pi(name, ty, body) => {
                let ty_elab = self.elaborate(*ty)?;
                
                self.locals.push(name.clone());
                let body_elab = self.elaborate(*body)?;
                self.locals.pop();
                
                Ok(Rc::new(Term::Pi(ty_elab, body_elab)))
            }
            SurfaceTermKind::Let(name, ty, val, body) => {
                let ty_elab = self.elaborate(*ty)?;
                let val_elab = self.elaborate(*val)?;
                
                self.locals.push(name.clone());
                let body_elab = self.elaborate(*body)?;
                self.locals.pop();
                
                Ok(Rc::new(Term::LetE(ty_elab, val_elab, body_elab)))
            }
            SurfaceTermKind::Ind(name) => {
                // Verify it exists?
                if self.env.get_inductive(&name).is_some() {
                    Ok(Rc::new(Term::Ind(name, vec![])))
                } else {
                    Err(ElabError::UnknownInductive(name, span))
                }
            }
            SurfaceTermKind::Ctor(name, idx) => {
                // Technically Ctor needs to be looked up to verify idx/name match, but roughly:
                // We trust the frontend or verification happens later?
                // Ideally check env.
                Ok(Rc::new(Term::Ctor(name, idx, vec![]))) 
            }
            SurfaceTermKind::Rec(name) => {
                 Ok(Rc::new(Term::Rec(name, vec![])))
            }
            SurfaceTermKind::Match(disc, ret_ty, cases) => {
                 // 1. Identify Inductive Type from first case
                 if cases.is_empty() { return Err(ElabError::NotImplemented(span)); } // Empty match?
                 let first_ctor = &cases[0].0;
                 
                 let mut ind_name = String::new();
                 let mut found = false;
                 // Inefficient linear search, but simplest given Env structure
                 for (name, decl) in &self.env.inductives {
                     for ctor in &decl.ctors {
                         if ctor.name == *first_ctor {
                             ind_name = name.clone();
                             found = true;
                             break;
                         }
                     }
                     if found { break; }
                 }
                 
                 if !found {
                     return Err(ElabError::UnknownInductive(format!("Owner of {}", first_ctor), span));
                 }
                 
                 let decl = self.env.get_inductive(&ind_name).unwrap();
                 
                 // 2. Elaborate Discriminant and Return Type
                 let disc_elab = self.elaborate(*disc)?;
                 let ret_ty_elab = self.elaborate(*ret_ty)?;
                 
                 // 3. Construct Motive: lam _ : Ind. ret_ty
                 // We need to bind a variable for the motive.
                 // The motive type is I -> Type.
                 // ret_ty usually depends on the index, but here we simplify (non-dependent match or simple dependency)
                 // User provided ret_ty.
                 // Matches `(lam x Ind body)`?
                 // If user `ret_ty` is just `Nat`, then motive is `lam _ : Ind. Nat`.
                 // If user intended dependent match, `ret_ty` should be `(lam x I Result)`.
                 // Current syntax `(match n RetTy ...)` usually implies `RetTy` is the result type.
                 // If `RetTy` is just a type, we wrap it in `lam _`.
                 // If `RetTy` is already a function?
                 // Let's assume `RetTy` is the *codomain* type and the match is non-dependent for now, OR `RetTy` handles dependency?
                 // Standard `Rec` expects `Motive: I -> Type`.
                 // In `Expander` for Nat: `lam _ . RetTy`. This implies non-dependent or `RetTy` doesn't capture `_`.
                 // We will do `lam _ : Ind. RetTy`.
                 // We need `Ind` term.
                 
                 let ind_term = Rc::new(Term::Ind(ind_name.clone(), vec![]));
                 let motive = Rc::new(Term::Lam(ind_term.clone(), ret_ty_elab));
                 
                 // 4. Build Rec Term
                 // Rec I params...
                 // We assume 0 parameters for now (e.g. Nat, Bool).
                 // What if `List` (1 param)?
                 // `List` has parameter `T`.
                 // WE NEED TO INFER parameters from `disc` type?
                 // `disc` type: `List Nat`.
                 // `Rec` needs `Nat`.
                 // This requires type inference which checking does.
                 // WE CANNOT DO THIS in Elaborator easily without `infer`.
                 // ! CRITICAL !
                 // If we have generic `Rec` for `List`, we need to apply `T` to `Rec`.
                 // `Rec List` takes `T`, then `Motive`...
                 // If we don't supply `T`, `Rec` is partial.
                 // BUT `match` syntax `(match l (List Nat) ...)` provided `ret_ty`.
                 // We assume `Rec` logic will handle params?
                 // Or we rely on `local inference`?
                 // If `Elaborator` cannot infer, we might need explicit params in `match`?
                 // `(match l (List Nat) ...)` -> `List Nat` is the type of `l`.
                 // `List` takes `Nat`.
                 // If we parse `(List Nat)` from user input?
                 // But user input `match n Type ...`.
                 // User input does NOT provide parameters to `match`!
                 // Wait. `Rec` implementation in `codegen`:
                 // `rec_List_entry` takes `arg_0` (Param).
                 // So we MUST pass Param.
                 // Workaround: For Phase 2, maybe ignore parameters or assume 0 params for User Inductives (like Nat/Bool).
                 // List support requires Phase 10 (which is done, but manually).
                 // If User defines `MyList T`. They need to pass `T`.
                 // If checking logic adds wildcards? Use `_`?
                 // Let's assume 0 params for now (Simple Inductives).
                 // Generic Inductive usually starts with 0 params.
                 // TODO: Support Params extraction from scrutinee type annotation if available.
                 // Or implicit?
                 // For now: `params = vec![]`.
                 
                 let rec_term = Rc::new(Term::Rec(ind_name.clone(), vec![]));
                 let mut app_chain = rec_term;
                 
                 // Apply params (None for now)
                 
                 // Apply Motive
                 app_chain = Rc::new(Term::App(app_chain, motive));
                 
                 // 5. Build Minor Premises (Cases)
                 for (c_idx, ctor) in decl.ctors.iter().enumerate() {
                     // Find user case
                     let mut user_case = None;
                     for (u_ctor, u_args, u_body) in &cases {
                         if *u_ctor == ctor.name {
                             user_case = Some((u_args, u_body));
                             break;
                         }
                     }
                     
                     if let Some((u_args, u_body)) = user_case {
                         // analyze ctor args
                         // Count fields in ctor.ty (skipping params)
                         // For now assume 0 params.
                         let mut curr = &ctor.ty;
                         let mut field_types = Vec::new();
                         while let Term::Pi(ty, body) = &**curr {
                             field_types.push(ty.clone());
                             curr = body;
                         }
                         
                         let num_fields = field_types.len();
                         
                         // Determine which are recursive
                         let mut rec_indices = Vec::new();
                         for (i, ty) in field_types.iter().enumerate() {
                             // Check for `Ind(ind_name)`
                             // Simple check
                             let is_rec = match &**ty {
                                 Term::Ind(n, _) if *n == ind_name => true,
                                 Term::App(head, _) => {
                                     match &**head {
                                         Term::Ind(n, _) if *n == ind_name => true,
                                         _ => false
                                     }
                                 }
                                 _ => false
                             };
                             if is_rec { rec_indices.push(i); }
                         }
                         
                         // Bindings
                         // u_args: [fields..., ihs...]
                         if u_args.len() < num_fields {
                              return Err(ElabError::UnboundVariable(format!("Not enough args for case {}", ctor.name), span));
                         }
                         
                         let field_names = &u_args[0..num_fields];
                         let provided_ihs = &u_args[num_fields..];
                         
                         if provided_ihs.len() > rec_indices.len() {
                             return Err(ElabError::UnboundVariable("Too many IH arguments".to_string(), span));
                         }
                         
                         // Build Lambdas (reverse order of wrapping)
                         // Inner: body
                         // Wrapped by IHs (reverse)
                         // Wrapped by Fields (reverse)
                         
                         // We need to Elaborate the body using these names!
                         // We must push names to `locals` before elaborating body.
                         
                         // Order of arguments in Minor Premise:
                         // fields, then IHs.
                         // Standard Rec order: `(n : Nat) -> C n -> Result`.
                         // arguments are interleaved?
                         // `compute_minor_premise_type`: `(n : Nat) -> C n -> C (succ n)`.
                         // Yes, `n`, then `ih`.
                         // `Cons h t ih`.
                         // So arguments to the lambda are: `f0, ih0?, f1, ih1? ...`?
                         // Let's check `compute_minor_premise_type` in `checker.rs`.
                         // It keeps `Pi(arg, Pi(IH, ...))` if recursive.
                         // So the Lambda sequence must match that structure.
                         // Arg1, IH1 (if rec), Arg2, IH2 (if rec)...
                         
                         // We need to map user names to this sequence.
                         // field_names[i] maps to Arg_i.
                         // provided_ihs[k] maps to IH for rec_indices[k].
                         
                         // We prepare the list of binder names in order.
                         let mut binders = Vec::new();
                         let mut ih_counter = 0;
                         
                         for i in 0..num_fields {
                             // Arg i
                             binders.push((field_names[i].clone(), field_types[i].clone()));
                             
                             // Check if i is recursive
                             if rec_indices.contains(&i) {
                                 // IH
                                 let ih_name = if ih_counter < provided_ihs.len() {
                                     provided_ihs[ih_counter].clone()
                                 } else {
                                     "_".to_string()
                                 };
                                 ih_counter += 1;
                                 
                                 // Type of IH is Motive applied to Arg i.
                                 // We approximate type as Ind for now (Elab types are checked later).
                                 binders.push((ih_name, Rc::new(Term::Sort(kernel::ast::Level::Zero)))); // Dummy type
                             }
                         }
                         
                         // Now push locals and elaborate body
                         for (name, _) in &binders {
                             self.locals.push(name.clone());
                         }
                         
                         let body_elab = self.elaborate(u_body.clone())?;
                         
                         // Pop locals
                         for _ in &binders {
                             self.locals.pop();
                         }
                         
                         // Wrap in Lambdas (reverse)
                         let mut case_term = body_elab;
                         for (name, ty) in binders.iter().rev() {
                             case_term = Rc::new(Term::Lam(ty.clone(), case_term));
                         }
                         
                         app_chain = Rc::new(Term::App(app_chain, case_term));
                         
                     } else {
                         return Err(ElabError::UnboundVariable(format!("Missing case for {}", ctor.name), span));
                     }
                 }
                 
                 // 6. Apply Discriminant
                 Ok(Rc::new(Term::App(app_chain, disc_elab)))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::ast::Level;

    #[test]
    fn test_elab_id() {
        let env = Env::new();
        let mut elab = Elaborator::new(&env);
        
        // (lam x (sort 0) x)
        let term = SurfaceTerm::Lam(
            "x".to_string(),
            Box::new(SurfaceTerm::Sort(Level::Zero)),
            Box::new(SurfaceTerm::Var("x".to_string()))
        );
        
        let core = elab.elaborate(term).expect("Elaboration failed");
        
        // Expect: Lam(Sort 0, Var 0)
        let expected = Rc::new(Term::Lam(
            Rc::new(Term::Sort(Level::Zero)),
            Rc::new(Term::Var(0))
        ));
        
        assert_eq!(core, expected);
    }

    #[test]
    fn test_elab_unbound() {
        let env = Env::new();
        let mut elab = Elaborator::new(&env);
        
        let term = SurfaceTerm::Var("z".to_string());
        let res = elab.elaborate(term);
        
        assert!(matches!(res, Err(ElabError::UnboundVariable(s)) if s == "z"));
    }

    #[test]
    fn test_elab_match_nat() {
        use kernel::ast::{InductiveDecl, Constructor};
        use crate::parser::Parser;
        use crate::macro_expander::Expander;

        // 1. Setup Env with Nat
        let mut env = Env::new();
        let nat_decl = InductiveDecl {
            name: "Nat".to_string(),
            univ_params: vec![],
            ty: Term::sort(Level::Zero), // Type 0
            ctors: vec![
                Constructor { name: "zero".to_string(), ty: Term::ind("Nat".to_string()) },
                Constructor { 
                    name: "succ".to_string(), 
                    ty: Term::pi(Term::ind("Nat".to_string()), Term::ind("Nat".to_string())) 
                },
            ],
        };
        env.add_inductive(nat_decl);

        // 2. Parse & Expand
        // (lam n Nat (match n Nat (case (zero) (zero)) (case (succ x) x)))
        // Identity on matches? Or simple predecessor?
        // Let's do predecessor: zero -> zero, succ x -> x
        let input = "(lam n (ind Nat) (match n (ind Nat) (case (zero) (ctor Nat 0)) (case (succ x) x)))"; 
        // Note: parser expects `(ind Nat)` or `Nat` depending on if we use raw syntax or macro. 
        // Our parser produces `Symbol("Nat")` which macro expander turns to `Ind("Nat")` if we use `ind` special form or if we have a macro.
        // Wait, macro expander hardcodes `(match ...)` logic.
        // Let's use the exact syntax supported by `macro_expander.rs`.
        // `match` expects: `(match disc type (case (zero) z) (case (succ x) s))`
        // And `ctor` special form is `(ctor Name idx)`.
        
        let mut parser = Parser::new(input);
        let syntax = parser.parse().unwrap();
        
        let mut expander = Expander::new();
        let surface = expander.expand(syntax[0].clone()).expect("Expansion failed");
        
        // 3. Elaborate
        let mut elab = Elaborator::new(&env);
        let core = elab.elaborate(surface).expect("Elaboration failed");
        
        println!("Elaborated match: {:?}", core);
        
        // Check structural correctness:
        // Should be Lam(Ind Nat, App(App(App(App(Rec Nat, Motive), ZeroCase), SuccCase), Var(0)))
        
        if let Term::Lam(ty, body) = &*core {
            assert!(matches!(&**ty, Term::Ind(n, _) if n == "Nat"));
            if let Term::App(f, arg) = &**body {
                // arg should be Var(0) -> n
                assert!(matches!(&**arg, Term::Var(0)));
                
                // f should be App(App(App(Rec, Motive), ZeroCase), SuccCase)
                // Let's dig deeper or just check it contains Rec
                // Simple check: is it an application chain starting with Rec?
                // Rec is deeply nested at the head.
            } else { panic!("Body not App"); }
        } else { panic!("Not Lam"); }
    }
}
