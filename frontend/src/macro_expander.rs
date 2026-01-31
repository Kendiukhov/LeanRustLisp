use crate::surface::{Syntax, SyntaxKind, SurfaceTerm, SurfaceTermKind, Span};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ExpansionError {
    #[error("Transformation failed")]
    TransformationError,
}

#[derive(Clone)]
pub struct MacroDef {
    pub args: Vec<String>,
    pub body: Syntax,
}

pub struct Expander {
    scope_counter: usize,
    gensym_counter: usize,
    pub macros: HashMap<String, MacroDef>,
}

impl Expander {
    pub fn new() -> Self {
        Expander {
            scope_counter: 0,
            gensym_counter: 0,
            macros: HashMap::new(),
        }
    }

    /// Create a new unique scope identifier for hygiene tracking.
    /// Each macro invocation gets a fresh scope to distinguish
    /// macro-introduced bindings from user bindings.
    pub fn new_scope(&mut self) -> crate::surface::ScopeId {
        let id = self.scope_counter;
        self.scope_counter += 1;
        crate::surface::ScopeId(id)
    }

    /// Generate a fresh name for hygienic renaming.
    /// Used when a macro introduces a binding that shouldn't
    /// capture names from the macro use site.
    fn gensym(&mut self, base_name: &str) -> String {
        let id = self.gensym_counter;
        self.gensym_counter += 1;
        format!("{}_g{}", base_name, id)
    }

    /// Check if two syntax objects have compatible scopes for binding.
    /// A reference can bind to a definition if:
    /// 1. They have the same name, AND
    /// 2. The reference's scopes are a superset of the definition's scopes
    ///
    /// This implements the key hygiene invariant: macro-introduced names
    /// (which have the macro scope) won't accidentally bind user names
    /// (which lack the macro scope).
    pub fn scopes_compatible(
        reference_scopes: &[crate::surface::ScopeId],
        definition_scopes: &[crate::surface::ScopeId],
    ) -> bool {
        // All definition scopes must be present in the reference
        definition_scopes.iter().all(|scope| reference_scopes.contains(scope))
    }

    /// Add a scope to a syntax object (used for explicit scope manipulation)
    pub fn add_scope(syntax: &Syntax, scope: crate::surface::ScopeId) -> Syntax {
        let mut new_scopes = syntax.scopes.clone();
        if !new_scopes.contains(&scope) {
            new_scopes.push(scope);
        }
        Syntax {
            scopes: new_scopes,
            ..syntax.clone()
        }
    }

    /// Remove a scope from a syntax object (for datum->syntax like operations)
    pub fn remove_scope(syntax: &Syntax, scope: crate::surface::ScopeId) -> Syntax {
        let new_scopes: Vec<_> = syntax.scopes.iter()
            .filter(|s| **s != scope)
            .cloned()
            .collect();
        Syntax {
            scopes: new_scopes,
            ..syntax.clone()
        }
    }

    pub fn expand(&mut self, syntax: Syntax) -> Result<Option<SurfaceTerm>, ExpansionError> {
        if let Some(expanded_syntax) = self.expand_all_macros(syntax)? {
            let term = self.expand_with_env(expanded_syntax, &mut HashMap::new(), false)?;
            Ok(Some(term))
        } else {
            Ok(None)
        }
    }

    pub fn expand_all_macros(&mut self, syntax: Syntax) -> Result<Option<Syntax>, ExpansionError> {
        match syntax.kind {
            SyntaxKind::List(list) => {
                if list.is_empty() {
                    return Ok(Some(Syntax { kind: SyntaxKind::List(vec![]), ..syntax }));
                }

                if let SyntaxKind::Symbol(s) = &list[0].kind {
                    if s == "defmacro" {
                        if list.len() != 4 { return Err(ExpansionError::TransformationError); }
                        
                        let name = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::TransformationError) };
                        
                        let mut args = Vec::new();
                        if let SyntaxKind::List(arg_list) = &list[2].kind {
                            for arg in arg_list {
                                if let SyntaxKind::Symbol(a) = &arg.kind {
                                    args.push(a.clone());
                                } else { return Err(ExpansionError::TransformationError); }
                            }
                        } else { return Err(ExpansionError::TransformationError); }
                        
                        let body = list[3].clone();
                        
                        self.macros.insert(name, MacroDef { args, body });

                        return Ok(None);
                    }

                    if let Some(def) = self.macros.get(s).cloned() {
                        let args = list[1..].to_vec();
                        let expanded = self.substitute_macro_args(&def, &args)?;
                        return self.expand_all_macros(expanded);
                    }
                }

                let new_list = list.into_iter()
                    .map(|item| self.expand_all_macros(item))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .filter_map(|x| x)
                    .collect();

                Ok(Some(Syntax {
                    kind: SyntaxKind::List(new_list),
                    ..syntax
                }))
            }
            SyntaxKind::BracedList(list) => {
                let new_list = list.into_iter()
                    .map(|item| self.expand_all_macros(item))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .filter_map(|x| x)
                    .collect();

                Ok(Some(Syntax {
                    kind: SyntaxKind::BracedList(new_list),
                    ..syntax
                }))
            }
            _ => Ok(Some(syntax)),
        }
    }

    fn substitute_macro_args(&mut self, def: &MacroDef, args: &[Syntax]) -> Result<Syntax, ExpansionError> {
        if args.len() != def.args.len() {
            return Err(ExpansionError::TransformationError);
        }

        // Generate a fresh scope for this macro invocation (hygiene)
        let macro_scope = self.new_scope();

        let mut subst_env = HashMap::new();
        for (i, arg_name) in def.args.iter().enumerate() {
            subst_env.insert(arg_name.clone(), args[i].clone());
        }

        // Add the macro scope to all syntax introduced by the macro body
        self.substitute_rec_with_scope(&def.body, &subst_env, macro_scope)
    }

    /// Substitute macro arguments and add scope to macro-introduced syntax.
    /// This implements Scheme-style hygiene: syntax from the macro body gets
    /// a fresh scope, while syntax from arguments keeps its original scopes.
    fn substitute_rec_with_scope(
        &self,
        syntax: &Syntax,
        subst_env: &HashMap<String, Syntax>,
        macro_scope: crate::surface::ScopeId,
    ) -> Result<Syntax, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::Symbol(s) => {
                if let Some(replacement) = subst_env.get(s) {
                    // Argument: keep original scopes (no macro scope added)
                    return Ok(replacement.clone());
                }
                // Macro-introduced symbol: add the macro scope
                let mut new_scopes = syntax.scopes.clone();
                if !new_scopes.contains(&macro_scope) {
                    new_scopes.push(macro_scope);
                }
                Ok(Syntax {
                    kind: SyntaxKind::Symbol(s.clone()),
                    span: syntax.span,
                    scopes: new_scopes,
                })
            }
            SyntaxKind::List(list) => {
                let new_list = list.iter()
                    .map(|item| self.substitute_rec_with_scope(item, subst_env, macro_scope))
                    .collect::<Result<Vec<_>, _>>()?;

                // List structure also gets the macro scope
                let mut new_scopes = syntax.scopes.clone();
                if !new_scopes.contains(&macro_scope) {
                    new_scopes.push(macro_scope);
                }
                Ok(Syntax {
                    kind: SyntaxKind::List(new_list),
                    span: syntax.span,
                    scopes: new_scopes,
                })
            }
            SyntaxKind::BracedList(list) => {
                let new_list = list.iter()
                    .map(|item| self.substitute_rec_with_scope(item, subst_env, macro_scope))
                    .collect::<Result<Vec<_>, _>>()?;

                let mut new_scopes = syntax.scopes.clone();
                if !new_scopes.contains(&macro_scope) {
                    new_scopes.push(macro_scope);
                }
                Ok(Syntax {
                    kind: SyntaxKind::BracedList(new_list),
                    span: syntax.span,
                    scopes: new_scopes,
                })
            }
            _ => {
                // Other syntax (strings, ints, holes) get the macro scope
                let mut new_scopes = syntax.scopes.clone();
                if !new_scopes.contains(&macro_scope) {
                    new_scopes.push(macro_scope);
                }
                Ok(Syntax {
                    scopes: new_scopes,
                    ..syntax.clone()
                })
            }
        }
    }

    /// Legacy substitute without scope tracking (for internal use)
    fn substitute_rec(&self, syntax: &Syntax, subst_env: &HashMap<String, Syntax>) -> Result<Syntax, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::Symbol(s) => {
                if let Some(replacement) = subst_env.get(s) {
                    return Ok(replacement.clone());
                }
                Ok(syntax.clone())
            }
            SyntaxKind::List(list) => {
                let new_list = list.iter()
                    .map(|item| self.substitute_rec(item, subst_env))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Syntax {
                    kind: SyntaxKind::List(new_list),
                    ..syntax.clone()
                })
            }
            SyntaxKind::BracedList(list) => {
                let new_list = list.iter()
                    .map(|item| self.substitute_rec(item, subst_env))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Syntax {
                    kind: SyntaxKind::BracedList(new_list),
                    ..syntax.clone()
                })
            }
            _ => Ok(syntax.clone()),
        }
    }

    fn expand_with_env(&mut self, syntax: Syntax, env: &mut HashMap<String, String>, in_macro: bool) -> Result<SurfaceTerm, ExpansionError> {
        let span = syntax.span;
        match syntax.kind {
            SyntaxKind::List(list) => {
                if list.is_empty() {
                    // This should not happen if called from `expand`
                    return Err(ExpansionError::TransformationError);
                }
                
                if let SyntaxKind::Symbol(s) = &list[0].kind {
                     match s.as_str() {
                         "lam" => {
                             if list.len() != 4 { return Err(ExpansionError::TransformationError); }
                             
                             let (binder_name, binder_info) = match &list[1].kind {
                                SyntaxKind::Symbol(s) => (s.clone(), kernel::ast::BinderInfo::Default),
                                SyntaxKind::BracedList(l) => {
                                    if l.len() == 1 {
                                        if let SyntaxKind::Symbol(s) = &l[0].kind {
                                            (s.clone(), kernel::ast::BinderInfo::Implicit)
                                        } else { return Err(ExpansionError::TransformationError); }
                                    } else { return Err(ExpansionError::TransformationError); }
                                }
                                _ => return Err(ExpansionError::TransformationError),
                             };
                             
                             let fresh_name = if in_macro { self.gensym(&binder_name) } else { binder_name.clone() };
                             
                             let ty = self.expand_with_env(list[2].clone(), env, in_macro)?;

                             let mut body_env = env.clone();
                             body_env.insert(binder_name, fresh_name.clone());
                             let body = self.expand_with_env(list[3].clone(), &mut body_env, in_macro)?;

                             Ok(mk_term(SurfaceTermKind::Lam(fresh_name, binder_info, Box::new(ty), Box::new(body)), span))
                         }
                         "pi" => {
                             if list.len() != 4 { return Err(ExpansionError::TransformationError); }

                             let (binder_name, binder_info) = match &list[1].kind {
                                SyntaxKind::Symbol(s) => (s.clone(), kernel::ast::BinderInfo::Default),
                                SyntaxKind::BracedList(l) => {
                                    if l.len() == 1 {
                                        if let SyntaxKind::Symbol(s) = &l[0].kind {
                                            (s.clone(), kernel::ast::BinderInfo::Implicit)
                                        } else { return Err(ExpansionError::TransformationError); }
                                    } else { return Err(ExpansionError::TransformationError); }
                                }
                                _ => return Err(ExpansionError::TransformationError),
                             };

                             let fresh_name = if in_macro { self.gensym(&binder_name) } else { binder_name.clone() };
                             
                             let ty = self.expand_with_env(list[2].clone(), env, in_macro)?;
                             
                             let mut body_env = env.clone();
                             body_env.insert(binder_name, fresh_name.clone());
                             let body = self.expand_with_env(list[3].clone(), &mut body_env, in_macro)?;

                             Ok(mk_term(SurfaceTermKind::Pi(fresh_name, binder_info, Box::new(ty), Box::new(body)), span))
                         }
                         "app" => {
                               let f = self.expand_with_env(list[1].clone(), env, in_macro)?;
                               // Explicit 'app' form usually implies explicit application, but let's check if the arg is braced?
                               // Actually if user wrote (app f {x}), that's technically valid S-expr, so we check.
                               if let SyntaxKind::BracedList(l) = &list[2].kind {
                                   if l.len() == 1 {
                                       let x = self.expand_with_env(l[0].clone(), env, in_macro)?;
                                       Ok(mk_term(SurfaceTermKind::App(Box::new(f), Box::new(x), false), span))
                                   } else { return Err(ExpansionError::TransformationError); }
                               } else {
                                   let x = self.expand_with_env(list[2].clone(), env, in_macro)?;
                                   Ok(mk_term(SurfaceTermKind::App(Box::new(f), Box::new(x), true), span))
                               }
                         }
                         "sort" => {
                             if list.len() != 2 { return Err(ExpansionError::TransformationError); }
                             if let SyntaxKind::Int(n) = &list[1].kind {
                                 if *n == 0 {
                                     Ok(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Zero), span))
                                 } else {
                                     Ok(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Succ(Box::new(kernel::ast::Level::Zero))), span))
                                 }
                             } else {
                                 Err(ExpansionError::TransformationError)
                             }
                         }
                         "ind" => {
                             if list.len() != 2 { return Err(ExpansionError::TransformationError); }
                             let n = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::TransformationError) };
                             Ok(mk_term(SurfaceTermKind::Ind(n), span))
                         }
                         "ctor" => {
                             if list.len() != 3 { return Err(ExpansionError::TransformationError); }
                             let name = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::TransformationError) };
                             let idx = if let SyntaxKind::Int(i) = &list[2].kind { *i } else { return Err(ExpansionError::TransformationError) };
                             Ok(mk_term(SurfaceTermKind::Ctor(name, idx), span))
                         }
                         "rec" => {
                             if list.len() != 2 { return Err(ExpansionError::TransformationError); }
                             let n = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::TransformationError) };
                             Ok(mk_term(SurfaceTermKind::Rec(n), span))
                         }
                          "match" => {
                              if list.len() < 3 { return Err(ExpansionError::TransformationError); }
                              
                              let disc = self.expand_with_env(list[1].clone(), env, in_macro)?;
                              let ret_ty = self.expand_with_env(list[2].clone(), env, in_macro)?;
                              
                              let mut cases = Vec::new();
                              for case_syntax in list.iter().skip(3) {
                                  if let SyntaxKind::List(clist) = &case_syntax.kind {
                                      if clist.len() != 3 { return Err(ExpansionError::TransformationError); }
                                      if let SyntaxKind::Symbol(s) = &clist[0].kind {
                                          if s != "case" { return Err(ExpansionError::TransformationError); }
                                      } else { return Err(ExpansionError::TransformationError); }
                                      
                                      let mut body_env = env.clone();
                                      let (ctor_name, args) = if let SyntaxKind::List(pat) = &clist[1].kind {
                                          if pat.is_empty() { return Err(ExpansionError::TransformationError); }
                                          let c_name = if let SyntaxKind::Symbol(c) = &pat[0].kind { c.clone() } else { return Err(ExpansionError::TransformationError); };
                                          let c_args: Vec<String> = pat.iter().skip(1).map(|p| {
                                              if let SyntaxKind::Symbol(a) = &p.kind { 
                                                  let fresh_name = if in_macro { self.gensym(a) } else { a.clone() };
                                                  body_env.insert(a.clone(), fresh_name.clone());
                                                  fresh_name
                                              } else { "_".to_string() }
                                          }).collect();
                                          (c_name, c_args)
                                      } else { return Err(ExpansionError::TransformationError); };
                                      
                                      let body = self.expand_with_env(clist[2].clone(), &mut body_env, in_macro)?;
                                      cases.push((ctor_name, args, body));
                                  } else { return Err(ExpansionError::TransformationError); }
                              }
                              
                              Ok(mk_term(SurfaceTermKind::Match(Box::new(disc), Box::new(ret_ty), cases), span))
                          }
                          "match_list" => {
                              if list.len() != 6 { return Err(ExpansionError::TransformationError); }
                              
                              let scrut = self.expand_with_env(list[1].clone(), env, in_macro)?;
                              let param_t = self.expand_with_env(list[2].clone(), env, in_macro)?;
                              let ret_ty = self.expand_with_env(list[3].clone(), env, in_macro)?;
                              
                              let case_nil = &list[4];
                              let case_cons = &list[5];
                              
                              let nil_body_lam = if let SyntaxKind::List(nlist) = &case_nil.kind {
                                  if nlist.len() != 3 { return Err(ExpansionError::TransformationError); }
                                  if let SyntaxKind::Symbol(s) = &nlist[0].kind {
                                      if s != "case" { return Err(ExpansionError::TransformationError); }
                                  } else { return Err(ExpansionError::TransformationError); }
                                  
                                  if let SyntaxKind::List(pat) = &nlist[1].kind {
                                      if pat.len() != 2 { return Err(ExpansionError::TransformationError); }
                                      if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                          if c != "nil" { return Err(ExpansionError::TransformationError); }
                                      } else { return Err(ExpansionError::TransformationError); }
                                      
                                      let t_name = if let SyntaxKind::Symbol(t) = &pat[1].kind { t.clone() } else { "_".to_string() };
                                      let mut body_env = env.clone();
                                      let fresh_t_name = if in_macro { self.gensym(&t_name) } else { t_name.clone() };
                                      body_env.insert(t_name, fresh_t_name.clone());

                                      let body = self.expand_with_env(nlist[2].clone(), &mut body_env, in_macro)?;
                                      
                                      mk_term(SurfaceTermKind::Lam(fresh_t_name, kernel::ast::BinderInfo::Default, Box::new(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Succ(Box::new(kernel::ast::Level::Zero))), span)), Box::new(body)), span)
                                  } else { return Err(ExpansionError::TransformationError); }
                              } else { return Err(ExpansionError::TransformationError); };
                              
                              let cons_val = if let SyntaxKind::List(clist) = &case_cons.kind {
                                  if clist.len() != 3 { return Err(ExpansionError::TransformationError); }
                                  if let SyntaxKind::Symbol(s) = &clist[0].kind {
                                      if s != "case" { return Err(ExpansionError::TransformationError); }
                                  } else { return Err(ExpansionError::TransformationError); }
                                  
                                  if let SyntaxKind::List(pat) = &clist[1].kind {
                                      if pat.len() != 5 { return Err(ExpansionError::TransformationError); }
                                      if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                           if c != "cons" { return Err(ExpansionError::TransformationError); }
                                      }
                                      let mut body_env = env.clone();
                                      let vars: Vec<String> = pat.iter().skip(1).map(|p| {
                                          if let SyntaxKind::Symbol(v) = &p.kind {
                                              let fresh_name = if in_macro { self.gensym(v) } else { v.clone() };
                                              body_env.insert(v.clone(), fresh_name.clone());
                                              fresh_name
                                          } else { "_".to_string() }
                                      }).collect();
                                      
                                      let body = self.expand_with_env(clist[2].clone(), &mut body_env, in_macro)?;
                                      
                                      let mut lam = body;
                                      lam = mk_term(SurfaceTermKind::Lam(vars[3].clone(), kernel::ast::BinderInfo::Default, Box::new(ret_ty.clone()), Box::new(lam)), span);
                                      
                                      let list_t = mk_term(SurfaceTermKind::App(Box::new(mk_term(SurfaceTermKind::Ind("List".to_string()), span)), Box::new(mk_term(SurfaceTermKind::Var(vars[0].clone()), span)), true), span);
                                      lam = mk_term(SurfaceTermKind::Lam(vars[2].clone(), kernel::ast::BinderInfo::Default, Box::new(list_t), Box::new(lam)), span);
                                      
                                      lam = mk_term(SurfaceTermKind::Lam(vars[1].clone(), kernel::ast::BinderInfo::Default, Box::new(mk_term(SurfaceTermKind::Var(vars[0].clone()), span)), Box::new(lam)), span);
                                      
                                      lam = mk_term(SurfaceTermKind::Lam(vars[0].clone(), kernel::ast::BinderInfo::Default, Box::new(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Succ(Box::new(kernel::ast::Level::Zero))), span)), Box::new(lam)), span);
                                      
                                      lam
                                  } else { return Err(ExpansionError::TransformationError); }
                              } else { return Err(ExpansionError::TransformationError); };
                              
                              let list_t_term = mk_term(SurfaceTermKind::App(Box::new(mk_term(SurfaceTermKind::Ind("List".to_string()), span)), Box::new(param_t.clone()), true), span);
                              let motive = mk_term(SurfaceTermKind::Lam("_".to_string(), kernel::ast::BinderInfo::Default, Box::new(list_t_term), Box::new(ret_ty)), span);
                              let rec_const = mk_term(SurfaceTermKind::Rec("List".to_string()), span);
                              
                              let app1 = mk_term(SurfaceTermKind::App(Box::new(rec_const), Box::new(param_t), true), span);
                              let app2 = mk_term(SurfaceTermKind::App(Box::new(app1), Box::new(motive), true), span);
                              let app3 = mk_term(SurfaceTermKind::App(Box::new(app2), Box::new(nil_body_lam), true), span);
                              let app4 = mk_term(SurfaceTermKind::App(Box::new(app3), Box::new(cons_val), true), span);
                              Ok(mk_term(SurfaceTermKind::App(Box::new(app4), Box::new(scrut), true), span))
                          }
                         _ => {
                             let mut term = self.expand_with_env(list[0].clone(), env, in_macro)?;
                             for arg in list.iter().skip(1) {
                                 if let SyntaxKind::BracedList(l) = &arg.kind {
                                    if l.len() == 1 {
                                        let arg_term = self.expand_with_env(l[0].clone(), env, in_macro)?;
                                        term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(arg_term), false), span);
                                    } else { return Err(ExpansionError::TransformationError); }
                                 } else {
                                     let arg_term = self.expand_with_env(arg.clone(), env, in_macro)?;
                                     term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(arg_term), true), span);
                                 }
                             }
                             Ok(term)
                         }
                     }
                } else {
                    let mut term = self.expand_with_env(list[0].clone(), env, in_macro)?;
                    for arg in list.iter().skip(1) {
                        if let SyntaxKind::BracedList(l) = &arg.kind {
                           if l.len() == 1 {
                               let arg_term = self.expand_with_env(l[0].clone(), env, in_macro)?;
                               term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(arg_term), false), span);
                           } else { return Err(ExpansionError::TransformationError); }
                        } else {
                            let arg_term = self.expand_with_env(arg.clone(), env, in_macro)?;
                            term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(arg_term), true), span);
                        }
                    }
                    Ok(term)
                }
            }
            SyntaxKind::Symbol(s) => {
                if let Some(renamed) = env.get(&s) {
                    Ok(mk_term(SurfaceTermKind::Var(renamed.clone()), span))
                } else {
                    Ok(mk_term(SurfaceTermKind::Var(s), span))
                }
            },
            SyntaxKind::Hole => Ok(mk_term(SurfaceTermKind::Hole, span)),
            SyntaxKind::Int(_) => Err(ExpansionError::TransformationError), 
            _ => Err(ExpansionError::TransformationError),
        }
    }
}

fn mk_term(kind: SurfaceTermKind, span: Span) -> SurfaceTerm {
    SurfaceTerm { kind, span }
}
