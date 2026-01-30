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
    macros: HashMap<String, MacroDef>,
}

impl Expander {
    pub fn new() -> Self {
        Expander {
            scope_counter: 0,
            macros: HashMap::new(),
        }
    }

    pub fn new_scope(&mut self) -> crate::surface::ScopeId {
        let id = self.scope_counter;
        self.scope_counter += 1;
        crate::surface::ScopeId(id)
    }

    fn apply_macro(&mut self, def: &MacroDef, args: &[Syntax]) -> Result<Syntax, ExpansionError> {
        if args.len() != def.args.len() {
            return Err(ExpansionError::TransformationError);
        }
        
        let intro_scope = self.new_scope();
        
        // Bind args (without intro_scope)
        let mut env = HashMap::new();
        for (i, arg_name) in def.args.iter().enumerate() {
            env.insert(arg_name.clone(), args[i].clone());
        }
        
        // Tag body with intro_scope
        let mut body = def.body.clone();
        self.tag_syntax(&mut body, intro_scope);
        
        self.eval_syntax(&body, &env)
    }

    fn tag_syntax(&self, syntax: &mut Syntax, scope: crate::surface::ScopeId) {
        syntax.scopes.push(scope);
        if let SyntaxKind::List(list) = &mut syntax.kind {
            for item in list {
                self.tag_syntax(item, scope);
            }
        }
    }

    fn resolve_ident(&self, syntax: &Syntax) -> Result<String, ExpansionError> {
        if let SyntaxKind::Symbol(s) = &syntax.kind {
            if syntax.scopes.is_empty() {
                Ok(s.clone())
            } else {
                // Canonicalize: s + sorted scopes
                let mut scopes = syntax.scopes.clone();
                scopes.sort_by_key(|k| k.0); // Sort by ID
                let suffix: String = scopes.iter().map(|id| format!("_{}", id.0)).collect();
                Ok(format!("{}{}", s, suffix))
            }
        } else {
            Err(ExpansionError::TransformationError)
        }
    }

    fn eval_syntax(&self, syntax: &Syntax, env: &HashMap<String, Syntax>) -> Result<Syntax, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::Symbol(s) => {
                if let Some(val) = env.get(s) {
                    Ok(val.clone())
                } else {
                    Ok(syntax.clone())
                }
            }
            SyntaxKind::List(list) => {
                if list.is_empty() { return Ok(syntax.clone()); }
                
                if let SyntaxKind::Symbol(op) = &list[0].kind {
                    match op.as_str() {
                        "quote" => {
                            if list.len() != 2 { return Err(ExpansionError::TransformationError); }
                            Ok(list[1].clone())
                        }
                        "list" => {
                            let mut new_list = Vec::new();
                            for item in list.iter().skip(1) {
                                new_list.push(self.eval_syntax(item, env)?);
                            }
                            Ok(Syntax {
                                kind: SyntaxKind::List(new_list),
                                span: syntax.span,
                                scopes: syntax.scopes.clone(),
                            })
                        }
                        _ => {
                            Err(ExpansionError::TransformationError)
                        }
                    }
                } else {
                    Err(ExpansionError::TransformationError)
                }
            }
            _ => Ok(syntax.clone()),
        }
    }

    // ... eval_syntax ...
}

fn mk_term(kind: SurfaceTermKind, span: Span) -> SurfaceTerm {
    SurfaceTerm { kind, span }
}

impl Expander {
    pub fn expand(&mut self, syntax: Syntax) -> Result<SurfaceTerm, ExpansionError> {
        let span = syntax.span;
        match syntax.kind {
            SyntaxKind::List(mut list) => {
                if list.is_empty() {
                    return Err(ExpansionError::TransformationError); // Empty list?
                }
                
                // Check head
                if let SyntaxKind::Symbol(s) = &list[0].kind {
                     match s.as_str() {
                         "lam" => {
                             // (lam x type body)
                             if list.len() != 4 {
                                 println!("Lam len error: {}", list.len());
                                 return Err(ExpansionError::TransformationError);
                             }
                             let arg_name = self.resolve_ident(&list[1])?;
                             let ty = self.expand(list[2].clone())?;
                             let body = self.expand(list[3].clone())?;
                             Ok(mk_term(SurfaceTermKind::Lam(arg_name, Box::new(ty), Box::new(body)), span))
                         }
                         "pi" => {
                             // (pi x type body)
                             if list.len() != 4 { return Err(ExpansionError::TransformationError); }
                             let arg_name = self.resolve_ident(&list[1])?;
                             let ty = self.expand(list[2].clone())?;
                             let body = self.expand(list[3].clone())?;
                             Ok(mk_term(SurfaceTermKind::Pi(arg_name, Box::new(ty), Box::new(body)), span))
                         }
                         "app" => {
                               let f = self.expand(list[1].clone())?;
                               let x = self.expand(list[2].clone())?;
                               Ok(mk_term(SurfaceTermKind::App(Box::new(f), Box::new(x)), span))
                         }
                         "sort" => {
                             // (sort n)
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
                             let n = self.resolve_ident(&list[1])?;
                             Ok(mk_term(SurfaceTermKind::Ind(n), span))
                         }
                         "ctor" => {
                             if list.len() != 3 { println!("Ctor len err: {}", list.len()); return Err(ExpansionError::TransformationError); }
                             let name = match self.resolve_ident(&list[1]) {
                                 Ok(n) => n,
                                 Err(e) => { println!("Ctor name resolve err"); return Err(e); }
                             };
                             let idx = if let SyntaxKind::Int(i) = &list[2].kind { *i } else { 
                                 println!("Ctor idx not int"); 
                                 return Err(ExpansionError::TransformationError) 
                             };
                             Ok(mk_term(SurfaceTermKind::Ctor(name, idx), span))
                         }
                         "rec" => {
                             if list.len() != 2 { return Err(ExpansionError::TransformationError); }
                             let n = self.resolve_ident(&list[1])?;
                             Ok(mk_term(SurfaceTermKind::Rec(n), span))
                         }
                          "match" => {
                              if list.len() < 3 { println!("Match len error: {}", list.len()); return Err(ExpansionError::TransformationError); }
                              
                              let disc = self.expand(list[1].clone())?;
                              let ret_ty = self.expand(list[2].clone())?;
                              
                              let mut cases = Vec::new();
                              for case_syntax in list.iter().skip(3) {
                                  // Parse (case (ctor args...) body)
                                  if let SyntaxKind::List(clist) = &case_syntax.kind {
                                      if clist.len() != 3 { return Err(ExpansionError::TransformationError); }
                                      if let SyntaxKind::Symbol(s) = &clist[0].kind {
                                          if s != "case" { return Err(ExpansionError::TransformationError); }
                                      } else { return Err(ExpansionError::TransformationError); }
                                      
                                      // Pattern
                                      let (ctor_name, args) = if let SyntaxKind::List(pat) = &clist[1].kind {
                                          if pat.is_empty() { return Err(ExpansionError::TransformationError); }
                                          let c_name = if let SyntaxKind::Symbol(c) = &pat[0].kind { c.clone() } else { return Err(ExpansionError::TransformationError); };
                                          let c_args: Vec<String> = pat.iter().skip(1).map(|p| {
                                              if let SyntaxKind::Symbol(a) = &p.kind { a.clone() } else { "_".to_string() }
                                          }).collect();
                                          (c_name, c_args)
                                      } else { return Err(ExpansionError::TransformationError); };
                                      
                                      let body = self.expand(clist[2].clone())?;
                                      cases.push((ctor_name, args, body));
                                  } else { return Err(ExpansionError::TransformationError); }
                              }
                              
                              Ok(mk_term(SurfaceTermKind::Match(Box::new(disc), Box::new(ret_ty), cases), span))
                          }
                          "match_list" => {
                              // (match_list scrut T ret_ty case_nil case_cons)
                              if list.len() != 6 { println!("match_list len error"); return Err(ExpansionError::TransformationError); }
                              
                              let scrut = self.expand(list[1].clone())?;
                              let param_t = self.expand(list[2].clone())?;
                              let ret_ty = self.expand(list[3].clone())?;
                              
                              let case_nil = &list[4];
                              let case_cons = &list[5];
                              
                              // Parse nil case
                              // (case (nil T) body)
                              let nil_body_lam = if let SyntaxKind::List(nlist) = &case_nil.kind {
                                  if nlist.len() != 3 { return Err(ExpansionError::TransformationError); }
                                  if let SyntaxKind::Symbol(s) = &nlist[0].kind {
                                      if s != "case" { return Err(ExpansionError::TransformationError); }
                                  } else { return Err(ExpansionError::TransformationError); }
                                  
                                  if let SyntaxKind::List(pat) = &nlist[1].kind {
                                      if pat.len() != 2 { println!("nil pat len err: {}", pat.len()); return Err(ExpansionError::TransformationError); }
                                      if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                          if c != "nil" { return Err(ExpansionError::TransformationError); }
                                      } else { return Err(ExpansionError::TransformationError); }
                                      
                                      let t_name = if let SyntaxKind::Symbol(t) = &pat[1].kind { t.clone() } else { "_".to_string() };
                                      let body = self.expand(nlist[2].clone())?;
                                      
                                      // Wrap: \T. body
                                      mk_term(SurfaceTermKind::Lam(t_name, Box::new(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Succ(Box::new(kernel::ast::Level::Zero))), span)), Box::new(body)), span)
                                  } else { return Err(ExpansionError::TransformationError); }
                              } else { return Err(ExpansionError::TransformationError); };
                              
                              // Parse cons case
                              let cons_val = if let SyntaxKind::List(clist) = &case_cons.kind {
                                  if clist.len() != 3 { return Err(ExpansionError::TransformationError); }
                                  if let SyntaxKind::Symbol(s) = &clist[0].kind {
                                      if s != "case" { return Err(ExpansionError::TransformationError); }
                                  } else { return Err(ExpansionError::TransformationError); }
                                  
                                  if let SyntaxKind::List(pat) = &clist[1].kind {
                                      if pat.len() != 5 { println!("cons pat len err: {}", pat.len()); return Err(ExpansionError::TransformationError); }
                                      if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                           if c != "cons" { return Err(ExpansionError::TransformationError); }
                                      }
                                      // Bindings: T, h, t, ih
                                      let vars: Vec<String> = pat.iter().skip(1).map(|p| {
                                          if let SyntaxKind::Symbol(v) = &p.kind { v.clone() } else { "_".to_string() }
                                      }).collect();
                                      
                                      let body = self.expand(clist[2].clone())?;
                                      
                                      // Construct lambdas: \T. \h. \t. \ih. body
                                      let mut lam = body;
                                      // Wrap ih: Type is ret_ty
                                      lam = mk_term(SurfaceTermKind::Lam(vars[3].clone(), Box::new(ret_ty.clone()), Box::new(lam)), span);
                                      
                                      // Wrap t: Type is (List T) => App(Ind(List), Var(T))
                                      let list_t = mk_term(SurfaceTermKind::App(Box::new(mk_term(SurfaceTermKind::Ind("List".to_string()), span)), Box::new(mk_term(SurfaceTermKind::Var(vars[0].clone()), span))), span);
                                      lam = mk_term(SurfaceTermKind::Lam(vars[2].clone(), Box::new(list_t), Box::new(lam)), span);
                                      
                                      // Wrap h: Type is T => Var(T)
                                      lam = mk_term(SurfaceTermKind::Lam(vars[1].clone(), Box::new(mk_term(SurfaceTermKind::Var(vars[0].clone()), span)), Box::new(lam)), span);
                                      
                                      // Wrap T: Type is Sort(1) (matching prelude)
                                      lam = mk_term(SurfaceTermKind::Lam(vars[0].clone(), Box::new(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Succ(Box::new(kernel::ast::Level::Zero))), span)), Box::new(lam)), span);
                                      
                                      lam
                                  } else { return Err(ExpansionError::TransformationError); }
                              } else { return Err(ExpansionError::TransformationError); };
                              
                              let list_t_term = mk_term(SurfaceTermKind::App(Box::new(mk_term(SurfaceTermKind::Ind("List".to_string()), span)), Box::new(param_t.clone())), span);
                              let motive = mk_term(SurfaceTermKind::Lam("_".to_string(), Box::new(list_t_term), Box::new(ret_ty)), span);
                              let rec_const = mk_term(SurfaceTermKind::Rec("List".to_string()), span);
                              
                              // App sequence: Rec T Motive nil_case cons_case scrut
                              let app1 = mk_term(SurfaceTermKind::App(Box::new(rec_const), Box::new(param_t)), span);
                              let app2 = mk_term(SurfaceTermKind::App(Box::new(app1), Box::new(motive)), span);
                              let app3 = mk_term(SurfaceTermKind::App(Box::new(app2), Box::new(nil_body_lam)), span);
                              let app4 = mk_term(SurfaceTermKind::App(Box::new(app3), Box::new(cons_val)), span);
                              Ok(mk_term(SurfaceTermKind::App(Box::new(app4), Box::new(scrut)), span))
                          }
                         "defmacro" => {
                              // (defmacro name (args) body)
                             if list.len() != 4 { return Err(ExpansionError::TransformationError); }
                             
                             let name = self.resolve_ident(&list[1])?;
                             
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
                             Ok(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Zero), span)) 
                         }
                         _ => {
                             // Check if it is a macro
                             if let Some(def) = self.macros.get(s).cloned() {
                                 // Invoke macro
                                 let args = list[1..].to_vec();
                                 let expanded = self.apply_macro(&def, &args)?;
                                 return self.expand(expanded);
                             }
                             
                             // Application
                             // (f x) -> App
                             if list.len() == 2 {
                                 // Implicit app case
                                 let f = self.expand(list[0].clone())?;
                                 let x = self.expand(list[1].clone())?;
                                 return Ok(mk_term(SurfaceTermKind::App(Box::new(f), Box::new(x)), span));
                             }
                             
                             // (app f x)
                             if s == "app" {
                                  let f = self.expand(list[1].clone())?;
                                  let x = self.expand(list[2].clone())?;
                                  Ok(mk_term(SurfaceTermKind::App(Box::new(f), Box::new(x)), span))
                             } else if s == "sort" {
                                 // ... existing sort logic ...
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
                             } else {
                                // Generic application (f a1 a2...)
                                let mut term = self.expand(list[0].clone())?;
                                for arg in list.iter().skip(1) {
                                    term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(self.expand(arg.clone())?)), span);
                                }
                                Ok(term)
                             }
                         }
                     }
                } else {
                    // Head is not a symbol: Generic Application ((f ...) x ...)
                    let mut term = self.expand(list[0].clone())?;
                    for arg in list.iter().skip(1) {
                        term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(self.expand(arg.clone())?)), span);
                    }
                    Ok(term)
                }
            }
            SyntaxKind::Symbol(_) => {
                let name = self.resolve_ident(&syntax)?;
                Ok(mk_term(SurfaceTermKind::Var(name), span))
            },
            SyntaxKind::Int(_) => Err(ExpansionError::TransformationError), 
            _ => Err(ExpansionError::TransformationError),
        }
    }

    fn parse_case_body(&mut self, syntax: &Syntax, expected_ctor: &str, expected_args_count: usize) -> Result<SurfaceTerm, ExpansionError> {
        if let SyntaxKind::List(list) = &syntax.kind {
            // (case (ctor args...) body)
            if list.len() != 3 { return Err(ExpansionError::TransformationError); }
            
            // Check 'case' keyword
            if let SyntaxKind::Symbol(s) = &list[0].kind {
                if s != "case" { return Err(ExpansionError::TransformationError); }
            } else { return Err(ExpansionError::TransformationError); }
            
            // Check pattern: (ctor args...)
            if let SyntaxKind::List(pat) = &list[1].kind {
                if pat.len() != 1 + expected_args_count { return Err(ExpansionError::TransformationError); }
                if let SyntaxKind::Symbol(c) = &pat[0].kind {
                    if c != expected_ctor { return Err(ExpansionError::TransformationError); }
                } else { return Err(ExpansionError::TransformationError); }
            } else { return Err(ExpansionError::TransformationError); }
            
            // Return body
            self.expand(list[2].clone())
        } else {
            Err(ExpansionError::TransformationError)
        }
    }

    fn parse_case_succ(&mut self, syntax: &Syntax) -> Result<SurfaceTerm, ExpansionError> {
         if let SyntaxKind::List(list) = &syntax.kind {
            // (case (succ n) body)
            if list.len() != 3 { return Err(ExpansionError::TransformationError); }
            
            let span = syntax.span;
             // Check 'case'
            if let SyntaxKind::Symbol(s) = &list[0].kind {
                if s != "case" { return Err(ExpansionError::TransformationError); }
            } else { return Err(ExpansionError::TransformationError); }
            
            let (arg_name, ih_name) = if let SyntaxKind::List(pat) = &list[1].kind {
                if pat.len() < 2 || pat.len() > 3 { println!("Succ pat len err: {}", pat.len()); return Err(ExpansionError::TransformationError); }
                if let SyntaxKind::Symbol(c) = &pat[0].kind {
                    if c != "succ" { println!("Succ ctor err: {}", c); return Err(ExpansionError::TransformationError); }
                } else { println!("Succ head not symbol"); return Err(ExpansionError::TransformationError); }
                
                let n_name = if let SyntaxKind::Symbol(n) = &pat[1].kind {
                    n.clone()
                } else { println!("Succ arg1 not symbol"); return Err(ExpansionError::TransformationError); };

                let ih_name = if pat.len() == 3 {
                    if let SyntaxKind::Symbol(ih) = &pat[2].kind {
                        ih.clone()
                    } else { println!("Succ arg2 not symbol"); return Err(ExpansionError::TransformationError); }
                } else {
                    "_".to_string()
                };
                (n_name, ih_name)
            } else { println!("Succ pat not list"); return Err(ExpansionError::TransformationError); };
            
            // Body
            let body = self.expand(list[2].clone())?;
            // Return lam n. lam ih. body
            // Inner types are placeholders Ind("Nat")
            Ok(mk_term(SurfaceTermKind::Lam(
                arg_name, 
                Box::new(mk_term(SurfaceTermKind::Ind("Nat".to_string()), span)), 
                Box::new(mk_term(SurfaceTermKind::Lam(
                    ih_name,
                    Box::new(mk_term(SurfaceTermKind::Ind("Nat".to_string()), span)), // Type of IH is C n (Nat), approximated
                    Box::new(body)
                ), span))
            ), span))
        } else {
            Err(ExpansionError::TransformationError)
        }
    }
    
    fn peek_case_ctor(&self, syntax: &Syntax) -> Result<String, ExpansionError> {
        if let SyntaxKind::List(list) = &syntax.kind {
            if list.len() < 2 { return Err(ExpansionError::TransformationError); }
            if let SyntaxKind::Symbol(s) = &list[0].kind {
                if s != "case" { return Err(ExpansionError::TransformationError); }
            } else { return Err(ExpansionError::TransformationError); }
            
            if let SyntaxKind::List(pat) = &list[1].kind {
                if pat.is_empty() { return Err(ExpansionError::TransformationError); }
                if let SyntaxKind::Symbol(c) = &pat[0].kind {
                    Ok(c.clone())
                } else {
                    Err(ExpansionError::TransformationError)
                }
            } else {
                Err(ExpansionError::TransformationError)
            }
        } else {
            Err(ExpansionError::TransformationError)
        }
    }
}
