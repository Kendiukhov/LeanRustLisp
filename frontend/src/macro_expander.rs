use crate::surface::{Syntax, SyntaxKind, SurfaceTerm, SurfaceTermKind, Span, ScopeId};
use std::collections::{BTreeMap, HashMap};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ExpansionError {
    #[error("Transformation failed: {0}")]
    TransformationError(String),
    #[error("Invalid argument count for '{0}': expected {1}, got {2}")]
    ArgumentCountMismatch(String, usize, usize),
    #[error("Invalid syntax for '{0}': {1}")]
    InvalidSyntax(String, String),
    #[error("Unknown macro or form: {0}")]
    UnknownForm(String),
}

#[derive(Clone)]
pub struct MacroDef {
    pub args: Vec<String>,
    pub body: Syntax,
}

type HygieneEnv = BTreeMap<String, BTreeMap<Vec<ScopeId>, String>>;

pub struct Expander {
    scope_counter: usize,
    gensym_counter: usize,
    pub macros: BTreeMap<String, MacroDef>, // BTreeMap for deterministic iteration
    pub expansion_trace: Vec<(String, Span)>,
    pub verbose: bool,
}

impl Expander {
    pub fn new() -> Self {
        Expander {
            scope_counter: 0,
            gensym_counter: 0,
            macros: BTreeMap::new(),
            expansion_trace: Vec::new(),
            verbose: false,
        }
    }

    /// Create a new unique scope identifier for hygiene tracking.
    pub fn new_scope(&mut self) -> ScopeId {
        let id = self.scope_counter;
        self.scope_counter += 1;
        ScopeId(id)
    }

    fn gensym(&mut self, base_name: &str) -> String {
        let id = self.gensym_counter;
        self.gensym_counter += 1;
        format!("{}_g{}", base_name, id)
    }

    pub fn scopes_compatible(
        reference_scopes: &[ScopeId],
        definition_scopes: &[ScopeId],
    ) -> bool {
        definition_scopes.iter().all(|scope| reference_scopes.contains(scope))
    }

    fn normalize_scopes(scopes: &[ScopeId]) -> Vec<ScopeId> {
        let mut normalized = scopes.to_vec();
        normalized.sort();
        normalized.dedup();
        normalized
    }

    fn insert_binding(env: &mut HygieneEnv, name: String, scopes: Vec<ScopeId>, fresh: String) {
        let entry = env.entry(name).or_insert_with(BTreeMap::new);
        entry.insert(scopes, fresh);
    }

    fn resolve_binding(&self, env: &HygieneEnv, name: &str, reference_scopes: &[ScopeId]) -> Option<String> {
        let defs = env.get(name)?;
        let mut best: Option<(&Vec<ScopeId>, &String)> = None;
        for (def_scopes, def_name) in defs {
            if !reference_scopes.is_empty() && def_scopes.is_empty() {
                continue;
            }
            if !Expander::scopes_compatible(reference_scopes, def_scopes) {
                continue;
            }
            let replace = match best {
                None => true,
                Some((best_scopes, _)) => {
                    def_scopes.len() > best_scopes.len()
                        || (def_scopes.len() == best_scopes.len() && def_scopes > best_scopes)
                }
            };
            if replace {
                best = Some((def_scopes, def_name));
            }
        }
        best.map(|(_, name)| name.clone())
    }

    pub fn add_scope(syntax: &Syntax, scope: ScopeId) -> Syntax {
        let mut new_scopes = syntax.scopes.clone();
        if !new_scopes.contains(&scope) {
            new_scopes.push(scope);
        }
        Syntax {
            scopes: new_scopes,
            ..syntax.clone()
        }
    }

    pub fn remove_scope(syntax: &Syntax, scope: ScopeId) -> Syntax {
        let new_scopes: Vec<_> = syntax.scopes.iter()
            .filter(|s| **s != scope)
            .cloned()
            .collect();
        Syntax {
            scopes: new_scopes,
            ..syntax.clone()
        }
    }

    fn substitute_surface_var(&self, term: SurfaceTerm, name: &str, replacement: &SurfaceTerm) -> SurfaceTerm {
        let span = term.span;
        match term.kind {
            SurfaceTermKind::Var(v) => {
                if v == name {
                    replacement.clone()
                } else {
                    mk_term(SurfaceTermKind::Var(v), span)
                }
            }
            SurfaceTermKind::Sort(l) => mk_term(SurfaceTermKind::Sort(l), span),
            SurfaceTermKind::App(f, x, is_explicit) => {
                let new_f = self.substitute_surface_var(*f, name, replacement);
                let new_x = self.substitute_surface_var(*x, name, replacement);
                mk_term(SurfaceTermKind::App(Box::new(new_f), Box::new(new_x), is_explicit), span)
            }
            SurfaceTermKind::Lam(binder, info, ty, body) => {
                let new_ty = self.substitute_surface_var(*ty, name, replacement);
                if binder == name {
                    mk_term(SurfaceTermKind::Lam(binder, info, Box::new(new_ty), body), span)
                } else {
                    let new_body = self.substitute_surface_var(*body, name, replacement);
                    mk_term(SurfaceTermKind::Lam(binder, info, Box::new(new_ty), Box::new(new_body)), span)
                }
            }
            SurfaceTermKind::Pi(binder, info, ty, body) => {
                let new_ty = self.substitute_surface_var(*ty, name, replacement);
                if binder == name {
                    mk_term(SurfaceTermKind::Pi(binder, info, Box::new(new_ty), body), span)
                } else {
                    let new_body = self.substitute_surface_var(*body, name, replacement);
                    mk_term(SurfaceTermKind::Pi(binder, info, Box::new(new_ty), Box::new(new_body)), span)
                }
            }
            SurfaceTermKind::Let(binder, ty, val, body) => {
                let new_ty = self.substitute_surface_var(*ty, name, replacement);
                let new_val = self.substitute_surface_var(*val, name, replacement);
                if binder == name {
                    mk_term(SurfaceTermKind::Let(binder, Box::new(new_ty), Box::new(new_val), body), span)
                } else {
                    let new_body = self.substitute_surface_var(*body, name, replacement);
                    mk_term(SurfaceTermKind::Let(binder, Box::new(new_ty), Box::new(new_val), Box::new(new_body)), span)
                }
            }
            SurfaceTermKind::Ind(name) => mk_term(SurfaceTermKind::Ind(name), span),
            SurfaceTermKind::Ctor(name, idx) => mk_term(SurfaceTermKind::Ctor(name, idx), span),
            SurfaceTermKind::Rec(name) => mk_term(SurfaceTermKind::Rec(name), span),
            SurfaceTermKind::Fix(binder, ty, body) => {
                let new_ty = self.substitute_surface_var(*ty, name, replacement);
                if binder == name {
                    mk_term(SurfaceTermKind::Fix(binder, Box::new(new_ty), body), span)
                } else {
                    let new_body = self.substitute_surface_var(*body, name, replacement);
                    mk_term(SurfaceTermKind::Fix(binder, Box::new(new_ty), Box::new(new_body)), span)
                }
            }
            SurfaceTermKind::Match(scrutinee, ret_type, cases) => {
                let new_scrutinee = self.substitute_surface_var(*scrutinee, name, replacement);
                let new_ret_type = self.substitute_surface_var(*ret_type, name, replacement);
                let mut new_cases = Vec::new();
                for (ctor_name, bindings, body) in cases {
                    if bindings.iter().any(|b| b == name) {
                        new_cases.push((ctor_name, bindings, body));
                    } else {
                        let new_body = self.substitute_surface_var(body, name, replacement);
                        new_cases.push((ctor_name, bindings, new_body));
                    }
                }
                mk_term(
                    SurfaceTermKind::Match(Box::new(new_scrutinee), Box::new(new_ret_type), new_cases),
                    span,
                )
            }
            SurfaceTermKind::Hole => mk_term(SurfaceTermKind::Hole, span),
        }
    }

    fn get_key(&self, syntax: &Syntax) -> (String, Vec<ScopeId>) {
        let name = if let SyntaxKind::Symbol(s) = &syntax.kind {
            s.clone()
        } else {
            String::new() 
        };
        let scopes = Self::normalize_scopes(&syntax.scopes);
        (name, scopes)
    }

    pub fn expand(&mut self, syntax: Syntax) -> Result<Option<SurfaceTerm>, ExpansionError> {
        if let Some(expanded_syntax) = self.expand_all_macros(syntax)? {
            if self.verbose {
                println!("Expanded: {}", expanded_syntax.pretty_print());
            }
            // Use BTreeMap for deterministic environment mapping
            let term = self.expand_with_env(expanded_syntax, &mut BTreeMap::new())?;
            Ok(Some(term))
        } else {
            Ok(None)
        }
    }

    /// Public method to expand macros only (returns Syntax), useful for tooling (:expand)
    pub fn expand_syntax(&mut self, syntax: Syntax) -> Result<Syntax, ExpansionError> {
        let res = self.expand_all_macros(syntax)?;
        Ok(res.unwrap_or_else(|| {
            // If it expands to nothing (e.g. defmacro), return empty list syntax
            Syntax { kind: SyntaxKind::List(vec![]), span: Span { start: 0, end: 0, line: 0, col: 0 }, scopes: vec![] }
        }))
    }

    pub fn add_macro(&mut self, name: String, args: Vec<String>, body: Syntax) {
        self.macros.insert(name, MacroDef { args, body });
    }

    fn expand_quasiquote(&mut self, syntax: &Syntax) -> Result<Option<Syntax>, ExpansionError> {
        let span = syntax.span;
        let scopes = syntax.scopes.clone();
        match &syntax.kind {
            SyntaxKind::List(list) => {
                if !list.is_empty() {
                    // Check for (unquote e)
                    if let SyntaxKind::Symbol(s) = &list[0].kind {
                        if s == "unquote" {
                            if list.len() != 2 { return Err(ExpansionError::ArgumentCountMismatch("unquote".to_string(), 1, list.len() - 1)); }
                            return self.expand_all_macros(list[1].clone());
                        }
                    }
                }

                let mut tail = Syntax { kind: SyntaxKind::Symbol("nil".to_string()), span, scopes: scopes.clone() };
                
                for item in list.iter().rev() {
                     let splicing = if let SyntaxKind::List(sub) = &item.kind {
                         if !sub.is_empty() {
                             if let SyntaxKind::Symbol(s) = &sub[0].kind {
                                 if s == "unquote-splicing" {
                                      if sub.len() != 2 { return Err(ExpansionError::ArgumentCountMismatch("unquote-splicing".to_string(), 1, sub.len() - 1)); }
                                      Some(sub[1].clone())
                                 } else { None }
                             } else { None }
                         } else { None }
                     } else { None };

                     if let Some(expr) = splicing {
                         let expanded = self.expand_all_macros(expr)?.ok_or(ExpansionError::InvalidSyntax("unquote-splicing".to_string(), "Expression expanded to empty".to_string()))?;
                         tail = Syntax {
                              kind: SyntaxKind::List(vec![
                                  Syntax { kind: SyntaxKind::Symbol("append".to_string()), span, scopes: scopes.clone() },
                                  expanded,
                                  tail
                              ]),
                              span,
                              scopes: scopes.clone()
                         };
                     } else {
                         let head_expanded = self.expand_quasiquote(item)?.ok_or(ExpansionError::InvalidSyntax("quasiquote".to_string(), "Item expansion failed".to_string()))?;
                         tail = Syntax {
                              kind: SyntaxKind::List(vec![
                                  Syntax { kind: SyntaxKind::Symbol("cons".to_string()), span, scopes: scopes.clone() },
                                  head_expanded,
                                  tail
                              ]),
                              span,
                              scopes: scopes.clone()
                         };
                     }
                }
                Ok(Some(tail))
            },
            SyntaxKind::Symbol(_) => {
                Ok(Some(Syntax {
                    kind: SyntaxKind::List(vec![
                         Syntax { kind: SyntaxKind::Symbol("quote".to_string()), span, scopes: scopes.clone() },
                         syntax.clone()
                    ]),
                    span,
                    scopes
                }))
            },
            SyntaxKind::Int(_) | SyntaxKind::String(_) => {
                Ok(Some(syntax.clone()))
            }
            _ => Ok(Some(syntax.clone()))
        }
    }

    pub fn expand_all_macros(&mut self, syntax: Syntax) -> Result<Option<Syntax>, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::List(list) => {
                if list.is_empty() {
                    return Ok(Some(Syntax { kind: SyntaxKind::List(vec![]), ..syntax.clone() }));
                }

                if let SyntaxKind::Symbol(s) = &list[0].kind {

                    if s == "quote" {
                        return Ok(Some(syntax.clone()));
                    }
                    
                    if s == "quasiquote" {
                          if list.len() != 2 { return Err(ExpansionError::ArgumentCountMismatch("quasiquote".to_string(), 1, list.len() - 1)); }
                          return self.expand_quasiquote(&list[1]);
                    }

                    if s == "defmacro" {
                        if list.len() != 4 { return Err(ExpansionError::ArgumentCountMismatch("defmacro".to_string(), 3, list.len() - 1)); }
                        
                        let name = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::InvalidSyntax("defmacro".to_string(), "Name must be a symbol".to_string())); };
                        
                        let mut args = Vec::new();
                        if let SyntaxKind::List(arg_list) = &list[2].kind {
                            for arg in arg_list {
                                if let SyntaxKind::Symbol(a) = &arg.kind {
                                    args.push(a.clone());
                                } else { return Err(ExpansionError::InvalidSyntax("defmacro".to_string(), "Arguments must be symbols".to_string())); }
                            }
                        } else { return Err(ExpansionError::InvalidSyntax("defmacro".to_string(), "Argument list expected".to_string())); }
                        
                        let body = list[3].clone();
                        
                        self.macros.insert(name, MacroDef { args, body });

                        return Ok(None);
                    }

                    if let Some(def) = self.macros.get(s).cloned() {
                        // Push trace
                        self.expansion_trace.push((s.clone(), syntax.span));
                        
                        let args = list[1..].to_vec();
                        let expanded_res = self.substitute_macro_args(&def, &args);
                        
                        if expanded_res.is_err() {
                             // Keep trace on error? Yes.
                             return Err(expanded_res.unwrap_err());
                        }
                        let expanded = expanded_res.unwrap();
                        
                        let res = self.expand_all_macros(expanded);
                        
                        // Pop trace
                        self.expansion_trace.pop();
                        
                        return res;
                    }
                }

                let new_list = list.iter()
                    .map(|item| self.expand_all_macros(item.clone()))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .filter_map(|x| x)
                    .collect();

                Ok(Some(Syntax {
                    kind: SyntaxKind::List(new_list),
                    ..syntax.clone()
                }))
            }
            SyntaxKind::BracedList(list) => {
                let new_list = list.iter()
                    .map(|item| self.expand_all_macros(item.clone()))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .filter_map(|x| x)
                    .collect();

                Ok(Some(Syntax {
                    kind: SyntaxKind::BracedList(new_list),
                    ..syntax.clone()
                }))
            }
            _ => Ok(Some(syntax.clone())),
        }
    }

    fn substitute_macro_args(&mut self, def: &MacroDef, args: &[Syntax]) -> Result<Syntax, ExpansionError> {
        if args.len() != def.args.len() {
            return Err(ExpansionError::ArgumentCountMismatch("macro call".to_string(), def.args.len(), args.len()));
        }

        let macro_scope = self.new_scope();

        let mut subst_env = HashMap::new(); // Use HashMap for local subst, order doesn't matter as we lookup by name
        for (i, arg_name) in def.args.iter().enumerate() {
            subst_env.insert(arg_name.clone(), args[i].clone());
        }

        self.substitute_rec_with_scope(&def.body, &subst_env, macro_scope)
    }

    fn substitute_rec_with_scope(
        &self,
        syntax: &Syntax,
        subst_env: &HashMap<String, Syntax>,
        macro_scope: ScopeId,
    ) -> Result<Syntax, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::Symbol(s) => {
                if let Some(replacement) = subst_env.get(s) {
                    return Ok(replacement.clone());
                }
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

    fn expand_with_env(&mut self, syntax: Syntax, env: &mut HygieneEnv) -> Result<SurfaceTerm, ExpansionError> {
        let span = syntax.span;
        match syntax.kind {
            SyntaxKind::List(list) => {
                if list.is_empty() {
                    return Err(ExpansionError::InvalidSyntax("list".to_string(), "Empty list in expression position".to_string()));
                }
                
                if let SyntaxKind::Symbol(s) = &list[0].kind {
                     match s.as_str() {
                         "lam" => {
                             if list.len() != 4 { return Err(ExpansionError::ArgumentCountMismatch("lam".to_string(), 3, list.len() - 1)); }
                             
                             let (binder_name, binder_info, binder_key) = match &list[1].kind {
                                SyntaxKind::Symbol(s) => (s.clone(), kernel::ast::BinderInfo::Default, self.get_key(&list[1])),
                                SyntaxKind::Hole => ("_".to_string(), kernel::ast::BinderInfo::Default, self.get_key(&list[1])),
                                SyntaxKind::BracedList(l) => {
                                    if l.len() == 1 {
                                        if let SyntaxKind::Symbol(s) = &l[0].kind {
                                            (s.clone(), kernel::ast::BinderInfo::Implicit, self.get_key(&l[0]))
                                        } else { return Err(ExpansionError::InvalidSyntax("lam binder".to_string(), "Expected symbol in brace".to_string())); }
                                    } else { return Err(ExpansionError::InvalidSyntax("lam binder".to_string(), "Expected one element in brace".to_string())); }
                                }
                                _ => return Err(ExpansionError::InvalidSyntax("lam binder".to_string(), "Expected symbol or braced symbol".to_string())),
                             };
                             
                             let fresh_name = self.gensym(&binder_name);
                             
                             let ty = self.expand_with_env(list[2].clone(), env)?;

                             let mut body_env = env.clone();
                             Expander::insert_binding(&mut body_env, binder_key.0, binder_key.1, fresh_name.clone());
                             let body = self.expand_with_env(list[3].clone(), &mut body_env)?;

                             Ok(mk_term(SurfaceTermKind::Lam(fresh_name, binder_info, Box::new(ty), Box::new(body)), span))
                         }
                         "pi" => {
                             let (binder_name, binder_type_syntax, binder_info, binder_key, body_syntax) = if list.len() == 4 {
                                 let (b_name, b_info, b_key) = match &list[1].kind {
                                     SyntaxKind::Symbol(s) => (s.clone(), kernel::ast::BinderInfo::Default, self.get_key(&list[1])),
                                     SyntaxKind::Hole => ("_".to_string(), kernel::ast::BinderInfo::Default, self.get_key(&list[1])),
                                     SyntaxKind::BracedList(l) => {
                                         if l.len() == 1 {
                                             if let SyntaxKind::Symbol(s) = &l[0].kind {
                                                 (s.clone(), kernel::ast::BinderInfo::Implicit, self.get_key(&l[0]))
                                             } else { return Err(ExpansionError::InvalidSyntax("pi binder".to_string(), "Expected symbol in brace".to_string())); }
                                         } else { return Err(ExpansionError::InvalidSyntax("pi binder".to_string(), "Expected one element in brace".to_string())); }
                                     }
                                     _ => return Err(ExpansionError::InvalidSyntax("pi binder".to_string(), "Expected symbol or braced symbol".to_string())),
                                 };
                                 (b_name, list[2].clone(), b_info, b_key, list[3].clone())
                             } else if list.len() == 3 {
                                 let (b_name, b_ty, b_info, b_key) = match &list[1].kind {
                                     SyntaxKind::BracedList(l) => {
                                         if l.len() == 2 {
                                             if let SyntaxKind::Symbol(s) = &l[0].kind {
                                                 (s.clone(), l[1].clone(), kernel::ast::BinderInfo::Implicit, self.get_key(&l[0]))
                                             } else { return Err(ExpansionError::InvalidSyntax("pi binder".to_string(), "Expected {name type}".to_string())); }
                                         } else { return Err(ExpansionError::InvalidSyntax("pi binder".to_string(), "Expected {name type}".to_string())); }
                                     },
                                     SyntaxKind::List(l) => {
                                         if l.len() == 2 {
                                             if let SyntaxKind::Symbol(s) = &l[0].kind {
                                                 (s.clone(), l[1].clone(), kernel::ast::BinderInfo::Default, self.get_key(&l[0]))
                                             } else { return Err(ExpansionError::InvalidSyntax("pi binder".to_string(), "Expected (name type)".to_string())); }
                                         } else { return Err(ExpansionError::InvalidSyntax("pi binder".to_string(), "Expected (name type)".to_string())); }
                                     },
                                     _ => return Err(ExpansionError::InvalidSyntax("pi binder".to_string(), "Expected (name type) or {name type}".to_string())),
                                 };
                                 (b_name, b_ty, b_info, b_key, list[2].clone())
                             } else {
                                 return Err(ExpansionError::ArgumentCountMismatch("pi".to_string(), 3, list.len() - 1));
                             };

                             let fresh_name = self.gensym(&binder_name);
                             
                             let ty = self.expand_with_env(binder_type_syntax, env)?;
                             
                             let mut body_env = env.clone();
                             Expander::insert_binding(&mut body_env, binder_key.0, binder_key.1, fresh_name.clone());
                             let body = self.expand_with_env(body_syntax, &mut body_env)?;

                             Ok(mk_term(SurfaceTermKind::Pi(fresh_name, binder_info, Box::new(ty), Box::new(body)), span))
                         }
                         "let" => {
                             if list.len() != 5 { return Err(ExpansionError::ArgumentCountMismatch("let".to_string(), 4, list.len() - 1)); }
                             let name = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::InvalidSyntax("let".to_string(), "Expected name".to_string())); };
                             let binder_key = self.get_key(&list[1]);
                             
                             let ty = self.expand_with_env(list[2].clone(), env)?;
                             let val = self.expand_with_env(list[3].clone(), env)?;
                             
                             let fresh_name = self.gensym(&name);
                             let mut body_env = env.clone();
                             Expander::insert_binding(&mut body_env, binder_key.0, binder_key.1, fresh_name.clone());
                             
                             let body = self.expand_with_env(list[4].clone(), &mut body_env)?;
                             
                             Ok(mk_term(SurfaceTermKind::Let(fresh_name, Box::new(ty), Box::new(val), Box::new(body)), span))
                         }
                         "app" => {
                               let f = self.expand_with_env(list[1].clone(), env)?;
                               if let SyntaxKind::BracedList(l) = &list[2].kind {
                                   if l.len() == 1 {
                                       let x = self.expand_with_env(l[0].clone(), env)?;
                                       Ok(mk_term(SurfaceTermKind::App(Box::new(f), Box::new(x), false), span))
                                   } else { return Err(ExpansionError::InvalidSyntax("app".to_string(), "Implicit argument must be singleton".to_string())); }
                               } else {
                                   let x = self.expand_with_env(list[2].clone(), env)?;
                                   Ok(mk_term(SurfaceTermKind::App(Box::new(f), Box::new(x), true), span))
                               }
                         }
                         "sort" => {
                             if list.len() != 2 { return Err(ExpansionError::ArgumentCountMismatch("sort".to_string(), 1, list.len() - 1)); }
                             if let SyntaxKind::Int(n) = &list[1].kind {
                                 if *n == 0 {
                                     Ok(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Zero), span))
                                 } else {
                                     Ok(mk_term(SurfaceTermKind::Sort(kernel::ast::Level::Succ(Box::new(kernel::ast::Level::Zero))), span))
                                 }
                             } else {
                                 Err(ExpansionError::InvalidSyntax("sort".to_string(), "Expected integer level".to_string()))
                             }
                         }
                         "ind" => {
                             if list.len() != 2 { return Err(ExpansionError::ArgumentCountMismatch("ind".to_string(), 1, list.len() - 1)); }
                             let n = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::InvalidSyntax("ind".to_string(), "Expected name".to_string())); };
                             Ok(mk_term(SurfaceTermKind::Ind(n), span))
                         }
                         "ctor" => {
                             if list.len() != 3 { return Err(ExpansionError::ArgumentCountMismatch("ctor".to_string(), 2, list.len() - 1)); }
                             let name = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::InvalidSyntax("ctor".to_string(), "Expected name".to_string())); };
                             let idx = if let SyntaxKind::Int(i) = &list[2].kind { *i } else { return Err(ExpansionError::InvalidSyntax("ctor".to_string(), "Expected index".to_string())); };
                             Ok(mk_term(SurfaceTermKind::Ctor(name, idx), span))
                         }
                         "rec" => {
                             if list.len() != 2 { return Err(ExpansionError::ArgumentCountMismatch("rec".to_string(), 1, list.len() - 1)); }
                             let n = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::InvalidSyntax("rec".to_string(), "Expected name".to_string())); };
                             Ok(mk_term(SurfaceTermKind::Rec(n), span))
                         }
                         "fix" => {
                             if list.len() != 4 { return Err(ExpansionError::ArgumentCountMismatch("fix".to_string(), 3, list.len() - 1)); }
                             let name = if let SyntaxKind::Symbol(s) = &list[1].kind { s.clone() } else { return Err(ExpansionError::InvalidSyntax("fix".to_string(), "Expected name".to_string())); };
                             let key = self.get_key(&list[1]);
                             
                             let ty = self.expand_with_env(list[2].clone(), env)?;
                             
                             let fresh_name = self.gensym(&name);
                             let mut body_env = env.clone();
                             Expander::insert_binding(&mut body_env, key.0, key.1, fresh_name.clone());
                             
                             let body = self.expand_with_env(list[3].clone(), &mut body_env)?;
                             
                             Ok(mk_term(SurfaceTermKind::Fix(fresh_name, Box::new(ty), Box::new(body)), span))
                         }
                          "match" => {
                              if list.len() < 3 { return Err(ExpansionError::ArgumentCountMismatch("match".to_string(), 2, list.len() - 1)); }
                              
                              let disc = self.expand_with_env(list[1].clone(), env)?;
                              let ret_ty = self.expand_with_env(list[2].clone(), env)?;
                              
                              let mut cases = Vec::new();
                              for case_syntax in list.iter().skip(3) {
                                  if let SyntaxKind::List(clist) = &case_syntax.kind {
                                      if clist.len() != 3 { return Err(ExpansionError::InvalidSyntax("case".to_string(), "Expected (case pat body)".to_string())); }
                                      if let SyntaxKind::Symbol(s) = &clist[0].kind {
                                          if s != "case" { return Err(ExpansionError::InvalidSyntax("case".to_string(), "Expected 'case'".to_string())); }
                                      } else { return Err(ExpansionError::InvalidSyntax("case".to_string(), "Expected 'case'".to_string())); }
                                      
                                      let mut body_env = env.clone();
                                      let (ctor_name, args) = if let SyntaxKind::List(pat) = &clist[1].kind {
                                          if pat.is_empty() { return Err(ExpansionError::InvalidSyntax("case pattern".to_string(), "Empty pattern".to_string())); }
                                          let c_name = if let SyntaxKind::Symbol(c) = &pat[0].kind { c.clone() } else { return Err(ExpansionError::InvalidSyntax("case pattern".to_string(), "Expected constructor name".to_string())); };
                                          let c_args: Vec<String> = pat.iter().skip(1).map(|p| {
                                              if let SyntaxKind::Symbol(a) = &p.kind { 
                                                  let fresh_name = self.gensym(a);
                                                  let (key_name, key_scopes) = self.get_key(p);
                                                  Expander::insert_binding(&mut body_env, key_name, key_scopes, fresh_name.clone());
                                                  fresh_name
                                              } else { "_".to_string() }
                                          }).collect();
                                          (c_name, c_args)
                                      } else { return Err(ExpansionError::InvalidSyntax("case pattern".to_string(), "Expected list pattern".to_string())); };
                                      
                                      let body = self.expand_with_env(clist[2].clone(), &mut body_env)?;
                                      cases.push((ctor_name, args, body));
                                  } else { return Err(ExpansionError::InvalidSyntax("match".to_string(), "Expected case list".to_string())); }
                              }
                              
                              Ok(mk_term(SurfaceTermKind::Match(Box::new(disc), Box::new(ret_ty), cases), span))
                          }
                          "match_list" => {
                              if list.len() != 6 { return Err(ExpansionError::ArgumentCountMismatch("match_list".to_string(), 5, list.len() - 1)); }
                              
                              let scrut = self.expand_with_env(list[1].clone(), env)?;
                              let param_t = self.expand_with_env(list[2].clone(), env)?;
                              let ret_ty = self.expand_with_env(list[3].clone(), env)?;
                              
                              let case_nil = &list[4];
                              let case_cons = &list[5];
                              
                              let nil_body = if let SyntaxKind::List(nlist) = &case_nil.kind {
                                  if nlist.len() != 3 { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Invalid nil case".to_string())); }
                                  if let SyntaxKind::Symbol(s) = &nlist[0].kind {
                                      if s != "case" { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Expected 'case'".to_string())); }
                                  } else { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Expected 'case'".to_string())); }
                                  
                                  if let SyntaxKind::List(pat) = &nlist[1].kind {
                                      if pat.len() != 2 { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Invalid nil pattern".to_string())); }
                                      if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                          if c != "nil" { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Expected 'nil'".to_string())); }
                                      } else { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Expected 'nil'".to_string())); }
                                      
                                      let (t_key, t_name) = if let SyntaxKind::Symbol(t) = &pat[1].kind {
                                          (Some(self.get_key(&pat[1])), t.clone())
                                      } else {
                                          (None, "_".to_string())
                                      };
                                      let mut body_env = env.clone();
                                      let mut fresh_t_name = None;
                                      if let Some(k) = t_key {
                                          let fresh = self.gensym(&t_name);
                                          Expander::insert_binding(&mut body_env, k.0, k.1, fresh.clone());
                                          fresh_t_name = Some(fresh);
                                      }

                                      let body = self.expand_with_env(nlist[2].clone(), &mut body_env)?;
                                      if let Some(fresh) = fresh_t_name {
                                          self.substitute_surface_var(body, &fresh, &param_t)
                                      } else {
                                          body
                                      }
                                  } else { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Invalid nil pattern".to_string())); }
                              } else { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Invalid nil case".to_string())); };
                              
                              let (cons_bindings, cons_body) = if let SyntaxKind::List(clist) = &case_cons.kind {
                                  if clist.len() != 3 { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Invalid cons case".to_string())); }
                                  if let SyntaxKind::Symbol(s) = &clist[0].kind {
                                      if s != "case" { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Expected 'case'".to_string())); }
                                  } else { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Expected 'case'".to_string())); }
                                  
                                  if let SyntaxKind::List(pat) = &clist[1].kind {
                                      if pat.len() != 5 { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Invalid cons pattern".to_string())); }
                                      if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                           if c != "cons" { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Expected 'cons'".to_string())); }
                                      }
                                      let mut body_env = env.clone();
                                      let mut fresh_t_name = None;
                                      if let SyntaxKind::Symbol(t) = &pat[1].kind {
                                          let fresh = self.gensym(t);
                                          let (key_name, key_scopes) = self.get_key(&pat[1]);
                                          Expander::insert_binding(&mut body_env, key_name, key_scopes, fresh.clone());
                                          fresh_t_name = Some(fresh);
                                      }

                                      let mut bindings = Vec::new();
                                      for p in pat.iter().skip(2) {
                                          if let SyntaxKind::Symbol(v) = &p.kind {
                                              let fresh_name = self.gensym(v);
                                              let (key_name, key_scopes) = self.get_key(p);
                                              Expander::insert_binding(&mut body_env, key_name, key_scopes, fresh_name.clone());
                                              bindings.push(fresh_name);
                                          } else {
                                              bindings.push("_".to_string());
                                          }
                                      }

                                      let body = self.expand_with_env(clist[2].clone(), &mut body_env)?;
                                      let body = if let Some(fresh) = fresh_t_name {
                                          self.substitute_surface_var(body, &fresh, &param_t)
                                      } else {
                                          body
                                      };
                                      (bindings, body)
                                  } else { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Invalid cons pattern".to_string())); }
                              } else { return Err(ExpansionError::InvalidSyntax("match_list".to_string(), "Invalid cons case".to_string())); };
                              
                              let mut cases = Vec::new();
                              cases.push(("nil".to_string(), Vec::new(), nil_body));
                              cases.push(("cons".to_string(), cons_bindings, cons_body));

                              let scrut_name = self.gensym("scrut");
                              let scrut_ty = mk_term(
                                  SurfaceTermKind::App(
                                      Box::new(mk_term(SurfaceTermKind::Ind("List".to_string()), span)),
                                      Box::new(param_t.clone()),
                                      true,
                                  ),
                                  span,
                              );
                              let match_term = mk_term(
                                  SurfaceTermKind::Match(
                                      Box::new(mk_term(SurfaceTermKind::Var(scrut_name.clone()), span)),
                                      Box::new(ret_ty),
                                      cases,
                                  ),
                                  span,
                              );
                              Ok(mk_term(
                                  SurfaceTermKind::Let(scrut_name, Box::new(scrut_ty), Box::new(scrut), Box::new(match_term)),
                                  span,
                              ))
                          }
                         "quote" => {
                             if list.len() != 2 { return Err(ExpansionError::ArgumentCountMismatch("quote".to_string(), 1, list.len() - 1)); }
                             let content = &list[1];
                             Ok(self.quote_syntax(content, span))
                         }
                         _ => {
                             let mut term = self.expand_with_env(list[0].clone(), env)?;
                             for arg in list.iter().skip(1) {
                                 if let SyntaxKind::BracedList(l) = &arg.kind {
                                    if l.len() == 1 {
                                        let arg_term = self.expand_with_env(l[0].clone(), env)?;
                                        term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(arg_term), false), span);
                                    } else { return Err(ExpansionError::InvalidSyntax("application".to_string(), "Implicit arg must be singleton".to_string())); }
                                 } else {
                                     let arg_term = self.expand_with_env(arg.clone(), env)?;
                                     term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(arg_term), true), span);
                                 }
                             }
                             Ok(term)
                         }
                     }
                } else {
                    let mut term = self.expand_with_env(list[0].clone(), env)?;
                    for arg in list.iter().skip(1) {
                        if let SyntaxKind::BracedList(l) = &arg.kind {
                           if l.len() == 1 {
                               let arg_term = self.expand_with_env(l[0].clone(), env)?;
                               term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(arg_term), false), span);
                           } else { return Err(ExpansionError::InvalidSyntax("application".to_string(), "Implicit arg must be singleton".to_string())); }
                        } else {
                            let arg_term = self.expand_with_env(arg.clone(), env)?;
                            term = mk_term(SurfaceTermKind::App(Box::new(term), Box::new(arg_term), true), span);
                        }
                    }
                    Ok(term)
                }
            }
            SyntaxKind::Symbol(ref s) => {
                let (name, ref_scopes) = self.get_key(&syntax);
                if let Some(renamed) = self.resolve_binding(env, &name, &ref_scopes) {
                    Ok(mk_term(SurfaceTermKind::Var(renamed.clone()), span))
                } else {
                    Ok(mk_term(SurfaceTermKind::Var(s.clone()), span))
                }
            },
            SyntaxKind::Hole => Ok(mk_term(SurfaceTermKind::Hole, span)),
            SyntaxKind::Int(n) => {
                 // Desugar Int to Nat constructors
                 let mut t = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 0), span); // Zero
                 let succ = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 1), span); // Succ
                 for _ in 0..n {
                     t = mk_term(SurfaceTermKind::App(Box::new(succ.clone()), Box::new(t), true), span);
                 }
                 Ok(t)
            },
            _ => Err(ExpansionError::UnknownForm(format!("{:?}", syntax.kind))),
        }
    }

    fn quote_syntax(&self, syntax: &Syntax, span: Span) -> SurfaceTerm {
        match &syntax.kind {
            SyntaxKind::List(list) => {
                let nil_tm = mk_term(SurfaceTermKind::Ctor("List".to_string(), 0), span); // nil
                let cons_ctor = mk_term(SurfaceTermKind::Ctor("List".to_string(), 1), span); // cons
                
                let mut term = nil_tm;
                for item in list.iter().rev() {
                    let head = self.quote_syntax(item, span);
                    // cons head tail
                    let app1 = mk_term(SurfaceTermKind::App(Box::new(cons_ctor.clone()), Box::new(head), true), span);
                    term = mk_term(SurfaceTermKind::App(Box::new(app1), Box::new(term), true), span);
                }
                term
            },
            SyntaxKind::Int(n) => {
                let mut t = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 0), span); // Zero
                let succ = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 1), span); // Succ
                for _ in 0..*n {
                    t = mk_term(SurfaceTermKind::App(Box::new(succ.clone()), Box::new(t), true), span);
                }
                t
            },
            _ => mk_term(SurfaceTermKind::Hole, span),
        }
    }
}

fn mk_term(kind: SurfaceTermKind, span: Span) -> SurfaceTerm {
    SurfaceTerm { kind, span }
}
