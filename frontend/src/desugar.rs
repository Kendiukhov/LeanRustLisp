use crate::macro_expander::ExpansionError;
use crate::surface::{
    normalize_scopes, ScopeId, Span, SurfaceTerm, SurfaceTermKind, Syntax, SyntaxKind,
};
use kernel::ast::FunctionKind;
use std::collections::BTreeMap;

type HygieneEnv = BTreeMap<String, BTreeMap<Vec<ScopeId>, String>>;

pub struct Desugarer {
    gensym_counter: usize,
}

impl Desugarer {
    pub fn new() -> Self {
        Desugarer { gensym_counter: 0 }
    }

    fn gensym(&mut self, base_name: &str) -> String {
        let id = self.gensym_counter;
        self.gensym_counter += 1;
        format!("{}_g{}", base_name, id)
    }

    fn scopes_compatible(reference_scopes: &[ScopeId], definition_scopes: &[ScopeId]) -> bool {
        let ref_norm = normalize_scopes(reference_scopes);
        let def_norm = normalize_scopes(definition_scopes);

        if def_norm.is_empty() {
            return ref_norm.is_empty();
        }

        // Compatibility is subset-based: a reference can resolve to a binder when
        // the binder scopes are contained in the reference scopes.
        let mut ref_idx = 0usize;
        let mut def_idx = 0usize;
        while ref_idx < ref_norm.len() && def_idx < def_norm.len() {
            if ref_norm[ref_idx] == def_norm[def_idx] {
                ref_idx += 1;
                def_idx += 1;
            } else if ref_norm[ref_idx] < def_norm[def_idx] {
                ref_idx += 1;
            } else {
                return false;
            }
        }
        def_idx == def_norm.len()
    }

    fn insert_binding(env: &mut HygieneEnv, name: String, scopes: Vec<ScopeId>, fresh: String) {
        let entry = env.entry(name).or_insert_with(BTreeMap::new);
        entry.insert(scopes, fresh);
    }

    fn resolve_binding(
        &self,
        env: &HygieneEnv,
        name: &str,
        reference_scopes: &[ScopeId],
    ) -> Option<String> {
        let defs = env.get(name)?;
        let mut best: Option<(&Vec<ScopeId>, &String)> = None;
        for (def_scopes, def_name) in defs {
            if !reference_scopes.is_empty() && def_scopes.is_empty() {
                continue;
            }
            if !Self::scopes_compatible(reference_scopes, def_scopes) {
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

    fn get_key(&self, syntax: &Syntax) -> (String, Vec<ScopeId>) {
        let name = if let SyntaxKind::Symbol(s) = &syntax.kind {
            s.clone()
        } else {
            String::new()
        };
        let scopes = normalize_scopes(&syntax.scopes);
        (name, scopes)
    }

    fn parse_function_kind_token(
        &self,
        syntax: &Syntax,
    ) -> Result<Option<(FunctionKind, bool)>, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::Symbol(s) => match s.as_str() {
                "fn" => Ok(Some((FunctionKind::Fn, false))),
                "fnmut" => Ok(Some((FunctionKind::FnMut, false))),
                "fnonce" => Ok(Some((FunctionKind::FnOnce, false))),
                _ => Ok(None),
            },
            SyntaxKind::Index(base, index) => {
                if let SyntaxKind::Symbol(base_sym) = &base.kind {
                    if base_sym == "#" {
                        match &index.kind {
                            SyntaxKind::Symbol(attr) => match attr.as_str() {
                                "fn" => Ok(Some((FunctionKind::Fn, true))),
                                "mut" => Ok(Some((FunctionKind::FnMut, true))),
                                "once" => Ok(Some((FunctionKind::FnOnce, true))),
                                _ => Err(ExpansionError::InvalidSyntax(
                                    "function kind".to_string(),
                                    "Expected #[fn], #[mut], or #[once]".to_string(),
                                )),
                            },
                            _ => Err(ExpansionError::InvalidSyntax(
                                "function kind".to_string(),
                                "Expected #[fn], #[mut], or #[once]".to_string(),
                            )),
                        }
                    } else {
                        Ok(None)
                    }
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    pub fn desugar(&mut self, syntax: Syntax) -> Result<SurfaceTerm, ExpansionError> {
        self.desugar_with_env(syntax, &mut BTreeMap::new())
    }

    fn substitute_surface_var(
        &self,
        term: SurfaceTerm,
        name: &str,
        replacement: &SurfaceTerm,
    ) -> SurfaceTerm {
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
                mk_term(
                    SurfaceTermKind::App(Box::new(new_f), Box::new(new_x), is_explicit),
                    span,
                )
            }
            SurfaceTermKind::Index(base, index) => {
                let new_base = self.substitute_surface_var(*base, name, replacement);
                let new_index = self.substitute_surface_var(*index, name, replacement);
                mk_term(
                    SurfaceTermKind::Index(Box::new(new_base), Box::new(new_index)),
                    span,
                )
            }
            SurfaceTermKind::Lam(binder, info, kind, ty, body) => {
                let new_ty = self.substitute_surface_var(*ty, name, replacement);
                if binder == name {
                    mk_term(
                        SurfaceTermKind::Lam(binder, info, kind, Box::new(new_ty), body),
                        span,
                    )
                } else {
                    let new_body = self.substitute_surface_var(*body, name, replacement);
                    mk_term(
                        SurfaceTermKind::Lam(
                            binder,
                            info,
                            kind,
                            Box::new(new_ty),
                            Box::new(new_body),
                        ),
                        span,
                    )
                }
            }
            SurfaceTermKind::Pi(binder, info, kind, ty, body) => {
                let new_ty = self.substitute_surface_var(*ty, name, replacement);
                if binder == name {
                    mk_term(
                        SurfaceTermKind::Pi(binder, info, kind, Box::new(new_ty), body),
                        span,
                    )
                } else {
                    let new_body = self.substitute_surface_var(*body, name, replacement);
                    mk_term(
                        SurfaceTermKind::Pi(
                            binder,
                            info,
                            kind,
                            Box::new(new_ty),
                            Box::new(new_body),
                        ),
                        span,
                    )
                }
            }
            SurfaceTermKind::Let(binder, ty, val, body) => {
                let new_ty = self.substitute_surface_var(*ty, name, replacement);
                let new_val = self.substitute_surface_var(*val, name, replacement);
                if binder == name {
                    mk_term(
                        SurfaceTermKind::Let(binder, Box::new(new_ty), Box::new(new_val), body),
                        span,
                    )
                } else {
                    let new_body = self.substitute_surface_var(*body, name, replacement);
                    mk_term(
                        SurfaceTermKind::Let(
                            binder,
                            Box::new(new_ty),
                            Box::new(new_val),
                            Box::new(new_body),
                        ),
                        span,
                    )
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
                    mk_term(
                        SurfaceTermKind::Fix(binder, Box::new(new_ty), Box::new(new_body)),
                        span,
                    )
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
                    SurfaceTermKind::Match(
                        Box::new(new_scrutinee),
                        Box::new(new_ret_type),
                        new_cases,
                    ),
                    span,
                )
            }
            SurfaceTermKind::Eval(code, cap) => {
                let new_code = self.substitute_surface_var(*code, name, replacement);
                let new_cap = self.substitute_surface_var(*cap, name, replacement);
                mk_term(
                    SurfaceTermKind::Eval(Box::new(new_code), Box::new(new_cap)),
                    span,
                )
            }
            SurfaceTermKind::Hole => mk_term(SurfaceTermKind::Hole, span),
        }
    }

    fn desugar_with_env(
        &mut self,
        syntax: Syntax,
        env: &mut HygieneEnv,
    ) -> Result<SurfaceTerm, ExpansionError> {
        let span = syntax.span;
        match syntax.kind {
            SyntaxKind::List(list) => {
                if list.is_empty() {
                    return Err(ExpansionError::InvalidSyntax(
                        "list".to_string(),
                        "Empty list in expression position".to_string(),
                    ));
                }

                if let SyntaxKind::Symbol(s) = &list[0].kind {
                    match s.as_str() {
                        "lam" => {
                            if list.len() != 4 && list.len() != 5 {
                                return Err(ExpansionError::InvalidSyntax(
                                    "lam".to_string(),
                                    "Expected (lam [fn|fnmut|fnonce|#[fn]|#[mut]|#[once]] binder type body)"
                                        .to_string(),
                                ));
                            }

                            let (kind_opt, binder_index) = if list.len() == 5 {
                                match self.parse_function_kind_token(&list[1])? {
                                    Some((kind, _)) => (Some(kind), 2),
                                    None => {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "lam".to_string(),
                                            "Expected function kind (fn/fnmut/fnonce/#[fn]/#[mut]/#[once])"
                                                .to_string(),
                                        ));
                                    }
                                }
                            } else {
                                (None, 1)
                            };

                            let (binder_name, binder_info, binder_key) =
                                match &list[binder_index].kind {
                                    SyntaxKind::Symbol(s) => (
                                        s.clone(),
                                        kernel::ast::BinderInfo::Default,
                                        self.get_key(&list[binder_index]),
                                    ),
                                    SyntaxKind::Hole => (
                                        "_".to_string(),
                                        kernel::ast::BinderInfo::Default,
                                        self.get_key(&list[binder_index]),
                                    ),
                                    SyntaxKind::BracedList(l) => {
                                        if l.len() == 1 {
                                            if let SyntaxKind::Symbol(s) = &l[0].kind {
                                                (
                                                    s.clone(),
                                                    kernel::ast::BinderInfo::Implicit,
                                                    self.get_key(&l[0]),
                                                )
                                            } else {
                                                return Err(ExpansionError::InvalidSyntax(
                                                    "lam binder".to_string(),
                                                    "Expected symbol in brace".to_string(),
                                                ));
                                            }
                                        } else {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "lam binder".to_string(),
                                                "Expected one element in brace".to_string(),
                                            ));
                                        }
                                    }
                                    _ => {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "lam binder".to_string(),
                                            "Expected symbol or braced symbol".to_string(),
                                        ))
                                    }
                                };

                            let fresh_name = self.gensym(&binder_name);

                            let ty = self.desugar_with_env(list[binder_index + 1].clone(), env)?;

                            let mut body_env = env.clone();
                            Self::insert_binding(
                                &mut body_env,
                                binder_key.0,
                                binder_key.1,
                                fresh_name.clone(),
                            );
                            let body = self
                                .desugar_with_env(list[binder_index + 2].clone(), &mut body_env)?;

                            Ok(mk_term(
                                SurfaceTermKind::Lam(
                                    fresh_name,
                                    binder_info,
                                    kind_opt,
                                    Box::new(ty),
                                    Box::new(body),
                                ),
                                span,
                            ))
                        }
                        "pi" => {
                            let parse_pi_from = |start: usize| {
                                let remaining = list.len().saturating_sub(start);
                                if remaining == 3 {
                                    let (b_name, b_info, b_key) = match &list[start].kind {
                                        SyntaxKind::Symbol(s) => (
                                            s.clone(),
                                            kernel::ast::BinderInfo::Default,
                                            self.get_key(&list[start]),
                                        ),
                                        SyntaxKind::Hole => (
                                            "_".to_string(),
                                            kernel::ast::BinderInfo::Default,
                                            self.get_key(&list[start]),
                                        ),
                                        SyntaxKind::BracedList(l) => {
                                            if l.len() == 1 {
                                                if let SyntaxKind::Symbol(s) = &l[0].kind {
                                                    (
                                                        s.clone(),
                                                        kernel::ast::BinderInfo::Implicit,
                                                        self.get_key(&l[0]),
                                                    )
                                                } else {
                                                    return Err(ExpansionError::InvalidSyntax(
                                                        "pi binder".to_string(),
                                                        "Expected symbol in brace".to_string(),
                                                    ));
                                                }
                                            } else {
                                                return Err(ExpansionError::InvalidSyntax(
                                                    "pi binder".to_string(),
                                                    "Expected one element in brace".to_string(),
                                                ));
                                            }
                                        }
                                        _ => {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "pi binder".to_string(),
                                                "Expected symbol or braced symbol".to_string(),
                                            ))
                                        }
                                    };
                                    Ok((
                                        b_name,
                                        list[start + 1].clone(),
                                        b_info,
                                        b_key,
                                        list[start + 2].clone(),
                                    ))
                                } else if remaining == 2 {
                                    let (b_name, b_ty, b_info, b_key) = match &list[start].kind {
                                        SyntaxKind::BracedList(l) => {
                                            if l.len() == 2 {
                                                if let SyntaxKind::Symbol(s) = &l[0].kind {
                                                    (
                                                        s.clone(),
                                                        l[1].clone(),
                                                        kernel::ast::BinderInfo::Implicit,
                                                        self.get_key(&l[0]),
                                                    )
                                                } else {
                                                    return Err(ExpansionError::InvalidSyntax(
                                                        "pi binder".to_string(),
                                                        "Expected {name type}".to_string(),
                                                    ));
                                                }
                                            } else {
                                                return Err(ExpansionError::InvalidSyntax(
                                                    "pi binder".to_string(),
                                                    "Expected {name type}".to_string(),
                                                ));
                                            }
                                        }
                                        SyntaxKind::List(l) => {
                                            if l.len() == 2 {
                                                if let SyntaxKind::Symbol(s) = &l[0].kind {
                                                    (
                                                        s.clone(),
                                                        l[1].clone(),
                                                        kernel::ast::BinderInfo::Default,
                                                        self.get_key(&l[0]),
                                                    )
                                                } else {
                                                    return Err(ExpansionError::InvalidSyntax(
                                                        "pi binder".to_string(),
                                                        "Expected (name type)".to_string(),
                                                    ));
                                                }
                                            } else {
                                                return Err(ExpansionError::InvalidSyntax(
                                                    "pi binder".to_string(),
                                                    "Expected (name type)".to_string(),
                                                ));
                                            }
                                        }
                                        _ => {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "pi binder".to_string(),
                                                "Expected (name type) or {name type}".to_string(),
                                            ))
                                        }
                                    };
                                    Ok((b_name, b_ty, b_info, b_key, list[start + 1].clone()))
                                } else {
                                    Err(ExpansionError::InvalidSyntax(
                                        "pi".to_string(),
                                        "Expected (pi [kind] (name type) body) or (pi [kind] name type body)"
                                            .to_string(),
                                    ))
                                }
                            };

                            let mut kind_opt = None;
                            let mut parsed: Option<(
                                String,
                                Syntax,
                                kernel::ast::BinderInfo,
                                (String, Vec<ScopeId>),
                                Syntax,
                            )> = None;

                            if list.len() >= 4 {
                                if let Some((kind, strict)) =
                                    self.parse_function_kind_token(&list[1])?
                                {
                                    match parse_pi_from(2) {
                                        Ok(parsed_inner) => {
                                            kind_opt = Some(kind);
                                            parsed = Some(parsed_inner);
                                        }
                                        Err(err) => {
                                            if strict {
                                                return Err(err);
                                            }
                                        }
                                    }
                                }
                            }

                            let (
                                binder_name,
                                binder_type_syntax,
                                binder_info,
                                binder_key,
                                body_syntax,
                            ) = match parsed {
                                Some(value) => value,
                                None => parse_pi_from(1)?,
                            };

                            let fresh_name = self.gensym(&binder_name);

                            let ty = self.desugar_with_env(binder_type_syntax, env)?;

                            let mut body_env = env.clone();
                            Self::insert_binding(
                                &mut body_env,
                                binder_key.0,
                                binder_key.1,
                                fresh_name.clone(),
                            );
                            let body = self.desugar_with_env(body_syntax, &mut body_env)?;

                            Ok(mk_term(
                                SurfaceTermKind::Pi(
                                    fresh_name,
                                    binder_info,
                                    kind_opt,
                                    Box::new(ty),
                                    Box::new(body),
                                ),
                                span,
                            ))
                        }
                        "let" => {
                            if list.len() != 5 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "let".to_string(),
                                    4,
                                    list.len() - 1,
                                ));
                            }
                            let name = if let SyntaxKind::Symbol(s) = &list[1].kind {
                                s.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "let".to_string(),
                                    "Expected name".to_string(),
                                ));
                            };
                            let binder_key = self.get_key(&list[1]);

                            let ty = self.desugar_with_env(list[2].clone(), env)?;
                            let val = self.desugar_with_env(list[3].clone(), env)?;

                            let fresh_name = self.gensym(&name);
                            let mut body_env = env.clone();
                            Self::insert_binding(
                                &mut body_env,
                                binder_key.0,
                                binder_key.1,
                                fresh_name.clone(),
                            );

                            let body = self.desugar_with_env(list[4].clone(), &mut body_env)?;

                            Ok(mk_term(
                                SurfaceTermKind::Let(
                                    fresh_name,
                                    Box::new(ty),
                                    Box::new(val),
                                    Box::new(body),
                                ),
                                span,
                            ))
                        }
                        "&" => {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "&".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            let inner = self.desugar_with_env(list[1].clone(), env)?;
                            let borrow_fn =
                                mk_term(SurfaceTermKind::Var("borrow_shared".to_string()), span);
                            Ok(mk_term(
                                SurfaceTermKind::App(Box::new(borrow_fn), Box::new(inner), true),
                                span,
                            ))
                        }
                        "&mut" => {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "&mut".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            let inner = self.desugar_with_env(list[1].clone(), env)?;
                            let borrow_fn =
                                mk_term(SurfaceTermKind::Var("borrow_mut".to_string()), span);
                            Ok(mk_term(
                                SurfaceTermKind::App(Box::new(borrow_fn), Box::new(inner), true),
                                span,
                            ))
                        }
                        "app" => {
                            let f = self.desugar_with_env(list[1].clone(), env)?;
                            if let SyntaxKind::BracedList(l) = &list[2].kind {
                                if l.len() == 1 {
                                    let x = self.desugar_with_env(l[0].clone(), env)?;
                                    Ok(mk_term(
                                        SurfaceTermKind::App(Box::new(f), Box::new(x), false),
                                        span,
                                    ))
                                } else {
                                    Err(ExpansionError::InvalidSyntax(
                                        "app".to_string(),
                                        "Implicit argument must be singleton".to_string(),
                                    ))
                                }
                            } else {
                                let x = self.desugar_with_env(list[2].clone(), env)?;
                                Ok(mk_term(
                                    SurfaceTermKind::App(Box::new(f), Box::new(x), true),
                                    span,
                                ))
                            }
                        }
                        "sort" => {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "sort".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            if let SyntaxKind::Int(n) = &list[1].kind {
                                let mut level = kernel::ast::Level::Zero;
                                for _ in 0..*n {
                                    level = kernel::ast::Level::Succ(Box::new(level));
                                }
                                Ok(mk_term(SurfaceTermKind::Sort(level), span))
                            } else {
                                Err(ExpansionError::InvalidSyntax(
                                    "sort".to_string(),
                                    "Expected integer level".to_string(),
                                ))
                            }
                        }
                        "ind" => {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "ind".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            let n = if let SyntaxKind::Symbol(s) = &list[1].kind {
                                s.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "ind".to_string(),
                                    "Expected name".to_string(),
                                ));
                            };
                            Ok(mk_term(SurfaceTermKind::Ind(n), span))
                        }
                        "ctor" => {
                            if list.len() != 3 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "ctor".to_string(),
                                    2,
                                    list.len() - 1,
                                ));
                            }
                            let name = if let SyntaxKind::Symbol(s) = &list[1].kind {
                                s.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "ctor".to_string(),
                                    "Expected name".to_string(),
                                ));
                            };
                            let idx = if let SyntaxKind::Int(i) = &list[2].kind {
                                *i
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "ctor".to_string(),
                                    "Expected index".to_string(),
                                ));
                            };
                            Ok(mk_term(SurfaceTermKind::Ctor(name, idx), span))
                        }
                        "rec" => {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "rec".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            let n = if let SyntaxKind::Symbol(s) = &list[1].kind {
                                s.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "rec".to_string(),
                                    "Expected name".to_string(),
                                ));
                            };
                            Ok(mk_term(SurfaceTermKind::Rec(n), span))
                        }
                        "fix" => {
                            if list.len() != 4 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "fix".to_string(),
                                    3,
                                    list.len() - 1,
                                ));
                            }
                            let name = if let SyntaxKind::Symbol(s) = &list[1].kind {
                                s.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "fix".to_string(),
                                    "Expected name".to_string(),
                                ));
                            };
                            let key = self.get_key(&list[1]);

                            let ty = self.desugar_with_env(list[2].clone(), env)?;

                            let fresh_name = self.gensym(&name);
                            let mut body_env = env.clone();
                            Self::insert_binding(&mut body_env, key.0, key.1, fresh_name.clone());

                            let body = self.desugar_with_env(list[3].clone(), &mut body_env)?;

                            Ok(mk_term(
                                SurfaceTermKind::Fix(fresh_name, Box::new(ty), Box::new(body)),
                                span,
                            ))
                        }
                        "match" => {
                            if list.len() < 3 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "match".to_string(),
                                    2,
                                    list.len() - 1,
                                ));
                            }

                            let disc = self.desugar_with_env(list[1].clone(), env)?;
                            let ret_ty = self.desugar_with_env(list[2].clone(), env)?;

                            let mut cases = Vec::new();
                            for case_syntax in list.iter().skip(3) {
                                if let SyntaxKind::List(clist) = &case_syntax.kind {
                                    if clist.len() != 3 {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "case".to_string(),
                                            "Expected (case pat body)".to_string(),
                                        ));
                                    }
                                    if let SyntaxKind::Symbol(s) = &clist[0].kind {
                                        if s != "case" {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "case".to_string(),
                                                "Expected 'case'".to_string(),
                                            ));
                                        }
                                    } else {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "case".to_string(),
                                            "Expected 'case'".to_string(),
                                        ));
                                    }

                                    let mut body_env = env.clone();
                                    let (ctor_name, args) = if let SyntaxKind::List(pat) =
                                        &clist[1].kind
                                    {
                                        if pat.is_empty() {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "case pattern".to_string(),
                                                "Empty pattern".to_string(),
                                            ));
                                        }
                                        let c_name = if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                            c.clone()
                                        } else {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "case pattern".to_string(),
                                                "Expected constructor name".to_string(),
                                            ));
                                        };
                                        let c_args: Vec<String> = pat
                                            .iter()
                                            .skip(1)
                                            .map(|p| {
                                                if let SyntaxKind::Symbol(a) = &p.kind {
                                                    let fresh_name = self.gensym(a);
                                                    let (key_name, key_scopes) = self.get_key(p);
                                                    Self::insert_binding(
                                                        &mut body_env,
                                                        key_name,
                                                        key_scopes,
                                                        fresh_name.clone(),
                                                    );
                                                    fresh_name
                                                } else {
                                                    "_".to_string()
                                                }
                                            })
                                            .collect();
                                        (c_name, c_args)
                                    } else {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "case pattern".to_string(),
                                            "Expected list pattern".to_string(),
                                        ));
                                    };

                                    let body =
                                        self.desugar_with_env(clist[2].clone(), &mut body_env)?;
                                    cases.push((ctor_name, args, body));
                                } else {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "match".to_string(),
                                        "Expected case list".to_string(),
                                    ));
                                }
                            }

                            Ok(mk_term(
                                SurfaceTermKind::Match(Box::new(disc), Box::new(ret_ty), cases),
                                span,
                            ))
                        }
                        "match_list" => {
                            if list.len() != 6 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "match_list".to_string(),
                                    5,
                                    list.len() - 1,
                                ));
                            }

                            let scrut = self.desugar_with_env(list[1].clone(), env)?;
                            let param_t = self.desugar_with_env(list[2].clone(), env)?;
                            let ret_ty = self.desugar_with_env(list[3].clone(), env)?;

                            let case_nil = &list[4];
                            let case_cons = &list[5];

                            let nil_body = if let SyntaxKind::List(nlist) = &case_nil.kind {
                                if nlist.len() != 3 {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "match_list".to_string(),
                                        "Invalid nil case".to_string(),
                                    ));
                                }
                                if let SyntaxKind::Symbol(s) = &nlist[0].kind {
                                    if s != "case" {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "match_list".to_string(),
                                            "Expected 'case'".to_string(),
                                        ));
                                    }
                                } else {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "match_list".to_string(),
                                        "Expected 'case'".to_string(),
                                    ));
                                }

                                if let SyntaxKind::List(pat) = &nlist[1].kind {
                                    if pat.len() != 2 {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "match_list".to_string(),
                                            "Invalid nil pattern".to_string(),
                                        ));
                                    }
                                    if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                        if c != "nil" {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "match_list".to_string(),
                                                "Expected 'nil'".to_string(),
                                            ));
                                        }
                                    } else {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "match_list".to_string(),
                                            "Expected 'nil'".to_string(),
                                        ));
                                    }

                                    let (t_key, t_name) =
                                        if let SyntaxKind::Symbol(t) = &pat[1].kind {
                                            (Some(self.get_key(&pat[1])), t.clone())
                                        } else {
                                            (None, "_".to_string())
                                        };
                                    let mut body_env = env.clone();
                                    let mut fresh_t_name = None;
                                    if let Some(k) = t_key {
                                        let fresh = self.gensym(&t_name);
                                        Self::insert_binding(
                                            &mut body_env,
                                            k.0,
                                            k.1,
                                            fresh.clone(),
                                        );
                                        fresh_t_name = Some(fresh);
                                    }

                                    let body =
                                        self.desugar_with_env(nlist[2].clone(), &mut body_env)?;
                                    if let Some(fresh) = fresh_t_name {
                                        self.substitute_surface_var(body, &fresh, &param_t)
                                    } else {
                                        body
                                    }
                                } else {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "match_list".to_string(),
                                        "Invalid nil pattern".to_string(),
                                    ));
                                }
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "match_list".to_string(),
                                    "Invalid nil case".to_string(),
                                ));
                            };

                            let (cons_bindings, cons_body) =
                                if let SyntaxKind::List(clist) = &case_cons.kind {
                                    if clist.len() != 3 {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "match_list".to_string(),
                                            "Invalid cons case".to_string(),
                                        ));
                                    }
                                    if let SyntaxKind::Symbol(s) = &clist[0].kind {
                                        if s != "case" {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "match_list".to_string(),
                                                "Expected 'case'".to_string(),
                                            ));
                                        }
                                    } else {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "match_list".to_string(),
                                            "Expected 'case'".to_string(),
                                        ));
                                    }

                                    if let SyntaxKind::List(pat) = &clist[1].kind {
                                        if pat.len() != 4 {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "match_list".to_string(),
                                                "Invalid cons pattern".to_string(),
                                            ));
                                        }
                                        if let SyntaxKind::Symbol(c) = &pat[0].kind {
                                            if c != "cons" {
                                                return Err(ExpansionError::InvalidSyntax(
                                                    "match_list".to_string(),
                                                    "Expected 'cons'".to_string(),
                                                ));
                                            }
                                        }
                                        let mut body_env = env.clone();
                                        let mut fresh_t_name = None;
                                        if let SyntaxKind::Symbol(t) = &pat[1].kind {
                                            let fresh = self.gensym(t);
                                            let (key_name, key_scopes) = self.get_key(&pat[1]);
                                            Self::insert_binding(
                                                &mut body_env,
                                                key_name,
                                                key_scopes,
                                                fresh.clone(),
                                            );
                                            fresh_t_name = Some(fresh);
                                        }

                                        let mut bindings = Vec::new();
                                        for p in pat.iter().skip(2) {
                                            if let SyntaxKind::Symbol(v) = &p.kind {
                                                let fresh_name = self.gensym(v);
                                                let (key_name, key_scopes) = self.get_key(p);
                                                Self::insert_binding(
                                                    &mut body_env,
                                                    key_name,
                                                    key_scopes,
                                                    fresh_name.clone(),
                                                );
                                                bindings.push(fresh_name);
                                            } else {
                                                bindings.push("_".to_string());
                                            }
                                        }

                                        let body =
                                            self.desugar_with_env(clist[2].clone(), &mut body_env)?;
                                        let body = if let Some(fresh) = fresh_t_name {
                                            self.substitute_surface_var(body, &fresh, &param_t)
                                        } else {
                                            body
                                        };
                                        (bindings, body)
                                    } else {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "match_list".to_string(),
                                            "Invalid cons pattern".to_string(),
                                        ));
                                    }
                                } else {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "match_list".to_string(),
                                        "Invalid cons case".to_string(),
                                    ));
                                };

                            let mut cases = Vec::new();
                            cases.push(("nil".to_string(), Vec::new(), nil_body));
                            cases.push(("cons".to_string(), cons_bindings, cons_body));

                            let scrut_name = self.gensym("scrut");
                            let scrut_ty = mk_term(
                                SurfaceTermKind::App(
                                    Box::new(mk_term(
                                        SurfaceTermKind::Ind("List".to_string()),
                                        span,
                                    )),
                                    Box::new(param_t.clone()),
                                    true,
                                ),
                                span,
                            );
                            let match_term = mk_term(
                                SurfaceTermKind::Match(
                                    Box::new(mk_term(
                                        SurfaceTermKind::Var(scrut_name.clone()),
                                        span,
                                    )),
                                    Box::new(ret_ty),
                                    cases,
                                ),
                                span,
                            );
                            Ok(mk_term(
                                SurfaceTermKind::Let(
                                    scrut_name,
                                    Box::new(scrut_ty),
                                    Box::new(scrut),
                                    Box::new(match_term),
                                ),
                                span,
                            ))
                        }
                        "eval" => {
                            if list.len() != 3 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "eval".to_string(),
                                    2,
                                    list.len() - 1,
                                ));
                            }
                            let code = self.desugar_with_env(list[1].clone(), env)?;
                            let cap = self.desugar_with_env(list[2].clone(), env)?;
                            Ok(mk_term(
                                SurfaceTermKind::Eval(Box::new(code), Box::new(cap)),
                                span,
                            ))
                        }
                        "quote" => {
                            if list.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "quote".to_string(),
                                    1,
                                    list.len() - 1,
                                ));
                            }
                            let content = &list[1];
                            Ok(self.quote_syntax(content, span))
                        }
                        _ => {
                            let mut term = self.desugar_with_env(list[0].clone(), env)?;
                            for arg in list.iter().skip(1) {
                                if let SyntaxKind::BracedList(l) = &arg.kind {
                                    if l.len() == 1 {
                                        let arg_term = self.desugar_with_env(l[0].clone(), env)?;
                                        term = mk_term(
                                            SurfaceTermKind::App(
                                                Box::new(term),
                                                Box::new(arg_term),
                                                false,
                                            ),
                                            span,
                                        );
                                    } else {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "application".to_string(),
                                            "Implicit arg must be singleton".to_string(),
                                        ));
                                    }
                                } else {
                                    let arg_term = self.desugar_with_env(arg.clone(), env)?;
                                    term = mk_term(
                                        SurfaceTermKind::App(
                                            Box::new(term),
                                            Box::new(arg_term),
                                            true,
                                        ),
                                        span,
                                    );
                                }
                            }
                            Ok(term)
                        }
                    }
                } else {
                    let mut term = self.desugar_with_env(list[0].clone(), env)?;
                    for arg in list.iter().skip(1) {
                        if let SyntaxKind::BracedList(l) = &arg.kind {
                            if l.len() == 1 {
                                let arg_term = self.desugar_with_env(l[0].clone(), env)?;
                                term = mk_term(
                                    SurfaceTermKind::App(Box::new(term), Box::new(arg_term), false),
                                    span,
                                );
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "application".to_string(),
                                    "Implicit arg must be singleton".to_string(),
                                ));
                            }
                        } else {
                            let arg_term = self.desugar_with_env(arg.clone(), env)?;
                            term = mk_term(
                                SurfaceTermKind::App(Box::new(term), Box::new(arg_term), true),
                                span,
                            );
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
            }
            SyntaxKind::Index(base, index) => {
                if let SyntaxKind::Symbol(base_sym) = &base.kind {
                    if base_sym == "#" {
                        if let SyntaxKind::Symbol(label) = &index.kind {
                            let base_term = mk_term(SurfaceTermKind::Var("#".to_string()), span);
                            let index_term = mk_term(SurfaceTermKind::Var(label.clone()), span);
                            return Ok(mk_term(
                                SurfaceTermKind::Index(Box::new(base_term), Box::new(index_term)),
                                span,
                            ));
                        }
                    }
                }
                let base_term = self.desugar_with_env(*base, env)?;
                let index_term = self.desugar_with_env(*index, env)?;
                Ok(mk_term(
                    SurfaceTermKind::Index(Box::new(base_term), Box::new(index_term)),
                    span,
                ))
            }
            SyntaxKind::Hole => Ok(mk_term(SurfaceTermKind::Hole, span)),
            SyntaxKind::Int(n) => {
                // Desugar Int to Nat constructors
                let mut t = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 0), span); // Zero
                let succ = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 1), span); // Succ
                for _ in 0..n {
                    t = mk_term(
                        SurfaceTermKind::App(Box::new(succ.clone()), Box::new(t), true),
                        span,
                    );
                }
                Ok(t)
            }
            SyntaxKind::String(s) => {
                let syntax = Syntax {
                    kind: SyntaxKind::String(s),
                    span,
                    scopes: Vec::new(),
                };
                Ok(self.quote_syntax(&syntax, span))
            }
            _ => Err(ExpansionError::UnknownForm(format!("{:?}", syntax.kind))),
        }
    }

    fn quote_syntax(&self, syntax: &Syntax, span: Span) -> SurfaceTerm {
        let nil_tm = mk_term(SurfaceTermKind::Ctor("List".to_string(), 0), span); // nil
        let cons_ctor = mk_term(SurfaceTermKind::Ctor("List".to_string(), 1), span); // cons
        let build_list = |items: Vec<SurfaceTerm>| {
            let mut term = nil_tm.clone();
            for item in items.into_iter().rev() {
                let app1 = mk_term(
                    SurfaceTermKind::App(Box::new(cons_ctor.clone()), Box::new(item), true),
                    span,
                );
                term = mk_term(
                    SurfaceTermKind::App(Box::new(app1), Box::new(term), true),
                    span,
                );
            }
            term
        };
        let build_nat = |n: usize| {
            let mut t = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 0), span); // Zero
            let succ = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 1), span); // Succ
            for _ in 0..n {
                t = mk_term(
                    SurfaceTermKind::App(Box::new(succ.clone()), Box::new(t), true),
                    span,
                );
            }
            t
        };
        match &syntax.kind {
            SyntaxKind::List(list) => {
                let items = list
                    .iter()
                    .map(|item| self.quote_syntax(item, span))
                    .collect();
                build_list(items)
            }
            SyntaxKind::Int(n) => build_nat(*n),
            SyntaxKind::String(s) => {
                let items = s.chars().map(|ch| build_nat(ch as usize)).collect();
                build_list(items)
            }
            SyntaxKind::Symbol(s) => {
                let items = s.chars().map(|ch| build_nat(ch as usize)).collect();
                build_list(items)
            }
            _ => mk_term(SurfaceTermKind::Hole, span),
        }
    }
}

fn mk_term(kind: SurfaceTermKind, span: Span) -> SurfaceTerm {
    SurfaceTerm { kind, span }
}
