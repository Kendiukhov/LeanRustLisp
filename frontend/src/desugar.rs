use crate::macro_expander::ExpansionError;
use crate::surface::{
    normalize_scopes, ScopeId, Span, SurfaceTerm, SurfaceTermKind, Syntax, SyntaxKind,
};
use kernel::ast::FunctionKind;
use std::collections::BTreeMap;

type HygieneEnv = BTreeMap<String, BTreeMap<Vec<ScopeId>, String>>;
type PiBinderParse = (
    String,
    Syntax,
    kernel::ast::BinderInfo,
    (String, Vec<ScopeId>),
    Syntax,
);

pub struct Desugarer {
    gensym_counter: usize,
}

impl Default for Desugarer {
    fn default() -> Self {
        Self::new()
    }
}

impl Desugarer {
    const ASCII_CACHE_MAX: usize = 99;
    const TEXT_LITERAL_CHUNK_SIZE: usize = 16;

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
            match ref_norm[ref_idx].cmp(&def_norm[def_idx]) {
                std::cmp::Ordering::Equal => {
                    ref_idx += 1;
                    def_idx += 1;
                }
                std::cmp::Ordering::Less => {
                    ref_idx += 1;
                }
                std::cmp::Ordering::Greater => {
                    return false;
                }
            }
        }
        def_idx == def_norm.len()
    }

    fn insert_binding(env: &mut HygieneEnv, name: String, scopes: Vec<ScopeId>, fresh: String) {
        let entry = env.entry(name).or_default();
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
                let new_f = Self::substitute_surface_var(*f, name, replacement);
                let new_x = Self::substitute_surface_var(*x, name, replacement);
                mk_term(
                    SurfaceTermKind::App(Box::new(new_f), Box::new(new_x), is_explicit),
                    span,
                )
            }
            SurfaceTermKind::Index(base, index) => {
                let new_base = Self::substitute_surface_var(*base, name, replacement);
                let new_index = Self::substitute_surface_var(*index, name, replacement);
                mk_term(
                    SurfaceTermKind::Index(Box::new(new_base), Box::new(new_index)),
                    span,
                )
            }
            SurfaceTermKind::Lam(binder, info, kind, ty, body) => {
                let new_ty = Self::substitute_surface_var(*ty, name, replacement);
                if binder == name {
                    mk_term(
                        SurfaceTermKind::Lam(binder, info, kind, Box::new(new_ty), body),
                        span,
                    )
                } else {
                    let new_body = Self::substitute_surface_var(*body, name, replacement);
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
                let new_ty = Self::substitute_surface_var(*ty, name, replacement);
                if binder == name {
                    mk_term(
                        SurfaceTermKind::Pi(binder, info, kind, Box::new(new_ty), body),
                        span,
                    )
                } else {
                    let new_body = Self::substitute_surface_var(*body, name, replacement);
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
                let new_ty = Self::substitute_surface_var(*ty, name, replacement);
                let new_val = Self::substitute_surface_var(*val, name, replacement);
                if binder == name {
                    mk_term(
                        SurfaceTermKind::Let(binder, Box::new(new_ty), Box::new(new_val), body),
                        span,
                    )
                } else {
                    let new_body = Self::substitute_surface_var(*body, name, replacement);
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
                let new_ty = Self::substitute_surface_var(*ty, name, replacement);
                if binder == name {
                    mk_term(SurfaceTermKind::Fix(binder, Box::new(new_ty), body), span)
                } else {
                    let new_body = Self::substitute_surface_var(*body, name, replacement);
                    mk_term(
                        SurfaceTermKind::Fix(binder, Box::new(new_ty), Box::new(new_body)),
                        span,
                    )
                }
            }
            SurfaceTermKind::Match(scrutinee, ret_type, cases) => {
                let new_scrutinee = Self::substitute_surface_var(*scrutinee, name, replacement);
                let new_ret_type = Self::substitute_surface_var(*ret_type, name, replacement);
                let mut new_cases = Vec::new();
                for (ctor_name, bindings, body) in cases {
                    if bindings.iter().any(|b| b == name) {
                        new_cases.push((ctor_name, bindings, body));
                    } else {
                        let new_body = Self::substitute_surface_var(body, name, replacement);
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
                let new_code = Self::substitute_surface_var(*code, name, replacement);
                let new_cap = Self::substitute_surface_var(*cap, name, replacement);
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
                            let mut parsed: Option<PiBinderParse> = None;

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
                            if list.len() != 3 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "app".to_string(),
                                    2,
                                    list.len() - 1,
                                ));
                            }
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
                                let level_usize = usize::try_from(*n).map_err(|_| {
                                    ExpansionError::InvalidSyntax(
                                        "sort".to_string(),
                                        "Expected non-negative integer level".to_string(),
                                    )
                                })?;
                                let mut level = kernel::ast::Level::Zero;
                                for _ in 0..level_usize {
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
                                usize::try_from(*i).map_err(|_| {
                                    ExpansionError::InvalidSyntax(
                                        "ctor".to_string(),
                                        "Expected non-negative index".to_string(),
                                    )
                                })?
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
                            if list.len() < 4 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "match".to_string(),
                                    3,
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
                                        Self::substitute_surface_var(body, &fresh, &param_t)
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
                                            Self::substitute_surface_var(body, &fresh, &param_t)
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

                            let cases = vec![
                                ("nil".to_string(), Vec::new(), nil_body),
                                ("cons".to_string(), cons_bindings, cons_body),
                            ];

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
                            Ok(Self::quote_syntax(content, span))
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
            SyntaxKind::Int(n) => Ok(Self::number_literal_term(n, span)),
            SyntaxKind::String(s) => Ok(Self::text_literal_term(&s, span)),
            _ => Err(ExpansionError::UnknownForm(format!("{:?}", syntax.kind))),
        }
    }

    fn number_literal_term(value: i64, span: Span) -> SurfaceTerm {
        if value >= 0 {
            Self::nat_literal_term(value as usize, span)
        } else {
            Self::int_literal_term(value, span)
        }
    }

    fn nat_literal_term(value: usize, span: Span) -> SurfaceTerm {
        let mut term = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 0), span);
        let succ_ctor = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 1), span);
        for _ in 0..value {
            term = mk_term(
                SurfaceTermKind::App(Box::new(succ_ctor.clone()), Box::new(term), true),
                span,
            );
        }
        term
    }

    fn compact_nat_literal_term(value: usize, span: Span) -> SurfaceTerm {
        if value <= 1 {
            return Self::nat_literal_term(value, span);
        }

        let half_value = value / 2;
        let half_name = format!("__nat_half_{}", value);
        let nat_ty = mk_term(SurfaceTermKind::Ind("Nat".to_string()), span);
        let half_term = Self::compact_nat_literal_term(half_value, span);
        let half_var_lhs = mk_term(SurfaceTermKind::Var(half_name.clone()), span);
        let half_var_rhs = mk_term(SurfaceTermKind::Var(half_name.clone()), span);
        let add_fn = mk_term(SurfaceTermKind::Var("add".to_string()), span);
        let add_lhs = mk_term(
            SurfaceTermKind::App(Box::new(add_fn), Box::new(half_var_lhs), true),
            span,
        );
        let doubled = mk_term(
            SurfaceTermKind::App(Box::new(add_lhs), Box::new(half_var_rhs), true),
            span,
        );
        let body = if value % 2 == 0 {
            doubled
        } else {
            let succ_ctor = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 1), span);
            mk_term(
                SurfaceTermKind::App(Box::new(succ_ctor), Box::new(doubled), true),
                span,
            )
        };
        mk_term(
            SurfaceTermKind::Let(
                half_name,
                Box::new(nat_ty),
                Box::new(half_term),
                Box::new(body),
            ),
            span,
        )
    }

    fn int_literal_term(value: i64, span: Span) -> SurfaceTerm {
        let magnitude = value.unsigned_abs() as usize;
        let magnitude_term = Self::compact_nat_literal_term(magnitude, span);
        let neg_ctor = mk_term(SurfaceTermKind::Ctor("Int".to_string(), 1), span);
        mk_term(
            SurfaceTermKind::App(Box::new(neg_ctor), Box::new(magnitude_term), true),
            span,
        )
    }

    fn text_literal_term(value: &str, span: Span) -> SurfaceTerm {
        let codepoints: Vec<usize> = value.chars().map(|ch| ch as usize).collect();
        let mut high_codepoint_bindings: BTreeMap<usize, String> = BTreeMap::new();
        for code in &codepoints {
            if *code > Self::ASCII_CACHE_MAX {
                high_codepoint_bindings
                    .entry(*code)
                    .or_insert_with(|| format!("__text_cp_{}", code));
            }
        }

        let nil_list = mk_term(SurfaceTermKind::Ctor("List".to_string(), 0), span);
        let cons_ctor = mk_term(SurfaceTermKind::Ctor("List".to_string(), 1), span);
        let mut chunks: Vec<SurfaceTerm> = Vec::new();
        let mut current_chunk: Vec<usize> = Vec::new();
        for code in codepoints {
            current_chunk.push(code);
            if current_chunk.len() == Self::TEXT_LITERAL_CHUNK_SIZE {
                chunks.push(Self::list_chunk_term(
                    &current_chunk,
                    &cons_ctor,
                    &nil_list,
                    &high_codepoint_bindings,
                    span,
                ));
                current_chunk.clear();
            }
        }
        if !current_chunk.is_empty() {
            chunks.push(Self::list_chunk_term(
                &current_chunk,
                &cons_ctor,
                &nil_list,
                &high_codepoint_bindings,
                span,
            ));
        }

        let append_fn = mk_term(SurfaceTermKind::Var("append".to_string()), span);
        while chunks.len() > 1 {
            let mut next = Vec::with_capacity((chunks.len() + 1) / 2);
            for pair in chunks.chunks(2) {
                if pair.len() == 1 {
                    next.push(pair[0].clone());
                } else {
                    let left = pair[0].clone();
                    let right = pair[1].clone();
                    let append_left = mk_term(
                        SurfaceTermKind::App(Box::new(append_fn.clone()), Box::new(left), true),
                        span,
                    );
                    let merged = mk_term(
                        SurfaceTermKind::App(Box::new(append_left), Box::new(right), true),
                        span,
                    );
                    next.push(merged);
                }
            }
            chunks = next;
        }
        let list_value = chunks.into_iter().next().unwrap_or(nil_list);
        let text_ctor = mk_term(SurfaceTermKind::Ctor("Text".to_string(), 0), span);
        let mut text_term = mk_term(
            SurfaceTermKind::App(Box::new(text_ctor), Box::new(list_value), true),
            span,
        );
        if !high_codepoint_bindings.is_empty() {
            let nat_ty = mk_term(SurfaceTermKind::Ind("Nat".to_string()), span);
            for (code, name) in high_codepoint_bindings.iter().rev() {
                let code_term = Self::compact_nat_literal_term(*code, span);
                text_term = mk_term(
                    SurfaceTermKind::Let(
                        name.clone(),
                        Box::new(nat_ty.clone()),
                        Box::new(code_term),
                        Box::new(text_term),
                    ),
                    span,
                );
            }
        }
        text_term
    }

    fn list_chunk_term(
        values: &[usize],
        cons_ctor: &SurfaceTerm,
        nil_list: &SurfaceTerm,
        high_codepoint_bindings: &BTreeMap<usize, String>,
        span: Span,
    ) -> SurfaceTerm {
        let mut term = nil_list.clone();
        for code in values.iter().rev() {
            let head = if *code <= Self::ASCII_CACHE_MAX {
                mk_term(SurfaceTermKind::Var(format!("__nat_ascii_{}", code)), span)
            } else if let Some(binding) = high_codepoint_bindings.get(code) {
                mk_term(SurfaceTermKind::Var(binding.clone()), span)
            } else {
                Self::compact_nat_literal_term(*code, span)
            };
            let cons_head = mk_term(
                SurfaceTermKind::App(Box::new(cons_ctor.clone()), Box::new(head), true),
                span,
            );
            term = mk_term(
                SurfaceTermKind::App(Box::new(cons_head), Box::new(term), true),
                span,
            );
        }
        term
    }

    fn quote_syntax(syntax: &Syntax, span: Span) -> SurfaceTerm {
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
        match &syntax.kind {
            SyntaxKind::List(list) => {
                let items = list
                    .iter()
                    .map(|item| Self::quote_syntax(item, span))
                    .collect();
                build_list(items)
            }
            SyntaxKind::Int(n) => Self::number_literal_term(*n, span),
            SyntaxKind::String(s) => {
                let items = s
                    .chars()
                    .map(|ch| Self::nat_literal_term(ch as usize, span))
                    .collect();
                build_list(items)
            }
            SyntaxKind::Symbol(s) => {
                let items = s
                    .chars()
                    .map(|ch| Self::nat_literal_term(ch as usize, span))
                    .collect();
                build_list(items)
            }
            _ => mk_term(SurfaceTermKind::Hole, span),
        }
    }
}

fn mk_term(kind: SurfaceTermKind, span: Span) -> SurfaceTerm {
    SurfaceTerm { kind, span }
}
