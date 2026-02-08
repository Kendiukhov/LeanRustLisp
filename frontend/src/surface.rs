use kernel::ast::{AxiomTag, FunctionKind, Totality, Transparency};

/// Source location info
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub col: usize,
}

/// Scope identifier (for hygiene)
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct ScopeId(pub usize);

/// Normalize scope sets: sort and deduplicate for deterministic hygiene.
pub fn normalize_scopes(scopes: &[ScopeId]) -> Vec<ScopeId> {
    if scopes.len() <= 1 {
        return scopes.to_vec();
    }
    let mut normalized = scopes.to_vec();
    normalized.sort();
    normalized.dedup();
    normalized
}

/// Return a normalized scope set with `scope` inserted.
pub fn scopes_with(scopes: &[ScopeId], scope: ScopeId) -> Vec<ScopeId> {
    if scopes.contains(&scope) {
        return normalize_scopes(scopes);
    }
    let mut next = scopes.to_vec();
    next.push(scope);
    normalize_scopes(&next)
}

/// Return a normalized scope set with `scope` removed.
pub fn scopes_without(scopes: &[ScopeId], scope: ScopeId) -> Vec<ScopeId> {
    if !scopes.contains(&scope) {
        return normalize_scopes(scopes);
    }
    let next: Vec<ScopeId> = scopes.iter().cloned().filter(|s| *s != scope).collect();
    normalize_scopes(&next)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Syntax {
    pub kind: SyntaxKind,
    pub span: Span,
    pub scopes: Vec<ScopeId>,
}

impl Syntax {
    pub fn pretty_print(&self) -> String {
        self.pretty_print_stable()
    }

    pub fn pretty_print_stable(&self) -> String {
        match &self.kind {
            SyntaxKind::List(list) => {
                let inner: Vec<String> = list.iter().map(|s| s.pretty_print_stable()).collect();
                format!("({})", inner.join(" "))
            }
            SyntaxKind::BracedList(list) => {
                let inner: Vec<String> = list.iter().map(|s| s.pretty_print_stable()).collect();
                format!("{{{}}}", inner.join(" "))
            }
            SyntaxKind::Index(base, index) => format!(
                "{}[{}]",
                base.pretty_print_stable(),
                index.pretty_print_stable()
            ),
            SyntaxKind::Symbol(s) => s.clone(),
            SyntaxKind::String(s) => format!("\"{}\"", escape_string(s)),
            SyntaxKind::Int(n) => n.to_string(),
            SyntaxKind::Float(bits) => bits.clone(),
            SyntaxKind::Hole => "_".to_string(),
        }
    }

    pub fn with_scope(&self, scope: ScopeId) -> Syntax {
        Syntax {
            scopes: scopes_with(&self.scopes, scope),
            ..self.clone()
        }
    }

    pub fn without_scope(&self, scope: ScopeId) -> Syntax {
        Syntax {
            scopes: scopes_without(&self.scopes, scope),
            ..self.clone()
        }
    }
}

fn escape_string(input: &str) -> String {
    let mut out = String::new();
    for ch in input.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxKind {
    List(Vec<Syntax>),
    BracedList(Vec<Syntax>), // { ... }
    Index(Box<Syntax>, Box<Syntax>),
    Symbol(String),
    String(String),
    Int(i64),
    Float(String),
    Hole,
}

/// High-level Surface Term
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SurfaceTerm {
    pub kind: SurfaceTermKind,
    pub span: Span,
}

impl SurfaceTerm {
    pub fn find_fix_span(&self) -> Option<Span> {
        match &self.kind {
            SurfaceTermKind::Fix(_, _, _) => Some(self.span),
            SurfaceTermKind::Var(_)
            | SurfaceTermKind::Sort(_)
            | SurfaceTermKind::Ind(_)
            | SurfaceTermKind::Ctor(_, _)
            | SurfaceTermKind::Rec(_)
            | SurfaceTermKind::Hole => None,
            SurfaceTermKind::App(f, x, _) | SurfaceTermKind::Index(f, x) => {
                f.find_fix_span().or_else(|| x.find_fix_span())
            }
            SurfaceTermKind::Lam(_, _, _, ty, body) | SurfaceTermKind::Pi(_, _, _, ty, body) => {
                ty.find_fix_span().or_else(|| body.find_fix_span())
            }
            SurfaceTermKind::Let(_, ty, val, body) => ty
                .find_fix_span()
                .or_else(|| val.find_fix_span())
                .or_else(|| body.find_fix_span()),
            SurfaceTermKind::Match(scrutinee, ret_type, cases) => {
                if let Some(span) = scrutinee.find_fix_span() {
                    return Some(span);
                }
                if let Some(span) = ret_type.find_fix_span() {
                    return Some(span);
                }
                for (_, _, body) in cases {
                    if let Some(span) = body.find_fix_span() {
                        return Some(span);
                    }
                }
                None
            }
            SurfaceTermKind::Eval(code, cap) => {
                code.find_fix_span().or_else(|| cap.find_fix_span())
            }
        }
    }

    pub fn contains_fix(&self) -> bool {
        self.find_fix_span().is_some()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SurfaceTermKind {
    Var(String),
    Sort(kernel::ast::Level),
    App(Box<SurfaceTerm>, Box<SurfaceTerm>, bool), // fun, arg, is_explicit (true = explicit, false = implicit/brace)
    Index(Box<SurfaceTerm>, Box<SurfaceTerm>),
    Lam(
        String,
        kernel::ast::BinderInfo,
        Option<FunctionKind>,
        Box<SurfaceTerm>,
        Box<SurfaceTerm>,
    ), // Name, Info, Type, Body
    Pi(
        String,
        kernel::ast::BinderInfo,
        Option<FunctionKind>,
        Box<SurfaceTerm>,
        Box<SurfaceTerm>,
    ), // Name, Info, Type, Body
    Let(String, Box<SurfaceTerm>, Box<SurfaceTerm>, Box<SurfaceTerm>), // Name, Type, Val, Body
    // Direct mapping to kernel terms
    Ind(String),
    Ctor(String, usize),
    Rec(String),
    Fix(String, Box<SurfaceTerm>, Box<SurfaceTerm>), // Name, Type, Body
    Match(
        Box<SurfaceTerm>,
        Box<SurfaceTerm>,
        Vec<(String, Vec<String>, SurfaceTerm)>,
    ), // Scrutinee, RetType, Cases
    Eval(Box<SurfaceTerm>, Box<SurfaceTerm>),        // (eval <dyn-code> <EvalCap>)
    Hole,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Def {
        name: String,
        ty: SurfaceTerm,
        val: SurfaceTerm,
        totality: Totality,
        transparency: Transparency,
        noncomputable: bool,
    },
    Axiom {
        name: String,
        ty: SurfaceTerm,
        tags: Vec<AxiomTag>,
    },
    Inductive {
        name: String,
        ty: SurfaceTerm,
        ctors: Vec<(String, SurfaceTerm)>,
        is_copy: bool,
        attrs: Vec<String>,
    },
    Instance {
        trait_name: String,
        head: SurfaceTerm,
        requirements: Vec<SurfaceTerm>,
        is_unsafe: bool,
    },
    DefMacro {
        name: String,
        args: Vec<String>,
        body: Syntax,
    },
    Module {
        name: String,
    },
    ImportClassical,
    ImportModule {
        module: String,
        alias: Option<String>,
    },
    OpenModule {
        target: String,
    },
    Expr(SurfaceTerm),
}
