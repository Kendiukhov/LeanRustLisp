use std::rc::Rc;
use std::fmt;

/// Source location info
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub col: usize,
}

/// Scope identifier (for hygiene)
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct ScopeId(pub usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Syntax {
    pub kind: SyntaxKind,
    pub span: Span,
    pub scopes: Vec<ScopeId>,
}

impl Syntax {
    pub fn pretty_print(&self) -> String {
        match &self.kind {
            SyntaxKind::List(list) => {
                let inner: Vec<String> = list.iter().map(|s| s.pretty_print()).collect();
                format!("({})", inner.join(" "))
            }
            SyntaxKind::BracedList(list) => {
                let inner: Vec<String> = list.iter().map(|s| s.pretty_print()).collect();
                format!("{{{}}}", inner.join(" "))
            }
            SyntaxKind::Symbol(s) => s.clone(),
            SyntaxKind::String(s) => format!("\"{}\"", s),
            SyntaxKind::Int(n) => n.to_string(),
            SyntaxKind::Hole => "_".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxKind {
    List(Vec<Syntax>),
    BracedList(Vec<Syntax>), // { ... }
    Symbol(String),
    String(String),
    Int(usize),
    Hole,
}

/// High-level Surface Term
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SurfaceTerm {
    pub kind: SurfaceTermKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SurfaceTermKind {
    Var(String),
    Sort(kernel::ast::Level),
    App(Box<SurfaceTerm>, Box<SurfaceTerm>, bool), // fun, arg, is_explicit (true = explicit, false = implicit/brace)
    Lam(String, kernel::ast::BinderInfo, Box<SurfaceTerm>, Box<SurfaceTerm>), // Name, Info, Type, Body
    Pi(String, kernel::ast::BinderInfo, Box<SurfaceTerm>, Box<SurfaceTerm>),  // Name, Info, Type, Body
    Let(String, Box<SurfaceTerm>, Box<SurfaceTerm>, Box<SurfaceTerm>), // Name, Type, Val, Body
    // Direct mapping to kernel terms
    Ind(String),
    Ctor(String, usize),
    Rec(String),
    Match(Box<SurfaceTerm>, Box<SurfaceTerm>, Vec<(String, Vec<String>, SurfaceTerm)>), // Scrutinee, RetType, Cases
    Hole,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Def {
        name: String,
        ty: SurfaceTerm,
        val: SurfaceTerm,
        is_partial: bool,
    },
    Axiom {
        name: String,
        ty: SurfaceTerm,
    },
    Inductive {
        name: String,
        ty: SurfaceTerm,
        ctors: Vec<(String, SurfaceTerm)>,
    },
    DefMacro {
        name: String,
        args: Vec<String>,
        body: Syntax,
    },
    Expr(SurfaceTerm),
}
