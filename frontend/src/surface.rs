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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxKind {
    List(Vec<Syntax>),
    Symbol(String),
    String(String),
    Int(usize),
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
    App(Box<SurfaceTerm>, Box<SurfaceTerm>),
    Lam(String, Box<SurfaceTerm>, Box<SurfaceTerm>), // Name, Type, Body
    Pi(String, Box<SurfaceTerm>, Box<SurfaceTerm>),  // Name, Type, Body
    Let(String, Box<SurfaceTerm>, Box<SurfaceTerm>, Box<SurfaceTerm>), // Name, Type, Val, Body
    // Direct mapping to kernel terms
    Ind(String),
    Ctor(String, usize),
    Rec(String),
    Match(Box<SurfaceTerm>, Box<SurfaceTerm>, Vec<(String, Vec<String>, SurfaceTerm)>), // Scrutinee, RetType, Cases
}
