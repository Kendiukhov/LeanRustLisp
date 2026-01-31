use kernel::ast::{Term, Level};
use std::rc::Rc;

pub mod lower;
pub mod analysis;
pub mod codegen;
pub mod transform;
pub mod errors;

// Id types for type safety
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BasicBlock(pub u32);

impl BasicBlock {
    pub fn index(&self) -> usize { self.0 as usize }
}

impl From<usize> for BasicBlock {
    fn from(idx: usize) -> Self { BasicBlock(idx as u32) }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Local(pub u32);

impl Local {
    pub fn index(&self) -> usize { self.0 as usize }
}

impl From<usize> for Local {
    fn from(idx: usize) -> Self { Local(idx as u32) }
}

// A function body in MIR
#[derive(Debug, Clone)]
pub struct Body {
    pub basic_blocks: Vec<BasicBlockData>,
    pub local_decls: Vec<LocalDecl>,
    pub arg_count: usize,
}

impl Body {
    pub fn new(arg_count: usize) -> Self {
        Body {
            basic_blocks: Vec::new(),
            local_decls: Vec::new(),
            arg_count,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LocalDecl {
    pub ty: Rc<Term>,
    pub name: Option<String>,
    pub is_prop: bool, // Optimization: Pre-computed universe level check
    pub is_copy: bool, // Whether this type has Copy semantics (can be used without moving)
}

impl LocalDecl {
    pub fn new(ty: Rc<Term>, name: Option<String>) -> Self {
        LocalDecl { ty, name, is_prop: false, is_copy: false }
    }

    pub fn new_copy(ty: Rc<Term>, name: Option<String>) -> Self {
        LocalDecl { ty, name, is_prop: false, is_copy: true }
    }
}

#[derive(Debug, Clone)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assign(Place, Rvalue),
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Return,
    Goto { target: BasicBlock },
    SwitchInt {
        discr: Operand,
        targets: SwitchTargets,
    },
    Call {
        func: Operand,
        args: Vec<Operand>,
        destination: Place,
        target: Option<BasicBlock>,
    },
    Unreachable,
}

#[derive(Debug, Clone)]
pub struct SwitchTargets {
    pub values: Vec<u128>,
    pub targets: Vec<BasicBlock>,
    // Fallback if no value matches (standard 'otherwise')
    // usually the last target in targets list or separate?
    // Let's keep it simple: targets.len() == values.len() + 1
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub local: Local,
    // Projection (fields, derefs) would go here
    pub projection: Vec<PlaceElem>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlaceElem {
    Deref,
    Field(usize),
    Downcast(usize), // Variant index
}

impl From<Local> for Place {
    fn from(local: Local) -> Self {
        Place { local, projection: Vec::new() }
    }
}

#[derive(Debug, Clone)]
pub enum Rvalue {
    Use(Operand),
    // BinaryOp, UnaryOp... we lower LRL ops to function calls usually?
    // But basic arithmetic might be intrinsic.
    // For now, LRL treats almost everything as function calls (App).
    // But we might want specific ref handling.
    Ref(BorrowKind, Place),
    // Discriminant of an enum/inductive
    Discriminant(Place),
    // Standard aggregate creation (tuple, struct)
    // Aggregate(Box<AggregateKind>, Vec<Operand>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BorrowKind {
    Shared,
    Mut,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)] // Added Hash
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Box<Constant>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)] // Added Hash
pub struct Constant {
    pub literal: Literal,
    pub ty: Rc<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)] // Added Hash
pub enum Literal {
    Nat(u64), // For simplified constants
    Bool(bool),
    // Or just a raw Term?
    Term(Rc<Term>),
    Closure(usize, Vec<Operand>), // Index into bodies, captured environment
}
