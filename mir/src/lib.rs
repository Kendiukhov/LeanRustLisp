use std::fmt;

pub mod analysis;
pub mod codegen;
pub mod errors;
pub mod lints;
pub mod lower;
pub mod pretty;
pub mod transform;
pub mod typed_codegen;
pub mod types;

#[cfg(test)]
mod snapshots;

use crate::types::{AdtLayoutRegistry, CtorId, MirType, Mutability};

// Id types for type safety
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BasicBlock(pub u32);

impl BasicBlock {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

impl From<usize> for BasicBlock {
    fn from(idx: usize) -> Self {
        BasicBlock(idx as u32)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Local(pub u32);

impl Local {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

impl From<usize> for Local {
    fn from(idx: usize) -> Self {
        Local(idx as u32)
    }
}

// A function body in MIR
#[derive(Debug, Clone)]
pub struct Body {
    pub basic_blocks: Vec<BasicBlockData>,
    pub local_decls: Vec<LocalDecl>,
    pub arg_count: usize,
    pub adt_layouts: AdtLayoutRegistry,
}

impl Body {
    pub fn new(arg_count: usize) -> Self {
        Body {
            basic_blocks: Vec::new(),
            local_decls: Vec::new(),
            arg_count,
            adt_layouts: AdtLayoutRegistry::default(),
        }
    }
}

#[derive(Clone)]
pub struct LocalDecl {
    pub ty: MirType, // Use MirType instead of Term
    pub name: Option<String>,
    pub is_prop: bool, // Optimization: Pre-computed universe level check
    pub is_copy: bool, // Whether this type has Copy semantics
    pub closure_captures: Vec<MirType>, // Types captured by a closure value in this local
}

impl LocalDecl {
    pub fn new(ty: MirType, name: Option<String>) -> Self {
        let is_copy = ty.is_copy();
        LocalDecl {
            ty,
            name,
            is_prop: false,
            is_copy,
            closure_captures: Vec::new(),
        }
    }

    // Deprecated helpers if needed, or updated
}

impl fmt::Debug for LocalDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LocalDecl")
            .field("ty", &self.ty)
            .field("name", &self.name)
            .field("is_prop", &self.is_prop)
            .field("is_copy", &self.is_copy)
            .finish()
    }
}

#[derive(Debug, Clone)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

#[derive(Debug, Clone)]
pub enum RuntimeCheckKind {
    RefCellBorrow { local: Local },
    MutexLock { local: Local },
    BoundsCheck { local: Local, index: Local },
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assign(Place, Rvalue),
    RuntimeCheck(RuntimeCheckKind),
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Return,
    Goto {
        target: BasicBlock,
    },
    SwitchInt {
        discr: Operand,
        targets: SwitchTargets,
    },
    Call {
        func: CallOperand,
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
    Index(Local),
}

impl From<Local> for Place {
    fn from(local: Local) -> Self {
        Place {
            local,
            projection: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Rvalue {
    Use(Operand),
    Ref(BorrowKind, Place),
    Discriminant(Place),
    // Aggregate(Box<AggregateKind>, Vec<Operand>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BorrowKind {
    Shared,
    Mut,
}

impl From<BorrowKind> for Mutability {
    fn from(k: BorrowKind) -> Self {
        match k {
            BorrowKind::Shared => Mutability::Not,
            BorrowKind::Mut => Mutability::Mut,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Box<Constant>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CallOperand {
    Operand(Operand),
    Borrow(BorrowKind, Place),
}

impl From<Operand> for CallOperand {
    fn from(operand: Operand) -> Self {
        CallOperand::Operand(operand)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Constant {
    pub literal: Literal,
    pub ty: MirType, // Use MirType
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Unit,     // Unit value
    Nat(u64), // For simplified constants
    Bool(bool),
    /// Reference to a top-level definition by name.
    GlobalDef(String),
    /// Entry-point recursor function for an inductive.
    Recursor(String),
    /// Unsupported constant payload. Backends must reject this explicitly.
    OpaqueConst(String),
    Closure(usize, Vec<Operand>), // Index into bodies, captured environment
    Fix(usize, Vec<Operand>),     // Recursive closure with self in env[0]
    // CtorId, full call arity, runtime payload arity (after erasing type-only args)
    InductiveCtor(CtorId, usize, usize),
}

impl Literal {
    pub fn capture_operands(&self) -> Option<&[Operand]> {
        match self {
            Literal::Closure(_, captures) | Literal::Fix(_, captures) => Some(captures),
            _ => None,
        }
    }
}
