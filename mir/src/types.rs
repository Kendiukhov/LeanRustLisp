#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtId(pub String);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Region(pub usize);

impl Region {
    pub const STATIC: Region = Region(0); // Reserve 0 for static/global?
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Not,
    Mut,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MirType {
    Unit,
    Bool,
    Nat,
    /// Inductive type (Name, Generic Args)
    /// Note: Value arguments (indices) are currently erased or not represented in type identity
    /// for simplified borrowing. Ideally they should be distinct types if they affect layout.
    Adt(AdtId, Vec<MirType>),
    /// Reference: &'region mut? T
    Ref(Region, Box<MirType>, Mutability),
    /// Function / Closure: [Args] -> Ret
    Fn(Vec<MirType>, Box<MirType>),
    /// Raw pointer (for unsafe/primitives)
    RawPtr(Box<MirType>, Mutability),
    /// Interior Mutability wrapper (RefCell, Mutex, Atomic)
    InteriorMutable(Box<MirType>, IMKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IMKind {
    RefCell, // Panics on dynamic borrow violation
    Mutex,   // Blocks or waits, safe for concurrency
    Atomic,  // Hardware atomics
}

impl MirType {
    pub fn is_copy(&self) -> bool {
        match self {
            MirType::Unit | MirType::Bool | MirType::Nat => true,
            MirType::Ref(_, _, Mutability::Not) => true, // &T is Copy
            MirType::Ref(_, _, Mutability::Mut) => false, // &mut T is not Copy
            MirType::RawPtr(_, _) => true,
            MirType::Adt(_, _) => false, // Conservative default, needs lookup
            MirType::Fn(_, _) => false, // Closures move env? FnPtr is copy.
            MirType::InteriorMutable(_, _) => false, // Usually not Copy (RefCell/Mutex are not)
        }
    }
}
