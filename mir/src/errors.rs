//! Structured error types for MIR analyses (ownership and borrow checking)

use crate::{Local, Place, BasicBlock, BorrowKind};
use std::fmt;

/// Source span information (optional, may not be available for MIR)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MirSpan {
    pub block: BasicBlock,
    pub statement_index: usize,
}

impl fmt::Display for MirSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "block {} statement {}", self.block.0, self.statement_index)
    }
}

/// Ownership analysis errors
#[derive(Debug, Clone)]
pub enum OwnershipError {
    /// Use of a moved or uninitialized variable
    UseAfterMove {
        local: Local,
        location: Option<MirSpan>,
    },
    /// Double move of the same variable (e.g., in function arguments)
    DoubleMoveInArgs {
        local: Local,
        location: Option<MirSpan>,
    },
    /// Overwriting an initialized linear variable without proper drop
    OverwriteWithoutDrop {
        local: Local,
        location: Option<MirSpan>,
    },
    /// Linear variable dropped without being consumed
    LinearNotConsumed {
        local: Local,
        location: Option<MirSpan>,
    },
    /// Return value not initialized
    UninitializedReturn {
        location: Option<MirSpan>,
    },
    /// Use of uninitialized variable
    UseUninitialized {
        local: Local,
        location: Option<MirSpan>,
    },
}

impl fmt::Display for OwnershipError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OwnershipError::UseAfterMove { local, location } => {
                write!(f, "use of moved value: local _{}", local.0)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: value was moved earlier; consider using Clone or restructuring to avoid the move")
            }
            OwnershipError::DoubleMoveInArgs { local, location } => {
                write!(f, "value used after move in same expression: local _{}", local.0)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: arguments are evaluated left-to-right; the value was moved by an earlier argument")
            }
            OwnershipError::OverwriteWithoutDrop { local, location } => {
                write!(f, "overwriting initialized linear value without drop: local _{}", local.0)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: linear types must be consumed exactly once; drop or use the value before reassignment")
            }
            OwnershipError::LinearNotConsumed { local, location } => {
                write!(f, "linear value not consumed: local _{}", local.0)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: linear types must be consumed exactly once; the value went out of scope without being used")
            }
            OwnershipError::UninitializedReturn { location } => {
                write!(f, "return value not initialized")?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: ensure the return value is assigned on all code paths")
            }
            OwnershipError::UseUninitialized { local, location } => {
                write!(f, "use of uninitialized value: local _{}", local.0)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: ensure the variable is assigned before use")
            }
        }
    }
}

/// Borrow checking errors
#[derive(Debug, Clone)]
pub enum BorrowError {
    /// Cannot borrow as mutable because it's already borrowed
    ConflictingBorrow {
        place: Place,
        existing_kind: BorrowKind,
        requested_kind: BorrowKind,
        location: Option<MirSpan>,
    },
    /// Cannot use value because it's borrowed
    UseWhileBorrowed {
        place: Place,
        borrow_kind: BorrowKind,
        location: Option<MirSpan>,
    },
    /// Cannot move out of a reference
    MoveOutOfRef {
        place: Place,
        location: Option<MirSpan>,
    },
    /// Reference escapes its scope (dangling reference)
    DanglingReference {
        borrowed_local: Local,
        location: Option<MirSpan>,
    },
    /// Returning a reference to a local variable
    EscapingReference {
        place: Place,
        location: Option<MirSpan>,
    },
    /// Cannot mutate through a shared reference
    MutateSharedRef {
        place: Place,
        location: Option<MirSpan>,
    },
    /// Cannot assign to borrowed place
    AssignWhileBorrowed {
        place: Place,
        location: Option<MirSpan>,
    },
}

impl fmt::Display for BorrowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BorrowError::ConflictingBorrow { place, existing_kind, requested_kind, location } => {
                write!(f, "cannot borrow {:?} as {:?} because it is already borrowed as {:?}",
                    place, requested_kind, existing_kind)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: consider restructuring to avoid overlapping borrows")
            }
            BorrowError::UseWhileBorrowed { place, borrow_kind, location } => {
                write!(f, "cannot use {:?} because it is borrowed as {:?}", place, borrow_kind)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: the borrow must end before the value can be used again")
            }
            BorrowError::MoveOutOfRef { place, location } => {
                write!(f, "cannot move out of {:?} which is behind a reference", place)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: consider using Clone, or restructuring to avoid the move")
            }
            BorrowError::DanglingReference { borrowed_local, location } => {
                write!(f, "borrowed value does not live long enough: local _{} dropped while still borrowed", borrowed_local.0)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: ensure the borrowed value outlives all references to it")
            }
            BorrowError::EscapingReference { place, location } => {
                write!(f, "cannot return reference to local variable {:?}", place)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: local variables are dropped when the function returns; return owned data instead")
            }
            BorrowError::MutateSharedRef { place, location } => {
                write!(f, "cannot mutate {:?} which is behind a shared reference", place)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: use a mutable reference (&mut) to allow mutation")
            }
            BorrowError::AssignWhileBorrowed { place, location } => {
                write!(f, "cannot assign to {:?} because it is borrowed", place)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: the borrow must end before the value can be assigned")
            }
        }
    }
}

impl std::error::Error for OwnershipError {}
impl std::error::Error for BorrowError {}
