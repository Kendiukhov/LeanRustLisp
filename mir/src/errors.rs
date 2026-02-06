//! Structured error types for MIR analyses (ownership and borrow checking)

use crate::types::Region;
use crate::{BasicBlock, BorrowKind, Local, Place};
use std::collections::HashMap;
use std::fmt;

/// Source span information (copied from frontend)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub col: usize,
}

/// Source span information (optional, may not be available for MIR)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MirSpan {
    pub block: BasicBlock,
    pub statement_index: usize,
}

impl fmt::Display for MirSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "block {} statement {}",
            self.block.0, self.statement_index
        )
    }
}

pub type MirSpanMap = HashMap<MirSpan, SourceSpan>;

#[derive(Debug, Clone, Default)]
pub struct BorrowErrorContext {
    pub loan: Option<BorrowLoanContext>,
    pub region: Option<RegionConstraintChain>,
}

#[derive(Debug, Clone)]
pub struct BorrowLoanContext {
    pub place: Place,
    pub kind: BorrowKind,
    pub region: Region,
    pub issued_at: MirSpan,
    pub holder: Local,
}

#[derive(Debug, Clone)]
pub struct RegionConstraintChain {
    pub chain: Vec<Region>,
    pub live_at: MirSpan,
}

/// Ownership analysis errors
#[derive(Debug, Clone)]
pub enum OwnershipError {
    /// Use of a moved or uninitialized variable
    UseAfterMove {
        local: Local,
        location: Option<MirSpan>,
    },
    /// Copy of a non-Copy place
    CopyOfNonCopy {
        place: Place,
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
    UninitializedReturn { location: Option<MirSpan> },
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
            OwnershipError::CopyOfNonCopy { place, location } => {
                write!(f, "copy of non-Copy place: {:?}", place)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(
                    f,
                    "\n  help: move the value instead, or change its type to be Copy"
                )
            }
            OwnershipError::DoubleMoveInArgs { local, location } => {
                write!(
                    f,
                    "value used after move in same expression: local _{}",
                    local.0
                )?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: arguments are evaluated left-to-right; the value was moved by an earlier argument")
            }
            OwnershipError::OverwriteWithoutDrop { local, location } => {
                write!(
                    f,
                    "overwriting initialized linear value without drop: local _{}",
                    local.0
                )?;
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
                write!(
                    f,
                    "\n  help: ensure the return value is assigned on all code paths"
                )
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

impl OwnershipError {
    pub fn diagnostic_code(&self) -> &'static str {
        match self {
            OwnershipError::UseAfterMove { .. } => "M100",
            OwnershipError::CopyOfNonCopy { .. } => "M101",
            OwnershipError::DoubleMoveInArgs { .. } => "M102",
            OwnershipError::OverwriteWithoutDrop { .. } => "M103",
            OwnershipError::LinearNotConsumed { .. } => "M104",
            OwnershipError::UninitializedReturn { .. } => "M105",
            OwnershipError::UseUninitialized { .. } => "M106",
        }
    }

    pub fn location(&self) -> Option<MirSpan> {
        match self {
            OwnershipError::UseAfterMove { location, .. }
            | OwnershipError::CopyOfNonCopy { location, .. }
            | OwnershipError::DoubleMoveInArgs { location, .. }
            | OwnershipError::OverwriteWithoutDrop { location, .. }
            | OwnershipError::LinearNotConsumed { location, .. }
            | OwnershipError::UninitializedReturn { location }
            | OwnershipError::UseUninitialized { location, .. } => *location,
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
        context: BorrowErrorContext,
    },
    /// Cannot use value because it's borrowed
    UseWhileBorrowed {
        place: Place,
        borrow_kind: BorrowKind,
        location: Option<MirSpan>,
        context: BorrowErrorContext,
    },
    /// Cannot move out of a reference
    MoveOutOfRef {
        place: Place,
        location: Option<MirSpan>,
        context: BorrowErrorContext,
    },
    /// Reference escapes its scope (dangling reference)
    DanglingReference {
        borrowed_local: Local,
        location: Option<MirSpan>,
        context: BorrowErrorContext,
    },
    /// Returning a reference to a local variable
    EscapingReference {
        place: Place,
        location: Option<MirSpan>,
        context: BorrowErrorContext,
    },
    /// Cannot mutate through a shared reference
    MutateSharedRef {
        place: Place,
        location: Option<MirSpan>,
        context: BorrowErrorContext,
    },
    /// Cannot assign to borrowed place
    AssignWhileBorrowed {
        place: Place,
        location: Option<MirSpan>,
        context: BorrowErrorContext,
    },
    /// Internal invariant violation during borrow checking
    InternalInvariant {
        invariant: &'static str,
        evidence: String,
        location: Option<MirSpan>,
        context: BorrowErrorContext,
    },
}

impl BorrowError {
    pub fn diagnostic_code(&self) -> &'static str {
        match self {
            BorrowError::ConflictingBorrow { .. } => "M200",
            BorrowError::UseWhileBorrowed { .. } => "M201",
            BorrowError::MoveOutOfRef { .. } => "M202",
            BorrowError::DanglingReference { .. } => "M203",
            BorrowError::EscapingReference { .. } => "M204",
            BorrowError::MutateSharedRef { .. } => "M205",
            BorrowError::AssignWhileBorrowed { .. } => "M206",
            BorrowError::InternalInvariant { .. } => "M207",
        }
    }
}

impl fmt::Display for BorrowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BorrowError::ConflictingBorrow {
                place,
                existing_kind,
                requested_kind,
                location,
                context,
            } => {
                write!(
                    f,
                    "cannot borrow {:?} as {:?} because it is already borrowed as {:?}",
                    place, requested_kind, existing_kind
                )?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(
                    f,
                    "\n  help: consider restructuring to avoid overlapping borrows"
                )?;
                append_borrow_context(f, context)
            }
            BorrowError::UseWhileBorrowed {
                place,
                borrow_kind,
                location,
                context,
            } => {
                write!(
                    f,
                    "cannot use {:?} because it is borrowed as {:?}",
                    place, borrow_kind
                )?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(
                    f,
                    "\n  help: the borrow must end before the value can be used again"
                )?;
                append_borrow_context(f, context)
            }
            BorrowError::MoveOutOfRef {
                place,
                location,
                context,
            } => {
                write!(
                    f,
                    "cannot move out of {:?} which is behind a reference",
                    place
                )?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(
                    f,
                    "\n  help: consider using Clone, or restructuring to avoid the move"
                )?;
                append_borrow_context(f, context)
            }
            BorrowError::DanglingReference {
                borrowed_local,
                location,
                context,
            } => {
                write!(f, "borrowed value does not live long enough: local _{} dropped while still borrowed", borrowed_local.0)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(
                    f,
                    "\n  help: ensure the borrowed value outlives all references to it"
                )?;
                append_borrow_context(f, context)
            }
            BorrowError::EscapingReference {
                place,
                location,
                context,
            } => {
                write!(f, "cannot return reference to local variable {:?}", place)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(f, "\n  help: local variables are dropped when the function returns; return owned data instead")?;
                append_borrow_context(f, context)
            }
            BorrowError::MutateSharedRef {
                place,
                location,
                context,
            } => {
                write!(
                    f,
                    "cannot mutate {:?} which is behind a shared reference",
                    place
                )?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(
                    f,
                    "\n  help: use a mutable reference (&mut) to allow mutation"
                )?;
                append_borrow_context(f, context)
            }
            BorrowError::AssignWhileBorrowed {
                place,
                location,
                context,
            } => {
                write!(f, "cannot assign to {:?} because it is borrowed", place)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                write!(
                    f,
                    "\n  help: the borrow must end before the value can be assigned"
                )?;
                append_borrow_context(f, context)
            }
            BorrowError::InternalInvariant {
                invariant,
                evidence,
                location,
                context,
            } => {
                write!(f, "internal NLL invariant violated: {}", invariant)?;
                if let Some(loc) = location {
                    write!(f, " at {}", loc)?;
                }
                if !evidence.is_empty() {
                    write!(f, "\n  note: evidence: {}", evidence)?;
                }
                write!(
                    f,
                    "\n  help: this indicates a compiler bug; please report the issue"
                )?;
                append_borrow_context(f, context)
            }
        }
    }
}

impl BorrowError {
    pub fn location(&self) -> Option<MirSpan> {
        match self {
            BorrowError::ConflictingBorrow { location, .. }
            | BorrowError::UseWhileBorrowed { location, .. }
            | BorrowError::MoveOutOfRef { location, .. }
            | BorrowError::DanglingReference { location, .. }
            | BorrowError::EscapingReference { location, .. }
            | BorrowError::MutateSharedRef { location, .. }
            | BorrowError::AssignWhileBorrowed { location, .. }
            | BorrowError::InternalInvariant { location, .. } => *location,
        }
    }
}

impl std::error::Error for OwnershipError {}
impl std::error::Error for BorrowError {}

fn append_borrow_context(f: &mut fmt::Formatter<'_>, context: &BorrowErrorContext) -> fmt::Result {
    if context.loan.is_none() && context.region.is_none() {
        return Ok(());
    }

    if let Some(loan) = &context.loan {
        write!(
            f,
            "\n  note: loan issued at {} (place {}, kind {}, region {}, holder {})",
            loan.issued_at,
            format_place(&loan.place),
            format_borrow_kind(loan.kind),
            format_region(loan.region),
            format_local(loan.holder)
        )?;
    }

    if let Some(region) = &context.region {
        if region.chain.is_empty() {
            write!(f, "\n  note: region liveness could not be explained")?;
        } else if region.chain.len() == 1 {
            write!(
                f,
                "\n  note: region {} is live at {} (direct liveness requirement)",
                format_region(region.chain[0]),
                region.live_at
            )?;
        } else {
            let chain_str = format_region_chain(&region.chain);
            let root = region.chain[region.chain.len() - 1];
            write!(
                f,
                "\n  note: region {} is live at {} because {} ({} is required to be live here)",
                format_region(region.chain[0]),
                region.live_at,
                chain_str,
                format_region(root)
            )?;
        }
    }

    Ok(())
}

fn format_region(region: Region) -> String {
    format!("'{}", region.0)
}

fn format_region_chain(chain: &[Region]) -> String {
    chain
        .iter()
        .map(|region| format_region(*region))
        .collect::<Vec<_>>()
        .join(" >= ")
}

fn format_local(local: Local) -> String {
    format!("_{}", local.0)
}

fn format_borrow_kind(kind: BorrowKind) -> &'static str {
    match kind {
        BorrowKind::Shared => "Shared",
        BorrowKind::Mut => "Mut",
    }
}

fn format_place(place: &Place) -> String {
    let mut s = format_local(place.local);
    for elem in &place.projection {
        match elem {
            crate::PlaceElem::Deref => s = format!("(*{})", s),
            crate::PlaceElem::Field(i) => s = format!("{}.{}", s, i),
            crate::PlaceElem::Downcast(i) => s = format!("({} as variant#{})", s, i),
            crate::PlaceElem::Index(local) => s = format!("{}[{}]", s, format_local(*local)),
        }
    }
    s
}
