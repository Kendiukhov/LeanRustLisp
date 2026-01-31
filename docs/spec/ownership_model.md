# Ownership and Resource Model

This document outlines how LeanRustLisp integrates Rust-style ownership into a dependent type system.

## 1. Core Principle

**Affine Types**: Values are affine by default.
*   Usage: 0 or 1 times.
*   Drop: Allowed (destructors run).
*   Copy: Opt-in via `is_copy` metadata on inductive type declarations.

## 2. Borrowing & References

Borrowing produces references with explicit lifetimes (regions):

*   **Shared Reference**: `&'ρ A`
    *   Read-only access.
    *   Copyable (unrestricted).
*   **Unique Reference**: `&'ρ mut A`
    *   Read-write access.
    *   **Linear capability**: Cannot be aliased. Must be used linearly to preserve the ability to mutate.

## 3. Lifetimes at the Type Level

*   Lifetimes (`'ρ`) are first-class terms at the type level.
*   They are **not** value-dependent at runtime (erased).
*   The compiler implies a partial order (outlives relation) on regions.
*   **Verification**: A constraint solver runs on the mid-level IR (LRL-MIR) and generates evidence or checkable constraints for the kernel (or acts as a trusted oracle if split logic is used).

## 4. Mutation & Dependent Types

Systems programming wants in-place mutation, but dependent types need type stability.

*   **Rule**: `&mut T` preserves the type `T`. You cannot change the index of a dependently typed value in-place behind a reference if the index determines the type.
    *   *Example*: You cannot mutate a `Vec A n` into a `Vec A (n+1)` in-place via a simple `&mut` reference because the type changes.
*   **State Replacement**: To change type indices, you must take ownership and return a new value.
*   **Existential Packaging**: For mutable containers with dynamic size:
    ```lisp
    (structure Buffer (A : Type)
      (n : Nat)
      (data : Vec A n))
    ```
    The `n` is hidden; mutating the buffer updates `n` internally.

## 5. Safe Concurrency

*   **Contract**: Safe code implies no Data Races and no UB.
*   **Send/Sync**: Modeled as typeclass predicates derived/verified by the compiler.
*   **Primitives**: Mutexes, RwLocks, and Channels use ownership transfer to ensure safety.

---

## 6. Implementation: MIR-Based Analysis

The ownership and borrow checking is implemented in the `mir` crate as a dataflow analysis over the Mid-level Intermediate Representation (MIR).

### 6.1 Architecture

```
kernel::Term (typed AST)
     │
     ▼
mir::lower::MirLowerer
     │  Lowers Term to MIR Body (basic blocks, statements, terminators)
     ▼
mir::Body
     │
     ├──► mir::analysis::ownership::OwnershipAnalysis
     │         Tracks initialization state per local
     │
     └──► mir::analysis::borrow::BorrowChecker
               Tracks active loans and reference conflicts
```

### 6.2 Ownership Analysis (`mir/src/analysis/ownership.rs`)

Tracks the state of each local variable through program execution:

```rust
enum LocalState {
    Uninitialized,  // Never assigned or after StorageDead
    Initialized,    // Has a valid value
    Moved,          // Value has been moved out
}
```

**Key checks performed:**
- **Use after move**: Detects when a moved value is used again
- **Double move in arguments**: Catches same value moved multiple times in a call
- **Uninitialized use**: Prevents reading uninitialized locals
- **Linear type consumption**: Ensures linear (non-Copy) types are consumed exactly once
- **Return initialization**: Verifies return value is initialized on all paths

**Copy type detection:**
Types are considered Copy if:
- They are `Sort` (types themselves)
- They are `Pi` types (function types)
- They are inductive types with `is_copy: true` metadata

```rust
fn is_type_copy(&self, ty: &Rc<Term>) -> bool {
    match &**ty {
        Term::Sort(_) => true,
        Term::Pi(_, _, _) => true,
        Term::Ind(name, _) => {
            self.kernel_env.inductives.get(name)
                .map(|decl| decl.is_copy)
                .unwrap_or(false)
        },
        _ => false
    }
}
```

### 6.3 Borrow Checking (`mir/src/analysis/borrow.rs`)

Tracks active loans (borrows) and detects conflicts:

```rust
struct Loan {
    place: Place,       // What is borrowed
    kind: BorrowKind,   // Shared or Mut
    block: BasicBlock,  // Where the borrow occurred
}

enum BorrowKind {
    Shared,  // &T - multiple allowed
    Mut,     // &mut T - exclusive
}
```

**Key checks performed:**
- **Conflicting borrows**: Cannot have `&mut` while any other borrow exists
- **Use while borrowed**: Cannot move/modify a borrowed value
- **Move out of reference**: Cannot move out from behind a reference
- **Dangling references**: Borrowed value must outlive all references
- **Escaping references**: Cannot return references to local variables
- **Mutate through shared ref**: Cannot write through `&T`

### 6.4 Structured Error Types (`mir/src/errors.rs`)

Errors include source location information via `MirSpan`:

```rust
struct MirSpan {
    block: BasicBlock,
    statement_index: usize,
}

enum OwnershipError {
    UseAfterMove { local: Local, location: Option<MirSpan> },
    DoubleMoveInArgs { local: Local, location: Option<MirSpan> },
    OverwriteWithoutDrop { local: Local, location: Option<MirSpan> },
    LinearNotConsumed { local: Local, location: Option<MirSpan> },
    UninitializedReturn { location: Option<MirSpan> },
    UseUninitialized { local: Local, location: Option<MirSpan> },
}

enum BorrowError {
    ConflictingBorrow { place, existing_kind, requested_kind, location },
    UseWhileBorrowed { place, borrow_kind, location },
    MoveOutOfRef { place, location },
    DanglingReference { borrowed_local, location },
    EscapingReference { place, location },
    MutateSharedRef { place, location },
    AssignWhileBorrowed { place, location },
}
```

Error messages include helpful suggestions:
```
use of moved value: local _1 at block 0 statement 2
  help: value was moved earlier; consider using Clone or restructuring to avoid the move
```

### 6.5 Copy Type Metadata

Inductive types can be marked as Copy via the `is_copy` field in `InductiveDecl`:

```rust
// kernel/src/ast.rs
struct InductiveDecl {
    name: String,
    univ_params: Vec<String>,
    num_params: usize,
    ty: Rc<Term>,
    ctors: Vec<Constructor>,
    is_copy: bool,  // Whether values of this type can be freely copied
}

impl InductiveDecl {
    fn new(name, ty, ctors) -> Self { /* is_copy: false */ }
    fn new_copy(name, ty, ctors) -> Self { /* is_copy: true */ }
}
```

This metadata is propagated to MIR locals via `LocalDecl::is_copy`, enabling the ownership analysis to distinguish between linear and freely-copyable types.

### 6.6 Integration Points

**Lowering (`mir/src/lower.rs`):**
- Converts kernel `Term` to MIR `Body`
- Looks up `is_copy` from kernel environment for each local
- Generates `Move` vs `Copy` operands based on type

**Compilation (`cli/src/compiler.rs`):**
- After MIR lowering, runs ownership and borrow analysis
- Reports structured errors with location information
- Only proceeds to codegen if analyses pass
