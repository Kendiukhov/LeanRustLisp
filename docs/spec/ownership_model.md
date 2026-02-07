# Ownership and Resource Model

This document outlines how LeanRustLisp integrates Rust-style ownership into a dependent type system.

## 1. Core Principle

**Affine Types**: Values are affine by default.
*   Usage: 0 or 1 times.
*   Drop: Allowed (destructors run).
*   Copy: Opt-in via derived Copy instances on inductives (surface syntax: `(inductive copy ...)`). Explicit Copy instances are permitted only under `unsafe` and are tracked as unsafe axioms.

## 1.1 Copy Instances and Safety

Copy instances come from two sources:

*   **Derived**: `(inductive copy ...)` requests derivation. The kernel checks that the inductive is not interior-mutable and that all constructor fields are Copy (or depend only on parameters). If derivation fails and `copy` was requested, the declaration is rejected.
*   **Explicit**: `(unsafe instance copy (pi ...))` registers a Copy instance. Explicit instances are always treated as unsafe axioms (recorded as `copy_instance(TypeName)` with the `unsafe` tag) and are rejected for interior-mutable inductives.

Explicit instances take precedence over derived ones during Copy resolution.

## 2. Borrowing & References

Borrowing produces references with explicit lifetimes (regions):

*   **Shared Reference**: `&'ρ A`
    *   Read-only access.
    *   Copyable (unrestricted).
*   **Unique Reference**: `&'ρ mut A`
    *   Read-write access.
    *   **Linear capability**: Cannot be aliased. Must be used linearly to preserve the ability to mutate.

At the core, references are expressed via the reserved primitives `Ref`, `Shared`, and `Mut`
(e.g., `Ref Shared A`, `Ref Mut A`). These names are reserved by the kernel and must have fixed
prelude-defined signatures; user code may not redefine them.

Surface `&`/`&mut` desugar to the reserved primitives `borrow_shared` and `borrow_mut`. These
primitives are admitted by the kernel as total axioms with fixed signatures. Their safety
contract is enforced by the MIR borrow checker (outside the TCB), so safe code may borrow without
an explicit `unsafe` marker.

## 3. Lifetimes at the Type Level

*   Lifetimes (`'ρ`) are first-class terms at the type level.
*   They are **not** value-dependent at runtime (erased).
*   The compiler implies a partial order (outlives relation) on regions.
*   **Verification**: A constraint solver runs on the mid-level IR (LRL-MIR) and generates evidence or checkable constraints for the kernel (or acts as a trusted oracle if split logic is used).

### 3.1 Lifetime Labels and Elision (Function Types)

Function *types* may label reference lifetimes by attaching an attribute to
`Ref` in the signature. The label becomes a named region parameter; reusing the
same label ties lifetimes together.

Core/surface form:
```
Ref #[label] Shared T
Ref #[label] Mut T
```

Implementation note: lifetime labels are carried structurally on the core `Ref`
application node (not in side tables) and are preserved through term
transformations (`shift`, `subst`, WHNF). Labels participate in definitional
equality (label-strict); see `docs/spec/mir/borrows-regions.md` §Call-Site Region Constraints.

Example (return tied to the first argument):
```
(pi a (Ref #[a] Shared Nat)
  (pi b (Ref #[b] Shared Nat)
    (Ref #[a] Shared Nat)))
```

Elision rule (Rust-style): if a signature contains exactly one distinct
reference lifetime among its inputs, unlabeled return references are assigned
that lifetime. Otherwise, return references must be explicitly labeled.

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

## 6. Functions and Closure Kinds

Function values carry an explicit kind (`Fn`, `FnMut`, `FnOnce`) that controls
call semantics and ownership. See `docs/spec/function_kinds.md` for details.

*   **Fn** calls use a shared borrow of the closure environment.
*   **FnMut** calls use a mutable borrow of the closure environment.
*   **FnOnce** calls consume the closure environment.
*   Function values are non-Copy by default.
*   MIR lowering may mark a closure value Copy-by-clone when all captured
    values are Copy, enabling safe duplication of reusable closure adapters.

### 6.1 Implicit binders (observational-only)

Implicit binders (`{x}`) are for inference and erasure, not for consuming
resources. For ownership soundness:

*   Implicit **value** binders may only be used observationally at runtime:
    read or copy, but never move, mutably borrow, or store in non-Copy
    positions.
*   Using an implicit value in a consuming position is a kernel error.
*   If you need to consume a value, make the binder explicit.

---

## 7. Implementation: MIR-Based Analysis

The ownership and borrow checking is implemented in the `mir` crate as a dataflow analysis over the Mid-level Intermediate Representation (MIR).

### 7.1 Architecture

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

### 7.2 Ownership Analysis (`mir/src/analysis/ownership.rs`)

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
- They are inductive types with a resolved Copy instance whose requirements are Copy (derived or explicit)
- Function types (`Pi`) are never Copy
Function values are non-Copy by default; capture information currently affects
call mode, not Copy.

```rust
fn is_copy_type(&self, ty: &Rc<Term>) -> bool {
    match whnf(ty) {
        Term::Sort(_) => true,
        Term::Pi(_, _, _, _) => false,
        Term::Ind(name, args) => copy_instance_satisfiable(name, args),
        _ => false,
    }
}
```

### 7.3 Borrow Checking (`mir/src/analysis/borrow.rs`)

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

### 7.4 Structured Error Types (`mir/src/errors.rs`)

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

### 7.5 Copy Type Metadata

Inductive types can request derived Copy via the `is_copy` field in `InductiveDecl`.
This is a derivation request; the kernel attempts to build a Copy instance and
rejects the inductive if derivation fails. Explicit Copy instances are stored
separately and treated as unsafe axioms.

```rust
// kernel/src/ast.rs
struct InductiveDecl {
    name: String,
    univ_params: Vec<String>,
    num_params: usize,
    ty: Rc<Term>,
    ctors: Vec<Constructor>,
    is_copy: bool,  // Whether Copy derivation was explicitly requested
    markers: Vec<TypeMarker>,
    axioms: Vec<String>,
}

impl InductiveDecl {
    fn new(name, ty, ctors) -> Self { /* is_copy: false */ }
    fn new_copy(name, ty, ctors) -> Self { /* is_copy: true */ }
}
```

Resolved Copy instances (derived or explicit) are propagated to MIR locals via
`LocalDecl::is_copy`, enabling the ownership analysis to distinguish between
linear and freely-copyable types.

### 7.6 Integration Points

**Lowering (`mir/src/lower.rs`):**
- Converts kernel `Term` to MIR `Body`
- Resolves Copy via kernel Copy-instance checking for each local
- Generates `Move` vs `Copy` operands based on type

**Compilation (`cli/src/compiler.rs`):**
- After MIR lowering, runs ownership and borrow analysis
- Reports structured errors with location information
- Only proceeds to codegen if analyses pass
