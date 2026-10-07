# Ownership and Resource Model

This document outlines how LeanRustLisp integrates Rust-style ownership into a dependent type system.

## 1. Core Principle

**Affine Types**: a value whose type is not Copy is affine.
*   Usage: 0 or 1 times (moves); reads and borrows do not use it up.
*   Drop: Allowed (destructors run).
*   Copy: sorts, types, type families and proofs; `Ref Shared _`; and every inductive type whose
    Copy instance (derived structurally for every declaration, or explicit and `unsafe`) holds for
    its arguments. A declaration opts out of derivation with the `affine` marker:
    `(inductive (affine) Chan (sort 1) ...)` is never Copy, even if every field is.
    `(inductive copy ...)` turns a derivation failure into an error. Function types (other than
    proofs and type families), `Ref Mut _`, interior-mutable and affine inductives, opaque types
    and type variables are not Copy.

## 1.1 Copy Instances and Safety

Copy instances come from two sources:

*   **Derived**: the kernel attempts structural derivation for *every* inductive declaration (`Env::add_inductive` → `derive_copy_instance`); writing `(inductive copy ...)` only turns a derivation failure into an error. Derivation fails for interior-mutable inductives and for inductives marked `affine`. Otherwise the instance is parameterised by the type's uniform **parameters** only (`num_params`), and every constructor binder after the parameters is a runtime **field** — including binders that appear as index arguments of the constructor's result type (indices are not parameters, so such binders are stored). Each field must be Copy, expressed as a requirement over the parameters:
    *   a recursive field (the type itself applied to its parameters and any indices) adds no requirement: Copy-ness never depends on indices, so an indexed family such as `Vec A n` is Copy exactly when `A` is (like `List A`);
    *   for a field whose type is another inductive family, only that family's parameter arguments are kept;
    *   a field whose type depends on an earlier field in any other way, or a non-uniform recursive occurrence, makes derivation fail (the type is then not Copy).
*   **Explicit**: `(unsafe instance copy (pi ...))` registers a Copy instance. Explicit instances are always treated as unsafe axioms (recorded as `copy_instance(TypeName)` with the `unsafe` tag) and are rejected for interior-mutable inductives and for affine inductives (`K0052`).

Explicit instances take precedence over derived ones during Copy resolution.

Independently of instances, a type whose values are erased at run time is Copy
(`is_erased_type` in `kernel/src/checker.rs`): a sort, an arity `Pi ... -> Sort` (a type family),
or a proposition (a type whose type is `Prop`; its values are proofs). So a proof of a
proposition that stores a non-Copy witness is still duplicable.

### 1.2 The `affine` marker

`affine` reuses the inductive marker syntax (`(inductive (affine) Name Type ctors...)`, also
`(inductive (affine indexable) ...)`). It is built into the kernel (`TypeMarker::Affine`): unlike
`interior_mutable` or `indexable` it needs no prelude marker definition, adds no axiom
dependency, and only makes the ownership check stricter: no Copy instance is derived for the
type, an explicit Copy instance is rejected, and `(inductive copy (affine) ...)` is rejected
(`K0052`). The marker is also rejected (`K0052`) on an inductive in `Prop`: proofs are erased at
run time and always Copy, so the marker could not take effect. Affinity applies to values bound
to variables; a global definition is a constant (each reference denotes the definition's value
anew, as a Rust `const`), so `(def g Chan (mk_chan 3))` may be referenced more than once. Example: with `(inductive (affine) Chan (sort 1) (ctor mk_chan (pi id Nat Chan)))`,
`(lam c Chan (mk_cp c c))` is rejected with
`K0021 ... [UseAfterMove]: variable 'c' is used after it was moved`; without the marker `Chan`
is Copy and the same definition is accepted.

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

Borrowing is not moving: in the kernel's ownership walk the argument of `borrow_shared` is a
*read* and the argument of `borrow_mut` a *mutable use* of the variable (§6.2). Both require that
the variable has not been moved, and neither moves it. Whether a move happens while a loan is
still live (`M201`), and whether loans conflict (`M200`) or outlive their referent (`M203`), is
decided by the MIR borrow checker alone.

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
A *signature* is a complete chain of `pi`s (all the arguments of a curried
function type, up to its final result); the rule is checked once per chain, not
for each curried suffix. Each unlabeled input reference counts as a lifetime of
its own. So `(pi a (Ref Shared Nat) (pi n Nat (Ref Shared Nat)))` (one input
lifetime, the reference first) is accepted like `(pi n Nat (pi a (Ref Shared Nat)
(Ref Shared Nat)))`, while two unlabeled input references, or none, with an
unlabeled result are rejected (`F0208` in the elaborator, `K0045` in the kernel).
A `pi` appearing as an argument type or inside the result is a signature of its own.

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

## 6.2 Kernel ownership check (trusted)

`Env::add_definition` runs an affine ownership walk over every definition value
(`check_ownership_in_term` in `kernel/src/checker.rs`; top-level expressions are submitted the
same way by the CLI driver). Violations are `K0021` errors that name the variable
(`Ownership violation [UseAfterMove]: variable 'k' is used after it was moved`).

**State.** The walk threads a stack with one entry per variable in scope: whether it is Copy,
whether it is an implicit binder, and whether it has been *moved*. A *repetition barrier* marks
the start of a scope that may run more than once.

**Erased positions.** A subterm is *erased* — not evaluated at run time, no ownership effect at
all, allowed even after a move — if it is a type, a type family or a proof. Concretely: binder
types of `lam`/`let`/`fix`, every `pi` type, a `let` value whose declared type is erased, an
argument whose expected domain is erased (a sort, an arity, or a proposition: type arguments and
proof arguments), an application whose own type is erased (e.g. `Eq A x y`, or a lemma
`cong ... e`), and the parameters, motive and indices of a recursor application (plus its minor
premises, major premise and extra arguments when their domains are erased, e.g. an elimination
into `Prop`). Erased subterms are skipped by the walk.

**Uses of a variable in a runtime position.**

*   *move* (consume): the variable as a value (argument, constructor field, `let` value, result),
    or the head of a call of an `FnOnce` function;
*   *read*: the head of a call of an `Fn` function, the argument of `borrow_shared`;
*   *mutable use*: the head of a call of an `FnMut` function, the argument of `borrow_mut`.

For a Copy variable every use is allowed. For a non-Copy variable every use requires that it has
not been moved (`UseAfterMove`); a move marks it moved; a move of a variable bound outside the
innermost repetition barrier is `ConsumedInRepeatedScope`. A move or mutable use of an implicit
binder of non-Copy type is `ImplicitNonCopyUse`.

**Closures.** In `lam^k x:A. t` (kind `k`), a use in mode `m` of a variable bound outside the
lambda counts as `min(m, capmode(k))`, where `capmode(Fn) = read`, `capmode(FnMut) = mutable
use`, `capmode(FnOnce) = move` (an `Fn` closure only reads what it captures, so a move inside an
`Fn` closure body is a read of the captured variable; the kind check below rejects the closure
if it really moves a non-Copy capture). The body is walked in the same state, so moves inside a
closure body are moves of the captured variables at the point where the closure is built.

**Applications.** `h a1 ... an`: the head is used first — a variable head according to the kind
of its type's first `pi`, a compound head is evaluated (walked as a value) — then the arguments
left to right, skipping erased ones. `borrow_shared {A} x` / `borrow_mut {A} x` with a variable
`x` read / mutably use `x`; a compound argument is evaluated (moved) as a temporary.

**`let x : A = v; t`**: `v` (unless erased), then `t` with `x` pushed (Copy iff `A` is Copy).

**Recursors** `Rec_I params motive minors indices major extra...`. The application must supply
the motive and all minor premises in place (`RecursorWithoutMinorPremises`; minor premises
passed later through a variable could not be checked). Parameters, motive and indices are
erased.

*   `I` *non-recursive* (no constructor has a field of type `I ...`) and the application
    *saturated* (the major premise is supplied): exactly one minor premise runs, after the major
    premise is evaluated (also the order of MIR's inline lowering). The major premise is walked
    first; then every minor premise is walked from the same state, and the moved sets are joined
    (a variable is moved after the elimination if some branch moved it). So
    `(match b T (case (true) (close c)) (case (false) (finish c)))` is accepted, and a use of `c`
    after the match is rejected.
*   `I` *recursive*, or the application *unsaturated* (applied without its major premise, for any
    `I`): the arguments are walked left to right (minor premises are built as values before any
    dispatch: as closures before the major premise is evaluated, as in MIR, or held by the
    function value that an unsaturated application returns). A minor premise is *repeatable* if
    the application is unsaturated, or `I` is branching (some constructor has two or more
    recursive fields), or its constructor has a recursive field. So for an unsaturated
    application every minor premise is repeatable, also for a non-recursive `I`: in
    `((rec Bool) (lam z Bool Nat) (burn k) (burn k))` both field-less cases are evaluated when
    the partial application is built, and the second `(burn k)` is a use after move (`K0021`
    `UseAfterMove`), whereas the saturated `((rec Bool) (lam z Bool Nat) (burn k) (burn k) b)`
    is accepted. (An unsaturated recursor is in any case rejected later by lowering,
    "Partially applied recursor".) A repeatable minor premise of a
    constructor with fields must be a lambda (or a global constant / constructor;
    `RepeatedMinorNotLambda`) and is walked under a repetition barrier, so it may not move
    non-Copy variables bound outside it (`ConsumedInRepeatedScope`); a repeatable minor premise
    of a field-less constructor is the value returned for every occurrence of the constructor
    and must be Copy (`RepeatedMinorValueNotCopy`). Other minor premises (the base case of a
    linear recursion) may move outer variables.
*   Inside a minor premise the fields are pushed as variables; a recursive field of non-Copy type
    starts out *moved*, because the recursor computes the induction hypotheses eagerly and so
    consumes the field before the minor premise runs (`RecursiveFieldConsumedByIh`); such fields
    must be bound by lambdas (`MinorMustBindRecursiveField`).

**Fixpoints.** `fix f:T. t` walks `t` under a repetition barrier (the body runs once per
recursive call).

**Function kinds** (`K0043`, checked when the kernel infers the type of every `lam`). The
*uses* of the variables free in a lambda body are computed by one stateless analysis that uses
the same positions as the walk (`term_variable_uses`): erased occurrences and reads count as
`read`, then `mutable use`, then `move`, taking the strongest use and applying the closure
downgrade above for nested lambdas. A captured variable is *moved into* the closure if it is not
Copy and its use is `move` (a moved `Ref Mut` is a mutable use), *mutably borrowed* if its use
is `mutable use` and it is not Copy, and *read* otherwise (a Copy capture is always read: the
closure works on its own copy). The required kind is `FnOnce` if some capture is moved, else
`FnMut` if some capture is mutably borrowed, else `Fn`, and `lam^k` is accepted iff the required
kind is at most `k` (`Fn < FnMut < FnOnce`). The elaborator stamps lambdas with the kind
computed by this same analysis (`analyze_closure_captures`), and MIR lowering uses it for the
capture modes it requires, so the three components agree; the elaborator falls back to a
syntactic approximation only for terms the kernel cannot type yet.

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
- **Borrow and call of a moved value**: a shared or mutable borrow (`Rvalue::Ref`), a discriminant read, or a call of a
  function value that has been moved is a use after move (function values moved by an assignment or an argument are
  tracked; a function value moved into a closure's environment because the closure only calls it is not)
- **Affine, not linear**: a non-Copy value may be dropped without being consumed (used *at most* once); no check
  requires consumption. `M104` (`LinearNotConsumed`) is defined in `mir/src/errors.rs` but no analysis reports it
- **Return initialization**: Verifies return value is initialized on all paths

**Copy type detection:**
MIR asks the kernel (`is_copy_type_in_env` / `is_copy_type_in_ctx`, §1): sorts, erased types
(type families, propositions), `Ref Shared _`, and inductive types with a Copy instance whose
requirements hold. A local whose type is a proposition (`LocalDecl::is_prop`) is Copy unless its
MIR type is a function, closure or opaque type. Function values are non-Copy by default; capture
information currently affects call mode, not Copy. MIR's own checks (typing and ownership) decide
whether a field projected out of a non-Copy value may be copied with the same Copy instances,
translated to MIR types when the layouts are built (`AdtLayout::copy_requirements`,
`AdtLayoutRegistry::type_is_copy` in `mir/src/types.rs`): a `List Nat` field of an `affine` value
may be copied out of it, an affine field may not.

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
