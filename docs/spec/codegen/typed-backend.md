# Typed Backend (Stage 1 + Phase 2 + Phase 3 Scaffolding)

This document defines the **Stage 1** supported subset for the typed MIR → Rust backend. The pipeline already enforces kernel/MIR typing/ownership/NLL; this document only constrains what the typed backend will accept and emit.

## Goals
- Emit **typed Rust** (enums/structs/functions), not the universal `Value` runtime.
- Preserve pre-codegen semantics for the supported subset.
- Avoid “tag-check panics” for supported programs.
- Deterministic output and stable naming.
- Support typed higher-order calls in the current subset.

## Current Supported Subset

### Types
- `Unit`, `Bool`, `Nat`
- ADTs (`MirType::Adt`) including parameterized forms (`Adt<T...>`)
  - Field types must themselves be Stage‑1 supported.
  - Direct self-recursion is allowed via `Box<...>` in Rust; mutual recursion is not supported yet.
- Prop inductives are runtime-erased:
  - any `MirType::Adt` whose inductive result sort is `Prop` lowers to `()`,
  - typed backend does not emit Rust enum definitions for these proof-only ADTs,
  - proof constructors lower to curried callables returning `()`.
- Type parameters (`MirType::Param`) lowered to deterministic Rust generic names (`T0`, `T1`, ...).
- References (`MirType::Ref`) lowered via typed wrappers:
  - `LrlRefShared<T>`
  - `LrlRefMut<T>`
- Raw pointers (`MirType::RawPtr`) lowered to `*const T` / `*mut T`.
- Interior mutability wrappers (`MirType::InteriorMutable`) lowered to:
  - `LrlRefCell<T>`
  - `LrlMutex<T>`
  - `LrlAtomic<T>`
- Index terms (`MirType::IndexTerm`) are accepted for typed codegen identity paths.
- Opaque MIR types (`MirType::Opaque`) are lowered to a typed placeholder wrapper (`LrlOpaque`).
- Functions of kind `Fn` and `FnOnce`:
  - Represented as `Rc<dyn LrlCallable<Arg, Ret>>` (curried, unary MIR functions).

### MIR Constructs
- Locals/temps with Stage‑1 types.
- `Rvalue::Use`, `Rvalue::Discriminant`, `Rvalue::Ref`.
- `Statement::Assign`, `RuntimeCheck`, `StorageLive/Dead`, `Nop`.
- `Terminator::Return`, `Goto`, `SwitchInt`, `Call`, `Unreachable`.
- Constructors as values (curried) for supported ADTs and builtins (`Nat`, `Bool`).
- Recursors (`Term::Rec`) with typed specialization entries.

### Control Flow
- Straight-line code and `SwitchInt` on discriminants (ADT/Bool/Nat).
- Place projections include `Field`, `Downcast`, `Deref`, and `Index` lowering.
- Executable typed indexing is supported for:
  - indexable ADTs with a singleton payload shape (`index == 0`),
  - indexable ADTs wrapping `List<T>` (delegates to typed list traversal).

### Functions & Closures
- Higher-order typed calls are supported in the current subset:
  - function values can be passed, returned, selected by `match`, and called.
  - calls are emitted as typed trait-object calls (`.call(...)`), with no dynamic function tag checks.
- Closure conversion strategy in this backend:
  - closure bodies are lifted to generated Rust functions,
  - lifted closures and fixpoints are materialized as generated adapter structs (`LrlClosureAdapter`, `LrlFixAdapter`) implementing `LrlCallable`,
  - captured values are stored in adapter struct fields (tuple-packed per closure literal).
- `FnMut` is not supported in typed backend.

## Explicitly Unsupported (Stage 1)
- Higher-order effects requiring mutable function state (`FnMut`).
- Executing polymorphic function values through the closure adapter path when the instantiated
  type arguments are not concretized in monomorphic local declarations.
- Executable indexing semantics for arbitrary custom container shapes.

## Backend Selection Behavior
- `--backend typed`: hard error on unsupported constructs with a clear diagnostic.
- `--backend auto`: try typed; on unsupported constructs, fall back to dynamic with a warning.
- `--backend dynamic`: always use dynamic backend.
- CLI defaults for `compile` and `compile-mir` use `--backend auto`.

## No Tag-Check Panics
For supported programs, emitted Rust must **not** include tag-check panics (e.g. “Expected Func”, “wrong tag”). Any remaining panic must be an intentional runtime check/helper path.

## Determinism
- Stable ordering of items (defs, ADTs, ctors).
- Stable symbol naming (sanitized names for Rust identifiers).
