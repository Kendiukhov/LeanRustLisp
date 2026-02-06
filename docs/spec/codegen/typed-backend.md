# Typed Backend (Stage 1 + Phase 2 Subset)

This document defines the **Stage 1** supported subset for the typed MIR → Rust backend. The pipeline already enforces kernel/MIR typing/ownership/NLL; this document only constrains what the typed backend will accept and emit.

## Goals
- Emit **typed Rust** (enums/structs/functions), not the universal `Value` runtime.
- Preserve pre-codegen semantics for the supported subset.
- Avoid “tag-check panics” for supported programs.
- Deterministic output and stable naming.
- Support typed higher-order calls in the current subset.

## Stage 1 Supported Subset

### Types
- `Unit`, `Bool`, `Nat`
- Non-parameterized ADTs (`MirType::Adt` with zero type args)
  - Field types must themselves be Stage‑1 supported.
  - Direct self-recursion is allowed via `Box<...>` in Rust; mutual recursion is not supported yet.
- Functions of kind `Fn` and `FnOnce`:
  - Represented as `Rc<dyn LrlCallable<Arg, Ret>>` (curried, unary MIR functions).

### MIR Constructs
- Locals/temps with Stage‑1 types.
- `Rvalue::Use`, `Rvalue::Discriminant`.
- `Statement::Assign`, `StorageLive/Dead`, `Nop`.
- `Terminator::Return`, `Goto`, `SwitchInt`, `Call`, `Unreachable`.
- Constructors as values (curried) for supported ADTs and builtins (`Nat`, `Bool`).
- Recursors (`Term::Rec`) for non‑parametric, non‑indexed inductives (used by `match` lowering).

### Control Flow
- Straight-line code and `SwitchInt` on discriminants (ADT/Bool/Nat).

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
- Parametric ADTs / generics (`List<A>`, `Option<A>`).
- `Ref`, `RawPtr`, `InteriorMutable` types or `Rvalue::Ref`.
- Runtime checks (`RuntimeCheckKind`) including bounds checks (indexing).
- Higher-order effects requiring mutable function state (`FnMut`).
- Indexed inductives (recursors requiring indices).
- MIR places with `Deref` or `Index` projections.

## Backend Selection Behavior
- `--backend typed`: hard error on unsupported constructs with a clear diagnostic.
- `--backend auto`: try typed; on unsupported constructs, fall back to dynamic with a warning.
- `--backend dynamic`: always use dynamic backend.

## No Tag-Check Panics
For supported programs, emitted Rust must **not** include tag-check panics (e.g. “Expected Func”, “wrong tag”). Any remaining panic must be an intentional runtime check; Stage 1 currently emits none.

## Determinism
- Stable ordering of items (defs, ADTs, ctors).
- Stable symbol naming (sanitized names for Rust identifiers).
