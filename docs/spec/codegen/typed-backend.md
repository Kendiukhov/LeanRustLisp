# Typed Backend Specification (Roadmap Phases 0-7)

This document defines the supported MIR -> Rust typed backend surface and fallback behavior. The pipeline already enforces kernel/MIR typing/ownership/NLL; this document constrains what the typed backend accepts/emits and records roadmap phase coverage.

## Goals
- Emit **typed Rust** (enums/structs/functions), not the universal `Value` runtime.
- Preserve pre-codegen semantics for the supported subset.
- Avoid “tag-check panics” for supported programs.
- Deterministic output and stable naming.
- Support typed higher-order calls in the current subset.

## Roadmap Coverage Status
- Phase -1: complete. Dynamic and typed backends both consume validated MIR in one pipeline.
- Phase 0: complete. `--backend typed|dynamic|auto` is implemented; `auto` falls back with explicit diagnostics.
- Phase 1: complete. Non-parameterized ADTs, constructors, matches, and projections emit as typed Rust.
- Phase 2: complete. Typed calls, lifted closures/fixpoints, and higher-order function paths are supported.
- Phase 3: complete. Parametric ADTs/functions, refs, raw pointers, interior mutability, index/runtime-check lowering are supported in typed codegen.
- Phase 4: complete. Proof terms are erased before codegen; Prop ADTs are runtime-erased in typed output.
- Phase 5: complete. Indexed/dependent lowering paths are implemented for the documented indexable/container shapes.
- Phase 6: complete. Typed prelude provides the effect/capability surface (`Comp`, `EvalCap`, `eval`) used by typed backend tests.
- Phase 7 (optional): complete. `compile` and `compile-mir` default to `--backend auto` (typed-first, dynamic fallback).
- Conformance coverage is documented in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/docs/dev/backend_conformance_subset.md` and `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/docs/dev/backend_conformance_report.md`.

## Current Supported Subset

### Types
- `Unit`, `Bool`, `Nat`
- ADTs (`MirType::Adt`) including parameterized forms (`Adt<T...>`)
  - Field types must themselves be supported by this backend.
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
- Locals/temps with supported types.
- `Rvalue::Use`, `Rvalue::Discriminant`, `Rvalue::Ref`.
- `Statement::Assign`, `RuntimeCheck`, `StorageLive/Dead`, `Nop`.
- `Terminator::Return`, `Goto`, `SwitchInt`, `Call`, `Unreachable`.
- Constructors as values (curried) for supported ADTs and builtins (`Nat`, `Bool`).
- Recursors (`Term::Rec`) with typed specialization entries.

### Control Flow
- Straight-line code and `SwitchInt` on discriminants (ADT/Bool/Nat).
- Place projections include `Field`, `Downcast`, `Deref`, and `Index` lowering.
- Executable typed indexing is supported for:
  - builtin `List<T>` traversal,
  - indexable ADTs with direct payload access (`index == 0`) even when payload is not the first field,
  - indexable ADTs whose payload field is another indexable/list container (delegates with `runtime_index`),
  - multi-variant indexable ADTs when at least one variant provides an index source field,
  - source-less indexable ADT shapes (compile successfully, with an explicit runtime panic path for index access).

### Functions & Closures
- Higher-order typed calls are supported in the current subset:
  - function values can be passed, returned, selected by `match`, and called.
  - calls are emitted as typed trait-object calls (`.call(...)`), with no dynamic function tag checks.
- Closure conversion strategy in this backend:
  - closure bodies are lifted to generated Rust functions,
  - lifted closures and fixpoints are materialized as generated adapter structs (`LrlClosureAdapter`, `LrlFixAdapter`) implementing `LrlCallable`,
  - captured values are stored in adapter struct fields (tuple-packed per closure literal).
- `FnMut` function-kind values are supported in typed backend call/lowering paths.
- Polymorphic function-value wrappers are supported through typed closure/fix adapters.

## Backend Selection Behavior
- `--backend typed`: hard error on unsupported constructs with a clear diagnostic.
- `--backend typed` + axioms:
  - default: reject axiom stubs,
  - with `--allow-axioms`: emit typed panic stubs and loud warnings.
- `--backend dynamic`: use dynamic backend.
- `--backend dynamic` + axioms:
  - default: reject executable axiom stubs,
  - with `--allow-axioms`: emit dynamic panic stubs and loud warnings.
- `--backend auto`:
  - no axiom stubs: try typed; on unsupported constructs, fall back to dynamic with a warning.
  - axiom stubs + no `--allow-axioms`: reject with an explicit opt-in diagnostic.
  - axiom stubs + `--allow-axioms`: prefer typed panic stubs; if typed is unsupported for other reasons, fall back to dynamic with warning.
- CLI defaults for `compile` and `compile-mir` use `--backend auto`.

## Axioms and Stub Safety
- **Axiom**: a declaration without a body (`def.value = None`) that cannot be executed directly.
- **Axiom stub**: generated Rust function used when an executable pipeline needs a runtime placeholder for an axiom.
- Typed stubs are emitted as typed panic stubs (return type inferred by call site), for example:
  - `fn some_axiom<T>() -> T { panic!(...) }`
- Dynamic stubs are emitted as `Value`-returning panic stubs.

Safety contract:
- Axioms are non-executable by default.
- Executable stubs require explicit `--allow-axioms` opt-in.
- When enabled, codegen emits loud warnings and writes artifact metadata (`build/output_<pid>_<nanos>.artifacts.json`) indicating executable axioms are present.
- If a runtime path reaches an axiom stub, execution will panic by design.

## Typed Unsupported Reason Codes
Typed-backend unsupported diagnostics use stable reason codes so fallback behavior can be tested and triaged deterministically.

- `TB001`: reserved legacy code (`FnMut` support gap; no longer emitted in current phase).
- `TB002`: Non-unary function shape encountered (typed backend currently supports unary-curried callables).
- `TB003`: Unsupported call operand form.
- `TB004`: Assignment to projected place is not supported.
- `TB005`: Unsupported place projection shape (malformed/non-lowerable projection path).
- `TB006`: Unsupported closure-environment projection shape.
- `TB007`: Unsupported closure type lowering.
- `TB008`: Unsupported fixpoint type lowering.
- `TB009`: reserved legacy code (polymorphic function-value support gap; no longer emitted in current phase).
- `TB900`: Internal typed-codegen invariant failure.

### Guard-Closure Status
- `TB001`: kept as a reserved stable code; former `FnMut` shape is supported and covered by direct typed-codegen tests.
- `TB002`: malformed/non-lowerable MIR guard (non-unary function shape); covered by direct typed-codegen tests.
- `TB003`: malformed/non-lowerable MIR guard (invalid call operand); covered by direct typed-codegen tests.
- `TB004`: malformed/non-lowerable MIR guard (assignment to projected place); covered by direct typed-codegen tests.
- `TB005`: malformed/non-lowerable MIR guard (unsupported place projection path); covered by direct typed-codegen tests.
- `TB006`: malformed/non-lowerable MIR guard (invalid closure env projection); covered by direct typed-codegen tests.
- `TB007`: malformed/non-lowerable MIR guard (closure literal/type mismatch); covered by direct typed-codegen tests.
- `TB008`: malformed/non-lowerable MIR guard (fixpoint literal/type mismatch); covered by direct typed-codegen tests.
- `TB009`: kept as a reserved stable code; former polymorphic function-value scenarios are supported in typed backend and covered by typed backend integration tests.
- `TB900`: internal invariant guard; indicates a backend bug or malformed MIR outside supported invariants.

## No Tag-Check Panics
For supported programs, emitted Rust must **not** include tag-check panics (e.g. “Expected Func”, “wrong tag”). Any remaining panic must be an intentional runtime check/helper path.

## Determinism
- Stable ordering of items (defs, ADTs, ctors).
- Stable symbol naming (sanitized names for Rust identifiers).
