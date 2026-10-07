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
  - Direct self-recursion is allowed: a directly recursive field is shared, `Rc<...>` in Rust
    (LRL data is immutable, so sharing is not observable). Cloning a value therefore copies one
    node, not the whole structure; moving a recursive field out of an owned node
    (`lrl_unshare`) copies the node only if it is still shared. (The fields used to be
    `Box<...>`, and every clone of a value -- each field projection and each step of a
    recursor -- copied the whole structure, which made structural recursion over a list
    quadratic.) Mutual recursion is not supported yet.
- Prop inductives are runtime-erased:
  - any `MirType::Adt` whose inductive result sort is `Prop` lowers to `()`,
  - typed backend does not emit Rust enum definitions for these proof-only ADTs,
  - proof constructors lower to curried callables returning `()`.
- Type parameters (`MirType::Param`) lowered to deterministic Rust generic names (`T0`, `T1`, ...).
  A closure function (and its adapter) is generic only over the parameters that occur in its
  Rust signature (return, argument and capture types); a parameter that occurs only inside a
  Prop inductive (rendered `()`) is not a generic parameter, since rustc could not infer it where
  the closure is created (e.g. the capture-free proof closures inside a generic `cong`).
- References (`MirType::Ref`) lowered via typed wrappers:
  - `LrlRefShared<T>`
  - `LrlRefMut<T>`
- Raw pointers (`MirType::RawPtr`) lowered to `*const T` / `*mut T`.
- Interior mutability wrappers (`MirType::InteriorMutable`) lowered to:
  - `LrlRefCell<T>`
  - `LrlMutex<T>`
  - `LrlAtomic<T>`
- Indexed families carry no index in their MIR type (indices are erased, value parameters are `Unit`; see `docs/spec/mir/typing.md`), so `Vec A n` is emitted as the Rust type of `Vec<A>`.
  A constructor function still receives every parameter: a type parameter as `()`, a value
  parameter (e.g. `k : Nat` in `(inductive NBox (pi k Nat (sort 1)) ...)`, or the uniform
  `n` of a channel `Chan n`) with the Rust type of its own type (`u64`), as call sites pass it
  (it used to be declared `()`, and rustc rejected the call with `E0308`).
- Opaque MIR types (`MirType::Opaque`) are lowered to the uniform boxed representation
  `LrlOpaque` (see "Values of Types Computed at Run Time" below).
- Functions of kind `Fn` and `FnOnce`:
  - Represented as `Rc<dyn LrlCallable<Arg, Ret>>` (curried, unary MIR functions).

### MIR Constructs
- Locals/temps with supported types.
- `Rvalue::Use`, `Rvalue::Discriminant`, `Rvalue::Ref`.
- `Statement::Assign`, `RuntimeCheck`, `StorageLive/Dead`, `Nop`.
- `Terminator::Return`, `Goto`, `SwitchInt`, `Call`, `Unreachable`.
- Constructors as values (curried) for supported ADTs and builtins (`Nat`, `Bool`).
- Recursors (`Term::Rec`) with typed specialization entries (one Rust entry/implementation
  pair per distinct MIR type of the recursor at its use sites). A specialization whose motive
  is a large elimination is emitted with a uniform boxed signature (next section).

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

## Values of Types Computed at Run Time

Some LRL types cannot be computed statically: the type of a value produced by a *large
elimination* -- a recursor whose motive returns a type, e.g. a total `head` on `Vec A (succ n)`
whose motive is `Unit` at index `zero` and `A` at `succ` -- depends on an index that is only
known at run time, and an application of a type-family variable (`P y`) is stuck. MIR lowering
gives such a type the MIR type `Opaque`; the typed backend represents every value of an
`Opaque` type uniformly as `LrlOpaque`, a box holding the value (`Rc<dyn Any>`) together with
the name of its Rust type:
- `LrlOpaque::wrap::<T>(v)` boxes a value of Rust type `T` (a value that is already boxed is
  not boxed again);
- `LrlOpaque::unwrap::<T>(b)` unboxes it with a *checked* downcast: if the box does not hold a
  `T`, the program panics with a message naming both types (it never reinterprets memory).

**Recursors of large eliminations.** The emitted recursor returns the value of the minor
premise selected by the major premise's constructor and passes induction hypotheses to the minor
premises, so it is well typed in Rust only if every minor premise's result, every induction
hypothesis and the recursor's result have the same Rust type. That holds for a constant motive,
but not for a large elimination (in `head`, the `vnil` minor returns `Unit`, the `vcons` minor
returns `A`, and the induction hypothesis has the `Opaque` type `motive n t`); such
specializations used to fail rustc with `E0308`. For them, every motive value is given the
uniform type `LrlOpaque`: the entry function is emitted with minor premises returning
`LrlOpaque`, induction hypotheses of type `LrlOpaque` and result `LrlOpaque`, and the reference
to the recursor at its use site is adapted to the use site's types by a conversion generated
from the two MIR types (`coerce_expr`): each minor premise's result is boxed, induction
hypotheses are unboxed where the minor expects a known type, and the recursor's result is
unboxed at the use site's result type. Function values are converted by wrapping them in a
closure that converts their argument and result. A recursor specialization whose motive is
constant is emitted as before.

**Why the downcasts succeed (soundness argument).** The kernel has type-checked the program, so
at run time the value delivered at an unboxing point has an LRL type definitionally equal to
the type known there. Boxing and unboxing happen only at types that contain no `Opaque`
position (*fully known* types); the Rust type of a fully known LRL type is determined by its
head constructors and type arguments (indices and proofs are erased, see
`docs/spec/mir/typing.md`), so two definitionally equal fully known types have the same Rust
type, and the downcast at an unboxing point finds the type that was boxed. A conversion that
would have to box or unbox a *partially* known type (e.g. `List<LrlOpaque>`, or a function
taking an `LrlOpaque`) is not generated: typed code generation fails with `TB010` and
`--backend auto` falls back to the dynamic backend, whose values are untyped. Whatever happens,
a failed downcast is a checked panic, not undefined behaviour; it would indicate a lowering
that maps definitionally equal types to different Rust types (for example a type parameter of
a generic function instantiated at run time with a partially known type), which this scheme
does not rule out statically.

**Other flows.** MIR typing lets a value of a stuck type flow to or from a place of a known
loan-free type (`docs/spec/mir/typing.md`, "Types Computed at Run Time"): a definition whose
result type is stuck in its own body (`pick : Π b. BoolOrNat b`, or `transport` along an equality
into a type family) used at a known type, or an alternative of a match whose motive computes
different types per constructor. The typed backend generates the same conversions at every
assignment and call whose source and target MIR types differ in such a position: the value is
boxed where it enters a stuck type and unboxed where it leaves one (the boxed type is always
stated, never inferred), function values are adapted. A conversion that involves a callee's own
type parameters, or would box or unbox a partially known type, is rejected with `TB010`.

**Existential fields (not supported).** A constructor field whose type is an earlier field of
the same constructor, as in the existential package
`(inductive Pkg (sort 2) (ctor pkg (pi A (sort 1) (pi x A (pi f (pi a A Nat) Pkg)))))`, is laid
out as `()`: the layout template (`lower_type_template` in `mir/src/types.rs`) erases a type
variable bound by an earlier field to `Unit`, so `Pkg` is emitted as `pkg((), (),
Rc<dyn LrlCallable<(), u64>>)`. Storing a value of the hidden type there (`pkg Bool true ...`)
makes rustc reject the generated Rust with `E0308`: `--backend typed` fails ("Compilation
failed."), and `--backend auto` falls back to the dynamic backend after rustc rejects the
output. The dynamic backend runs such programs (`cli/tests/review_regressions.rs`,
`existential_package_runs_on_the_dynamic_backend`).

## Entry Point
The program entry is the last top-level definition; the generated Rust `main` calls it and
prints its value. A polymorphic entry (whose type starts with type binders) is a function value
that is printed, never applied; its type parameters are instantiated with `()` (Rust cannot
infer them, and used to fail with `E0283`).

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
- `TB010`: A value of a type computed at run time would have to be boxed or unboxed at a partially known type (see "Values of Types Computed at Run Time").
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
- `TB010`: emitted for large eliminations whose motive values are partially known types; covered by `cli/tests/typed_large_elimination.rs` (typed rejection and `auto` fallback).
- `TB900`: internal invariant guard; indicates a backend bug or malformed MIR outside supported invariants.

## No Tag-Check Panics
For supported programs, emitted Rust must **not** include tag-check panics (e.g. “Expected Func”, “wrong tag”). Any remaining panic must be an intentional runtime check/helper path.

## Determinism
- Stable ordering of items (defs, ADTs, ctors).
- Stable symbol naming (sanitized names for Rust identifiers, see below).

## Rust Names of LRL Items
Both backends name generated Rust items after LRL definitions, inductive types and constructors
through one function, `mir::codegen::sanitize_name`:
- characters that cannot appear in a Rust identifier are escaped as `uXX_` (hexadecimal code
  point), e.g. `+` becomes `_u2B_` and `m.Shape` becomes `mu2E_Shape`;
- `main` becomes `__lrl_main` (the generated Rust `fn main` calls it and prints its result);
- a name that collides with a Rust keyword of any edition (including `crate`, `self`, `Self`,
  `super`, which cannot be raw identifiers, and `_`), a primitive type (`u64`, `bool`, `usize`,
  ...), a standard-library name that generated code uses unqualified (`Box`, `Rc`, `String`,
  `Clone`, `Fn`, `Option`, `Some`, `Ok`, ...), or a name of the generated code (the runtimes'
  `Lrl*` types, `runtime_*` helpers, `Value`, `rec_*` recursor entries, `closure_*` bodies,
  `__lrl*`, and the generic parameters `T0`, `T1`, ...) gets the prefix `lrl_` (`Box` becomes
  `lrl_Box`, `crate` becomes `lrl_crate`);
- a name that already starts with `lrl_` is prefixed as well, so two different identifiers
  never receive the same Rust name.

The dynamic backend's recursor functions are named `rec_<sanitized name>_entry` /
`rec_<sanitized name>_impl` (they used the raw inductive name, which is not a Rust identifier for
a module-qualified inductive). The typed backend recognises the prelude's interior-mutability
types (`RefCell`, `Mutex`, `Atomic`) by their LRL name, not by their Rust name.

Remaining limitation: the `uXX_` escaping itself is not injective (an LRL name `foou2E_bar`
and `foo.bar` both become `foou2E_bar`).
