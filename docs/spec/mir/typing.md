# MIR Typing and Nominal IDs

This document defines the MIR type language (`MirType`), nominal IDs, and
runtime-vs-erased policy for indices and proofs.

## Nominal ID Scheme (Deterministic)

All semantic identity is keyed by **deterministic nominal IDs** derived from:
- `PackageId` (from lrl.lock: name + version + source + hash)
- `ModulePath` (e.g., std::list)
- `ItemName` (e.g., List)
- `Disambiguator` (only if needed; e.g., gensyms or same-name items)

IDs are hashed to a 64-bit or 128-bit value (or interned as structured keys).
A single registry mints these IDs during declaration loading/elaboration:
- deterministic module load order
- no HashMap iteration dependence
- no ID minting inside MIR passes

ID definitions:
- **DefId**: any top-level definition (functions, constants, axioms)
- **AdtId**: inductive type definition
- **CtorId**: (AdtId, ctor_index) (index is preferred once ctor order is fixed)
- **FieldId**: (CtorId, field_index) (or field name if fields are named)

## MirType (Runtime Type Language)

`MirType` describes **runtime** types used by borrow checking and codegen:
- `Unit`, `Bool`, `Nat`
- `Adt(AdtId, Vec<MirType>)` (nominal ADT with type parameters)
- `Ref(Region, Box<MirType>, Mutability)`
- `Fn(FnKind, Vec<Region>, Vec<MirType>, Box<MirType>)` (kind is `Fn`, `FnMut`, or `FnOnce`)
- `RawPtr(Box<MirType>, Mutability)`
- `InteriorMutable(Box<MirType>, IMKind)`

`FnKind` is preserved into MIR to drive ownership semantics for calls (shared
borrow vs mutable borrow vs consume); see `docs/spec/function_kinds.md`.

`Fn` carries an **ordered binder list** of region parameters that are bound at
the function type level. Region parameters are assigned from **explicit
reference labels** (surface `Ref #[label] Shared T` / `Ref #[label] Mut T`) or
by **positional occurrence** when no label is given. Reusing the same label
ties lifetimes together (e.g., `Ref #[a] Shared T -> Ref #[a] Shared T`). The
pretty printer renders the binder list as `fn<'r0, 'r1>(...) -> ...` (or
`fn_mut` / `fn_once` for other kinds).

Elision rule: if a signature has exactly one distinct reference lifetime among
its inputs, unlabeled return references are assigned that lifetime. Otherwise,
return references must be labeled explicitly.

Implementation note: the core term stores the optional label on the outer `Ref`
application; MIR lowering reads it directly. Labels are preserved through core
term transformations and are ignored by definitional equality.

At each call site, these region parameters are instantiated with **fresh**
inference regions; call constraints relate arguments and the destination using
the instantiated regions (see `docs/spec/mir/nll-constraints.md`).

## Call Operands (Borrowed Callees)

`Terminator::Call` uses a dedicated call operand to encode how the callee is
accessed:

- `CallOperand::Operand(Operand)` uses the normal operand rules (e.g.,
  `Operand::Move` consumes the function value).
- `CallOperand::Borrow(BorrowKind, Place)` represents a borrow of the callee
  place, used for `Fn`/`FnMut` calls.

Typing rule:
- The callee place must have type `MirType::Fn(kind, args, ret)`.
- `BorrowKind::Shared` is required for `Fn` calls; `BorrowKind::Mut` is required
  for `FnMut` calls.
- `FnOnce` calls must use `Operand::Move` rather than a borrow.

Borrow checking treats the callee borrow as a temporary loan that covers the
call, ensuring arguments and destination do not violate aliasing constraints.

## Closure Capture Modes

Lowering preserves **per-capture modes** inferred during elaboration:
- **Observational** captures become shared borrows (`Ref Shared`) of the
  captured place.
- **Mutable-borrow** captures become mutable borrows (`Ref Mut`).
- **Consuming** captures move the value into the closure environment.

The closure local records these capture types in `LocalDecl::closure_captures`
so NLL can keep the corresponding loans live for the closure’s lifetime.

### Interior Mutability Classification

Interior mutability is determined by **marker traits/attributes** resolved by
elaboration into DefId-based flags (no string matching). Examples:
- `InteriorMutable`
- `MayPanicOnBorrowViolation` (RefCell-like)
- `ConcurrencyPrimitive` (Mutex/Atomic family)
- `AtomicPrimitive` (Atomic subtype marker)

These markers drive:
- runtime check insertion
- the panic-free profile lint

Panic-free profile restrictions:
- Any interior mutability (RefCell/Mutex/Atomic) is rejected.
- Indexing (including bounds checks) is rejected because it may panic.
- Borrowing via `borrow_shared`/`borrow_mut` is rejected.

### Marker Resolution Flow

Surface `inductive` declarations may include a marker list, e.g.:
`(inductive (interior_mutable may_panic_on_borrow_violation) RefCell ...)`.
The parser **does not** interpret marker names. During elaboration, each marker
symbol is resolved to a **DefId** by looking up the corresponding definition in
the environment (prelude provides the standard marker defs). The elaborator then
maps those DefIds to `TypeMarker` flags attached to the `InductiveDecl`. Downstream
passes (MIR lowering, NLL, lints, codegen) use these flags, not raw strings.

Validation rules:
- `interior_mutable` alone is invalid; it must be paired with a kind marker
  (`may_panic_on_borrow_violation`, `concurrency_primitive`, or `atomic_primitive`).
- `may_panic_on_borrow_violation` may not be combined with concurrency/atomic
  markers. `atomic_primitive` may appear with `concurrency_primitive` (redundant).

Prelude defines marker axioms explicitly (e.g., `(axiom unsafe interior_mutable Type)`), and
macro expansion may only introduce unsafe/classical forms in the prelude if the macro is
explicitly allowlisted in the compiler.

## Indices and Layout Policy

**Dependent indices do not affect runtime layout.**
- `MirType::Adt(AdtId, type_args)` is the runtime identity.
- Index arguments are erased or kept only in compile-time metadata.
- If a library needs a runtime index, it must be an explicit field in the
  runtime representation (e.g., `VecDyn<A> { len: usize, data: Box<[A]> }`).

This avoids backend-dependent layout logic and matches proof erasure.

## Sanity Rule

Borrow checking, MIR typing, and codegen must **never** depend on raw strings for
semantic identity. All semantics must be keyed by DefId/AdtId/CtorId/FieldId
(including PackageId).
