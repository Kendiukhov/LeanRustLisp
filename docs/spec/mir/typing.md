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
- `Opaque { reason }`: a type lowering cannot compute statically -- an opaque nominal type
  (an axiom type), or a *stuck* type computed at run time (see "Types Computed at Run Time")

`FnKind` is preserved into MIR to drive ownership semantics for calls (shared
borrow vs mutable borrow vs consume); see `docs/spec/function_kinds.md`.

Types are erased at run time: a term whose type is a sort (a type) is lowered to the value `()`
of type `Unit`, whether it is a sort, a Pi type, an inductive type or a type *application* such
as `List Nat`, `Vec A 1` or `T k` with `T : Nat -> Type` (`LoweringContext::term_is_type` in
`mir/src/lower.rs`). A type passed as an argument (explicitly or as an inferred implicit
argument) is therefore a `()` argument, never a call of an erased type constructor.

`MirType::is_copy` is a context-free approximation (every `Adt` is non-Copy); the checks that
need the Copy-ness of an inductive type use `AdtLayoutRegistry::type_is_copy`, which evaluates the
kernel's Copy instances (translated to MIR templates over the parameters) at the type's arguments.

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

Copy-ness of closure values follows Rust: a closure is `Copy` (duplicable by clone)
exactly when every capture is `Copy` or a shared reference. A non-Copy value captured
observationally by an `FnOnce` closure, and any function value captured observationally
or mutably, is moved into the environment (so that a closure returned from its
defining body does not hold a reference into that body), which makes the closure
non-Copy. The exception is the minor premise of a recursive constructor in a recursor
application, which never escapes the application and must be passed to the recursive
call and then called: its observational captures, function values included, stay shared
borrows, so it is Copy (see `docs/spec/mir/index.md`, "Recursor Lowering"). A closure
nested inside a body that holds a capture by shared reference re-captures that
reference (and dereferences it at each use).

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

**Dependent indices do not affect runtime layout, and MIR types do not mention them.**
- `MirType::Adt(AdtId, args)` is the runtime identity. `args` has exactly one entry per
  *uniform parameter* of the inductive (`InductiveDecl::num_params`), in order.
- **Index arguments are erased**: `Vec A n` and `Vec A m` (and `Vec A (succ n)` vs
  `Vec A (add 1 n)`) are the same MIR type `Vec<A>`. There is no index component in `MirType`
  (the former `MirType::IndexTerm` was removed).
- **Value parameters are represented by `Unit`**: a parameter whose binder type is not a sort
  (or a Π-telescope ending in a sort) — e.g. `x : A` in `Eq A x` — is a value, not a type, and
  does not influence the runtime layout; its argument is lowered to the placeholder `Unit` so
  that positional `Param(i)` references in layout templates keep their meaning. Type parameters
  (and type-family parameters) are lowered as types.
- If a library needs a runtime index, it must be an explicit field in the
  runtime representation (e.g., `VecDyn<A> { len: usize, data: Box<[A]> }`).

**Why erasure rather than comparing indices.** MIR typing is a check of *runtime
representations*: that every assignment, call and projection moves values whose layouts agree,
so that the backends can rely on them. Whether an index is right (`Vec A (succ n)` really has a
head) is a property of the dependent type, which the kernel has already checked for every
definition before it reaches MIR; MIR does not re-check it. Comparing index terms in MIR was
neither sound nor complete: the terms are open (de Bruijn variables of different scopes), so
syntactic comparison rejected kernel-correct programs (every value of an indexed family failed
with `M300`, e.g. `NVec [Var(1)]` vs `NVec [Var(0)]` for the same vector seen from two
binders), and comparing them up to definitional equality would require the kernel's context at
every MIR program point (MIR bodies do not carry it). Erasure makes MIR types exactly the
backends' types, which already ignored indices.

Consequences:
- The NLL `relate_types` relation relates the type arguments of any two values of the same
  family (before, a syntactic index mismatch made it skip relating their regions).
- A recursor arm whose constructor indices clash with the scrutinee's (e.g. `nil : Vec A zero`
  when the scrutinee has type `Vec A (succ n)`) is pruned by lowering (it is `Unreachable`),
  because the motive may assign it a different result type; see `docs/spec/mir/index.md`.

This avoids backend-dependent layout logic and matches proof erasure.

## Types Computed at Run Time

Lowering computes a value's MIR type from its kernel type in weak head normal form. When that
form is an application whose head is a variable or a recursor blocked on an unknown major
premise, the type is *stuck*: it is computed only at run time. Examples are a type-family
variable applied to arguments (`P y` inside `transport`) and a large elimination such as
`BoolOrNat b` (`match b (sort 1) (case (true) Nat) (case (false) Bool)`) for an unknown `b`, or
`HeadTy n` for an unknown index `n`. Its MIR type is `Opaque` with the reason
`STUCK_TYPE_REASON` (`MirType::is_stuck_type`). Other `Opaque` types (axiom types and other
opaque nominal types, reasons `const ...` / `app ...`) are unaffected by this section and are
compared by reason.

**Typing rule.** In assignments and calls, at any position of a type, a stuck type is
compatible with every *loan-free* type: `Unit`, `Bool`, `Nat`, and inductive types whose type
arguments and constructor fields are loan-free. References, function values (which may capture
references), raw pointers, interior mutability, opaque types and type parameters are not
loan-free. Justification:
- the kernel has type-checked the program, so for the run-time value the stuck type and the
  known type denote the same type (e.g. `BoolOrNat true` is `Nat` at a call `pick true`);
- the backends represent values of stuck types uniformly: the dynamic backend's values are
  untyped, and the typed backend boxes and unboxes them at such flows with a checked downcast
  (`docs/spec/codegen/typed-backend.md`, "Values of Types Computed at Run Time");
- the borrow checker cannot see regions inside a stuck type, so a flow between a stuck type and
  a type that may hold a loan (e.g. passing `(& t)` to `transport` at `P := λ _. Ref Shared Tok`)
  would hide the loan; such flows remain `M300` errors. A flow between a stuck type and a
  loan-free type carries no loan.

**Lowering of large eliminations of non-recursive types.** A match on a non-recursive inductive
is lowered inline (each alternative's body is lowered into the destination). If the motive is
not syntactically constant, an alternative's body has the type of the motive at its constructor,
which can differ from the destination's (the motive at the scrutinee). The body is then lowered
into a temporary of its own type and moved into the destination; when the two are different
known types (`Nat` and `Bool` for a scrutinee known to be `true`), the move goes through a
temporary of a stuck type, so that both assignments relate a stuck type and a known one. Such an
alternative is never taken (the kernel-checked types say the scrutinee is built by another
constructor). Recursors of recursive types keep their closure-based lowering; their typed-backend
code generation is described in `docs/spec/codegen/typed-backend.md`.

**Copy propagation.** An assignment between a stuck type and a known one is a change of
representation, so the MIR copy propagation (`transform::inline`) never replaces its source by
the source's own known value, and never propagates a value into an argument passed to a
parameter of a stuck type: the boundary stays an assignment (or argument) between locals whose
declared types are faithful. Likewise, lowering a non-variable term into a place of a stuck type
first builds the value in a temporary of its own (known, first-order) type.

**Limits.** The rule applies position-wise, so a partially stuck type meets a known one where
the stuck positions face loan-free types (`Pair Nat (T n)` and `Pair Nat Bool`); the dynamic
backend runs such programs, while the typed backend generates no deep conversion of data and
rejects them with `TB010` (`--backend auto` then falls back). Flows of stuck values to or from
types that may hold loans (references, function values, type parameters) are rejected.

**Fields of a stuck layout type.** An inductive's MIR layout is computed once, from its
constructor types with the uniform parameters as `MirType::Param`. A field whose type applies a
type-family parameter, such as `x : F zero` in
`(inductive Fam (pi F (pi n Nat (sort 1)) (sort 1)) (ctor mkf (pi F (pi n Nat (sort 1)) (pi x (F zero) (Fam F)))))`,
therefore has a stuck type in the layout whatever the argument for `F`, and MIR typing sees the
field place `p.(mkf).0` at that stuck type, which is not Copy. Lowering reads such a field out of
the scrutinee with a move, even when the field's type at the scrutinee's arguments (`K zero`,
i.e. `Nat`, for `F := K`) is Copy; the assignment into the field's local then relates a stuck
type and a known one as above. (It used to copy it, and MIR typing rejected the program with
`M300` "Copy of non-Copy place".) The typed backend rejects such programs with `TB010` (`Fam K`
meets `Fam<LrlOpaque>`, a partially known type), and `--backend auto` falls back to the
dynamic backend.

## Sanity Rule

Borrow checking, MIR typing, and codegen must **never** depend on raw strings for
semantic identity. All semantics must be keyed by DefId/AdtId/CtorId/FieldId
(including PackageId).
