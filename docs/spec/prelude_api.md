# Prelude API Contract

## Architecture

Prelude loading is now layered:

1. `stdlib/prelude_api.lrl` (shared public contract)
2. backend platform layer
   - dynamic: `stdlib/prelude_impl_dynamic.lrl`
   - typed/auto: `stdlib/prelude_impl_typed.lrl`

The user-facing assumption is: programs target the API contract, not a backend-specific prelude file.

## Guaranteed API Surface (0.1)

The following names are guaranteed by `prelude_api.lrl`:

- Marker axioms:
  - `interior_mutable`
  - `may_panic_on_borrow_violation`
  - `concurrency_primitive`
  - `atomic_primitive`
  - `indexable`
- Core types/constructors:
  - `Nat`, `zero`, `succ`
  - `Bool`, `true`, `false`
  - `False`
  - `List`, `nil`, `cons`
  - `Comp`, `ret`, `bind`
  - `Eq`, `refl`
- Core functions:
  - `add`, `append`, `not`, `if_nat`, `and`, `or`
  - `print_nat`, `print_bool`

`append` is executable in the shared API prelude. Current signature is Nat-list focused:
`append : List Nat -> List Nat -> List Nat`.
It is defined once in `prelude_api.lrl` and must not be redefined in backend impl preludes.
- Borrow/index/runtime boundary names:
  - `Shared`, `Mut`, `Ref`, `borrow_shared`, `borrow_mut`
  - `VecDyn`, `Slice`, `Array`
  - `index_vec_dyn`, `index_slice`, `index_array`
  - `RefCell`, `Mutex`, `Atomic`

## `Comp` Lives in `(sort 2)`

`Comp` is the return type that the kernel requires of `partial` definitions (`Comp A`). It is
declared as

```
(inductive Comp (pi A (sort 1) (sort 2))
  (ctor ret (pi A (sort 1) (Comp A)))
  (ctor bind (pi A (sort 1) (pi B (sort 1) (pi m (Comp A) (pi n (Comp B) (Comp B)))))))
```

so `Comp A : (sort 2)` for every `A : (sort 1)`. The reason is the kernel's universe rule for
inductive declarations (`docs/spec/core_calculus.md` §4): `bind`'s result is `Comp B`, so `A` is
not a uniform parameter, and `A` (in `ret` and `bind`) and `B` (in `bind`) are constructor fields
whose type `(sort 1)` has universe level 2. With `Comp` in `(sort 1)` these fields made `(sort 1)`
a retract of `Comp Nat` (`ElC (bind A Nat (ret A) (ret Nat)) ≡ A` for `ElC : Comp Nat -> (sort 1)`
defined by `match`), which is unsound; the kernel now rejects that declaration.

Design choice: the constructors and the surface API (`ret`, `bind`, `std/control/comp.lrl`'s
`comp_pure` / `comp_bind`) are unchanged; only the universe moved. `Comp` is value-erased (`ret`
carries no value; it is only built, returned and sequenced by partial code), so the larger
universe costs little. User-visible consequences (the universe hierarchy is not cumulative):

- `Comp A` is not a `(sort 1)` type: it cannot be an element type (`List (Comp Nat)`), the
  argument of a function generic over `(A : (sort 1))`, or a field of a `(sort 1)` inductive
  (`K0017`); `(def CT (sort 1) (Comp Nat))` is a type error.
- Matching on a `Bool`/`Nat` with motive `(Comp Nat)` eliminates into `(sort 2)`; this works as
  before (the elaborator computes the recursor level from the motive).

The alternative considered was a phantom `Comp` in `(sort 1)` with `A` a uniform parameter and a
homogeneous `bind : Comp A -> Comp A -> Comp A` (plus a cast `Comp A -> Comp B` defined in the
stdlib); it would keep `Comp A` in `(sort 1)` but change the arity of the `bind` constructor used by
existing programs. It was not needed: moving `Comp` to `(sort 2)` left the test suite and the
case-study programs unchanged.

## Platform Surface (Allowed in Impl Layers)

Backend implementation preludes are restricted to platform-dependent items:

- Dynamic platform (`prelude_impl_dynamic.lrl`):
  - `Dyn`, `EvalCap`, `eval`
- Typed platform (`prelude_impl_typed.lrl`):
  - `Dyn`, `EvalCap`, `eval` (typed representation)

Implementation preludes should not carry shared stdlib algorithms (for example `add`, `not`, `and`, `or`, `if_nat`).
This includes `append`, which is part of the shared public API layer.

## Stdlib Migration Boundary

The migration target is:

- `prelude_api.lrl` = public API contract and stable exported names.
- `prelude_impl_dynamic.lrl` / `prelude_impl_typed.lrl` = platform substrate only.
- shared, backend-neutral library logic = `stdlib/std/*` modules.

Ownership rules for definitions:

- Pure library algorithms must be defined once in shared stdlib modules (or temporarily in `prelude_api.lrl` while migrating).
- Backend impl preludes must not define or redefine user-facing stdlib algorithms.
- If a definition is needed only to bridge backend runtime representation, it may live in an impl prelude and must be documented as platform-specific.

Current 0.1 status:

- Core shared algorithms still live in `prelude_api.lrl`.
- Platform impl preludes are restricted to `Dyn` / `EvalCap` / `eval` substrate.
- Moving shared algorithms from `prelude_api.lrl` into `stdlib/std/*` is a staged migration, with API names kept stable.

## Guard Policy

`cli/tests/prelude_api_conformance.rs` enforces:

- shared API symbols are present when loading API + impl per backend
- platform impl files stay small (definition-count threshold)
- impl files do not duplicate shared stdlib algorithm definitions
