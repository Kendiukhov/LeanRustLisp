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
