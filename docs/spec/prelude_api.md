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

`append` is currently provided as an unsafe prelude axiom signature (`axiom unsafe append ...`) so the API name/type is stable while backend-independent executable lowering is still being finalized.
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

## Guard Policy

`cli/tests/prelude_api_conformance.rs` enforces:

- shared API symbols are present when loading API + impl per backend
- platform impl files stay small (definition-count threshold)
- impl files do not duplicate shared stdlib algorithm definitions
