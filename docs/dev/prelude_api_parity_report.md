# Prelude API Parity Report

## Scope

This report compares:

- shared API layer: `stdlib/prelude_api.lrl`
- dynamic platform layer: `stdlib/prelude_impl_dynamic.lrl`
- typed platform layer: `stdlib/prelude_impl_typed.lrl`

and classifies divergences.

## Shared API Coverage

The following are provided through `prelude_api.lrl` for both backend stacks:

- Core types: `Nat`, `Bool`, `False`, `List`, `Comp`, `Eq`
- Core functions: `add`, `append`, `not`, `if_nat`, `and`, `or`, `print_nat`, `print_bool`
- Borrow/index boundaries: `Shared`, `Mut`, `Ref`, `borrow_shared`, `borrow_mut`, `VecDyn`, `Slice`, `Array`, `index_*`
- Interior mutability declarations: `RefCell`, `Mutex`, `Atomic`
- Marker axioms: `interior_mutable`, `may_panic_on_borrow_violation`, `concurrency_primitive`, `atomic_primitive`, `indexable`

## Divergences

| Item | Dynamic | Typed | Classification | Note |
|---|---|---|---|---|
| `Dyn`, `EvalCap`, `eval` | Axiom-based placeholders | Concrete typed ADTs + identity `eval` | Feature-gated (explicit) | Kept backend-specific until effect/runtime model converges |

## API placeholders

- `append` is now declared in the shared API as `axiom unsafe` (signature-only contract) so both backends share one public name/type while executable backend-neutral lowering is tracked separately.

## Temporarily Gated Features

- Interior mutability runtime behavior (`RefCell`/`Mutex` checks): declared in API, runtime behavior still backend/runtime-gated.
- Dynamic boundary (`Dyn`/`EvalCap`/`eval`): backend-specific representation and execution model.
- Axiom execution: blocked by default; enabled only under `--allow-axioms`, with loud warnings and artifact metadata.

## Platform Layer Status

Current impl layers are restricted to runtime substrate declarations (`Dyn`, `EvalCap`, `eval`) and no longer carry shared stdlib algorithms.
