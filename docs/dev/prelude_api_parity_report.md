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

## API notes

- `append` is executable in `prelude_api.lrl` and shared by both backends.
- Current signature is Nat-list focused: `append : List Nat -> List Nat -> List Nat`.
- Backend impl preludes do not redefine `append`; they only provide platform-layer substrate.

## Temporarily Gated Features

- Interior mutability runtime behavior (`RefCell`/`Mutex` checks): declared in API, runtime behavior still backend/runtime-gated.
- Dynamic boundary (`Dyn`/`EvalCap`/`eval`): backend-specific representation and execution model.
- Axiom execution: blocked by default; enabled only under `--allow-axioms`, with loud warnings and artifact metadata.

## Platform Layer Status

Current impl layers are restricted to runtime substrate declarations (`Dyn`, `EvalCap`, `eval`) and no longer carry shared stdlib algorithms.

## Stdlib Ownership

Public contract ownership:

- `prelude_api.lrl` owns the exported prelude contract (names and signatures visible to user code).
- User code must rely on this contract, not on backend impl files.

Implementation ownership:

- `prelude_impl_dynamic.lrl` and `prelude_impl_typed.lrl` own only platform-dependent runtime substrate.
- They must not become duplicate stdlib layers.

Shared-library ownership:

- Backend-neutral algorithms belong in shared stdlib modules (`stdlib/std/*`) as migration proceeds.
- Until migration completes, shared algorithms may remain in `prelude_api.lrl`, but must still be defined once and never duplicated in impl preludes.

Policy classification:

- Must fix for 0.1: accidental shared algorithm duplication in impl preludes.
- Allowed divergence (documented): `Dyn`/`EvalCap`/`eval` representation and execution model.
- Feature-gated: interior mutability runtime checks and executable axioms.
