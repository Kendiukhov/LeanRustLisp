# Migration Notes - 2026-02-02 (Mode A Round 2)

These notes summarize user-visible changes related to Copy instances and function kinds.

## 1) Explicit Copy instances now require `unsafe`

- Old: `(instance copy (pi A (sort 1) (Box A)))`
- New: `(unsafe instance copy (pi A (sort 1) (Box A)))`
- Explicit Copy instances are rejected for interior-mutable types.
- Unsafe Copy instances are tracked as axioms: `copy_instance(TypeName)` tagged `unsafe`.

## 2) Function kinds and closure usage

- `lam`/`pi` accept an optional kind: `fn` (default) or `fnonce` (also `#[fn]` / `#[once]`).
- Kind inference marks closures that move or mutably borrow captures as `FnOnce`.
- A value of kind `Fn` may be used where `FnOnce` is expected (widening), since `Fn` is strictly stronger.
- Function values are non-Copy. If you previously duplicated a closure value, switch to:
  - passing it by shared reference,
  - lifting it to a top-level `def` (no captures), or
  - restructuring to avoid copying the function value.

## 3) Reserved primitive names

- `borrow_shared`, `borrow_mut`, `index_vec_dyn`, `index_slice`, `index_array` are reserved.
- These names are treated as compiler intrinsics during MIR lowering; user code must not redefine them.
- Only prelude code should introduce them as `unsafe` axioms with fixed signatures.

## 4) What to re-run

- `cargo test --all`
- `INSTA_UPDATE=always cargo test -p frontend` (or `-p cli`) if snapshots changed.
