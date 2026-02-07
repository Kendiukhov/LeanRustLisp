# Runtime Representation

## Typed Backend
- `Nat`: `num_bigint::BigUint`.
- `Bool`: `bool`.
- `List`: `Vec<T>` (with wrapper).
- `Ref`: Wrapper around raw pointer or `&T`.

## Dynamic Backend
- `Value`: A universal enum (`Int`, `String`, `Cons`, `Closure`, `Foreign`).
