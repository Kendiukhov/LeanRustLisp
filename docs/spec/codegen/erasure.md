# Erasure

## Prop Erasure
Terms in `Prop` are erased.
- `App(t, u)` where `u : Prop` -> `t` (if `t` is a function).
- `u : Prop` arguments are dropped from function signatures.

## Type Erasure
Type parameters are erased in the dynamic backend, but monomorphized (specialized) in the typed backend.
`PhantomData` fields are dropped.
