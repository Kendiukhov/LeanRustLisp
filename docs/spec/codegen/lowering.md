# Lowering

## MIR to Rust
The typed backend lowers MIR to Rust AST/HIR.
- `MirType::Adt` -> `enum` or `struct`.
- `MirType::Ref` -> `LrlRefShared<T>` / `LrlRefMut<T>`.
- `Statement::Assign` -> Rust assignment.

See [Typed Backend](typed-backend.md) for details.
