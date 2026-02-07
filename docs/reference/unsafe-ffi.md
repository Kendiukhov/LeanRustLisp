# Unsafe

LRL allows bypassing safety checks in designated blocks.

## The `unsafe` keyword

The `unsafe` block allows:
- Dereferencing raw pointers.
- Calling functions marked `unsafe` (including FFI).
- Implementing `unsafe` traits.

## Invariants

It is the programmer's responsibility to ensure that unsafe code maintains the logical invariants of the system:
- Memory safety (no invalid pointers).
- Type safety (casting must be valid).
- Thread safety (no data races).
