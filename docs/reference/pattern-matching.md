# Pattern Matching

Pattern matching is a surface-level feature that compiles to recursors.

## Exhaustiveness

Matches must differ cover all constructors of the inductive type. Missing cases result in a compile-time error.

## Redundancy

Unreachable patterns (shadowed by earlier ones) are compile-time errors.

## Compilation

The `match` construct is desugared into a tree of `Rec` applications (decision tree compilation).
This ensures that all pattern matching constitutes valid structural recursion (or well-founded recursion if specified).
