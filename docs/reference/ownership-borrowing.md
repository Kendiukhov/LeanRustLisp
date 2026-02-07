# Ownership and Borrowing

LRL enforces affine usage of linear resources.

## Usage Modes

The system tracks variable usage in three modes:
1. **Consuming**: The value is moved. It cannot be used again.
2. **MutBorrow**: The value is mutably borrowed. Exclusive access.
3. **Observational**: The value is read. Shared access.

## Move Semantics

By default, passing a non-`Copy` value to a function `(f x)` is a **move** (Consuming usage).
Subsequent use of `x` is a compile-time error (`UseAfterMove`).

## Copy Types

Types like `Nat` and `Bool` are `Copy`. They can be used multiple times; each usage is a copy.

## Closures and Capture

Closures capture variables from their environment. The capture mode is inferred based on usage in the body.
Code that attempts to capture a moved variable is rejected.
