# Ownership and Resource Model

This document outlines how LeanRustLisp integrates Rust-style ownership into a dependent type system.

## 1. Core Principle

**Affine Types**: Values are affine by default.
*   Usage: 0 or 1 times.
*   Drop: Allowed (destructors run).
*   Copy: Opt-in via `Copy`/`Dup` trait for unrestricted usage.

## 2. Borrowing & References

Borrowing produces references with explicit lifetimes (regions):

*   **Shared Reference**: `&'ρ A`
    *   Read-only access.
    *   Copyable (unrestricted).
*   **Unique Reference**: `&'ρ mut A`
    *   Read-write access.
    *   **Linear capability**: Cannot be aliased. Must be used linearly to preserve the ability to mutate.

## 3. Lifetimes at the Type Level

*   Lifetimes (`'ρ`) are first-class terms at the type level.
*   They are **not** value-dependent at runtime (erased).
*   The compiler implies a partial order (outlives relation) on regions.
*   **Verification**: A constraint solver runs on the mid-level IR (LRL-MIR) and generates evidence or checkable constraints for the kernel (or acts as a trusted oracle if split logic is used).

## 4. Mutation & Dependent Types

Systems programming wants in-place mutation, but dependent types need type stability.

*   **Rule**: `&mut T` preserves the type `T`. You cannot change the index of a dependently typed value in-place behind a reference if the index determines the type.
    *   *Example*: You cannot mutate a `Vec A n` into a `Vec A (n+1)` in-place via a simple `&mut` reference because the type changes.
*   **State Replacement**: To change type indices, you must take ownership and return a new value.
*   **Existential Packaging**: For mutable containers with dynamic size:
    ```lisp
    (structure Buffer (A : Type)
      (n : Nat)
      (data : Vec A n))
    ```
    The `n` is hidden; mutating the buffer updates `n` internally.

## 5. Safe Concurrency

*   **Contract**: Safe code implies no Data Races and no UB.
*   **Send/Sync**: Modeled as typeclass predicates derived/verified by the compiler.
*   **Primitives**: Mutexes, RwLocks, and Channels use ownership transfer to ensure safety.
