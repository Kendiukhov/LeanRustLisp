# Ownership and Borrowing

LRL adopts Rust's ownership model to manage memory without a garbage collector.

## Ownership

Every value in LRL has a single owner. When you pass a value to a function, you **move** it, transfering ownership.

```lisp
(let x (create-resource)
  (consume x)
  (consume x)) ;; Error: Use of moved value 'x'
```

### Copy Types

Simple types like `Nat` and `Bool` are `Copy`. They are duplicated when passed, so the original remains usable.

## Borrowing

You can allow temporary access to a value via **references**.

- `&T`: Shared (immutable) reference. Many allowed.
- `&mut T`: Mutable reference. Only one allowed (exclusive).

### The Rules of Borrowing

1. At any given time, you can have either one mutable reference or any number of immutable references.
2. References must always be valid.

### Example: Mutation Iteration (Forbidden)

Just like in Rust, you cannot modify a collection while iterating over it with an immutable iterator.

```lisp
;; Pseudo-code for a common error
(let v (vec 1 2 3)
  (for x in &v
    (push &mut v x))) ;; Error: Cannot borrow `v` as mutable because it is also borrowed as immutable
```

This discipline prevents data races and iterator invalidation *at compile time*.
