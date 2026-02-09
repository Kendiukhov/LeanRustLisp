# Proofs and Tactics

LRL follows the Curry-Howard correspondence: **Propositions are Types** and **Proofs are Programs**.

## Propositions are Types

To prove a statement `P`, you define a type `P` and construct a term `t : P`.

```lisp
;; Proposition: 0 = 0
(def zero-is-zero (Eq Nat zero zero)
  (refl Nat zero))
```

## Checked Proof Arguments

You can require proofs in APIs:

```lisp
(def with-self-eq
  (pi n Nat (pi p (Eq Nat n n) Nat))
  (lam n Nat
    (lam p (Eq Nat n n)
      n)))

(def one Nat (succ zero))
(def one-is-one (Eq Nat one one)
  (refl Nat one))

(def checked-one Nat
  (with-self-eq one one-is-one))
```

`checked-one` only exists if the proof term type-checks.

## Proof Erasure

Terms in `Prop` are erased at runtime. In practice, this means proof-heavy APIs can compile down to the same runtime behavior as proof-free equivalents.

## Why This Is Useful

- You can enforce invariants statically.
- You avoid runtime checks for those invariants when they are proven.
- You keep runtime code lean while still carrying strong compile-time guarantees.

*Note: tactics are planned but not yet implemented. Today, proofs are written as explicit terms.*
