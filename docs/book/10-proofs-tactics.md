# Proofs and Tactics

LRL follows the Curry-Howard correspondence: **Propositions are Types** and **Proofs are Programs**.

## Propositions are Types

To prove a statement `P`, you define a type `P` and construct a term `t : P`.

```lisp
;; A proposition that 0 = 0
(def zero-is-zero (Eq Nat zero zero)
  (refl Nat zero))
```

## Proof Erasure

All types in `Prop` are erased at runtime. This means your extensive proofs about vector bounds checks cost **zero runtime overhead**.

## A Simple Proof

(Example assumes `Vec` and `append` are defined)

```lisp
;; Lemma: appending nil to a vector yields the same vector
(def append-nil-lemma
  (pi (n Nat) (v (Vec Nat n))
      (Eq (Vec Nat n) (append v nil) v))
  (lam n Nat
    (lam v (Vec Nat n)
       ;; Proof body would go here
       (refl (Vec Nat n) v))))
```

*Note: Tactics are planned but not yet implemented. Currently, proofs are written as explicit terms.*
