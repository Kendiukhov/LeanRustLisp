# Types and Terms

In LRL, terms and types are unified (to an extent). However, there is a strict hierarchy of universes.

## Prop and Type

LRL distinguishes between logical propositions and computational data.

- `Prop`: The universe of logical propositions. Elements of `Prop` are erased at runtime.
- `Type n`: The universe of computational types at level `n`. `Type 0` is the type of ordinary data types like `Nat` and `Bool`. `Type 1` is the type of `Type 0`, and so on.

## Functions (Pi Types)

The type of a function is written as a Pi type (dependent product).

```lisp
(pi (x A) B)
```

If `B` does not depend on `x`, this is a simple function arrow `A -> B`.

```lisp
(-> Nat Nat)  ; Simple function
(pi (n Nat) (Vec Nat n)) ; Dependent function
```

## Dependent Types

Dependent types allow types to depend on values. A classic existence proof is "safe vector access" or "vectors of a specific length".

### Example: Polymorphic Identity

```lisp
(def id (pi (A (Type 0)) (-> A A))
  (lam A (Type 0) (lam x A x)))

(id Nat zero) 
;; A is explicitly passed as Nat
```

*Note: In future versions, implicit arguments will make this less verbose.*

## Definitional Equality

The type checker considers two terms equal if they reduce to the same normal form. This includes:

- **Beta (β) reduction**: Applying a lambda `(lam x t) u` reduces to `t[x/u]`.
- **Delta (δ) reduction**: Unfolding a definition. `id` reduces to its body.
- **Iota (ι) reduction**: Pattern matching reduction (e.g., `match (succ n)` reduces to the succ branch).

This means you don't need to manually prove that `(add 1 2)` equals `3`. They are *definitionally equal*.
