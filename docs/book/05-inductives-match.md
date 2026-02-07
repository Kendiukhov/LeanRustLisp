# Inductives and Matching

Inductive types are the fundamental way to define data in LRL.

## Defining Inductives

Use the `inductive` form.

```lisp
(inductive List (-> (Type 0) (Type 0))
  (nil (List A))
  (cons (-> A (List A) (List A))))
```

- **Parameters**: `List` takes a parameter `(Type 0)` implicitly by the kind signature.
- **Constructors**: list the constructors and their full types.

## Pattern Matching

The `match` expression allows you to branch on constructors.

```lisp
(def length (-> (List Nat) Nat)
  (lam l (List Nat)
    (match l
      (nil zero)
      (cons h t (succ (length t))))))
```

### Recursion

Recursive functions like `length` are allowed, but the kernel checks termination. The simplest form of termination is structural recursion on an inductive argument.

### Pitfalls

- **Missing Cases**: All constructors must be covered.
- **Erasure**: You cannot pattern match on a `Prop` (proof) to produce a `Type` (data) result. This is a fundamental restriction to ensure proofs can be erased.
