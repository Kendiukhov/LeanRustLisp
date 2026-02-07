# Examples

A collection of examples demonstrating LeanRustLisp's capabilities.

## 1. Natural Numbers & Recursion

Demonstrates **inductive types** and **structural recursion**.

```lisp
(inductive Nat (Type 0)
  (zero Nat)
  (succ (-> Nat Nat)))

(def add (-> Nat Nat Nat)
  (lam n (lam m
    (match n
      (zero m)
      (succ (pred) (succ (add pred m)))))))
```

**Key Concept**: The kernel verifies that `add` terminates because `pred` is a structural sub-term of `n`.

## 2. Safe Array Access (Dependent Types)

Demonstrates **dependent types** for bounds checking.

```lisp
;; Vector of length n
(inductive Vec (Type 0) (Nat)
  (nil (Vec zero))
  (cons (forall (n : Nat) (-> Nat (Vec n) (Vec (succ n))))))

;; Safe lookup (impossible to call with out-of-bounds index)
(def lookup (forall (n : Nat) (-> (Fin n) (Vec n) Nat))
  ...)
```

**Key Concept**: The type system prevents out-of-bounds errors at compile time.

## 3. hygienic Macros

Demonstrates the **macro system**.

```lisp
(macro unless (cond body)
  `(if (not ,cond) ,body ()))

(unless (is-empty list)
  (process list))
```

**Key Concept**: Macros transform syntax before elaboration. Hygiene ensures variables don't capture accidentally.

## 4. Borrowing & Ownership

Demonstrates **affine types** and **borrow checking**.

```lisp
(def process (-> (Ref String) Unit) ...)

(let s "hello")
(process (borrow s)) ;; OK: borrow
(consume s)          ;; OK: move
;; (process (borrow s)) ;; ERROR: Use after move
```

**Key Concept**: Linear resources must be used exactly once (or borrowed).

## 5. Noncomputable Logic

Demonstrates **erasure** and **logical axioms**.

```lisp
(axiom classical_choice ...)

(def my_theorem (-> Prop Prop)
  (lam p (or p (not p)))) ;; Uses classical logic

;; (eval my_theorem) ;; ERROR: Cannot evaluate noncomputable definition
```

**Key Concept**: Logical proofs are erased at runtime and cannot pollute executable code.
