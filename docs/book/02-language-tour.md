# A Tour of LeanRustLisp

This chapter takes you through a whirlwind tour of LRL's core features.

## 1. Defining Inductive Types

LRL uses inductive types to define data structures. Here is the classic definition of natural numbers.

```lisp
(inductive Nat (sort 1)
  (ctor zero Nat)
  (ctor succ (pi n Nat Nat)))
```

- `Nat` is the type name.
- `(sort 1)` is its universe.
- `zero` is a constructor that is a `Nat`.
- `succ` is a constructor that takes a `Nat` and returns a `Nat`.

## 2. Defining Functions

We can define functions using `def` and `lam` (lambda).

```lisp
(def one Nat (succ zero))

(def inc (pi n Nat Nat)
  (lam n Nat
    (succ n)))
```

## 3. Pattern Matching

We use `match` to deconstruct inductive types.

```lisp
(def is-zero (pi n Nat Bool)
  (lam n Nat
    (match n Bool
      (case (zero) true)
      (case (succ m ih) false))))
```

*Note: `Bool`, `true`, and `false` are defined in the standard prelude.*

## 4. Evaluation

You can evaluate expressions in the REPL or at the top level of a file (which prints the result).

```lisp
(is-zero zero)
;; Output: true : Bool

(is-zero (succ zero))
;; Output: false : Bool
```

## 5. Macro Expansion

Macros allow you to extend syntax at compile time. A simple example:

```lisp
(defmacro plus_two (x)
  (quasiquote (add (unquote x) (succ (succ zero)))))

(def x Nat (succ zero))
(def y Nat (plus_two x))
;; Expands to: (add x (succ (succ zero)))
```

Macros operate on syntax objects (`x` is syntax) and return new syntax.

## 6. Dependent Types

LRL is dependently typed: types can mention values. `Eq` in the prelude is a simple indexed family.

```lisp
(def zero-is-zero (Eq Nat zero zero)
  (refl Nat zero))
```

## 7. Positive Properties at a Glance

This small group of definitions shows three useful guarantees.

```lisp
;; 1) Total structural recursion.
(def nat-pred (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ n-prev ih) n-prev))))

;; 2) Hygienic macro expansion (no accidental capture).
(defmacro m1 (body) (lam x Nat body))
(def y0 Nat 10)
(def still-y0 Nat (app (m1 y0) 99)) ;; evaluates to 10

;; 3) Proof-carrying API: proof is checked statically.
(def with-self-eq
  (pi n Nat (pi p (Eq Nat n n) Nat))
  (lam n Nat
    (lam p (Eq Nat n n)
      n)))

(def checked-one Nat
  (with-self-eq (succ zero) (refl Nat (succ zero))))
```

The compiler checks each property (termination shape, hygiene, and proof typing) before runtime.
