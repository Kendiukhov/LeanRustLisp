# A Tour of LeanRustLisp

This chapter takes you through a whirlwind tour of LRL's core features.

## 1. Defining Inductive Types

LRL uses inductive types to define data structures. Here is the classic definition of natural numbers.

```lisp
(inductive Nat (Type 0)
  (zero Nat)
  (succ (-> Nat Nat)))
```

- `Nat` is the type name.
- `(Type 0)` is its universe (like `Set` in Coq or `Type` in Lean).
- `zero` is a constructor that is a `Nat`.
- `succ` is a constructor that takes a `Nat` and returns a `Nat`.

## 2. Defining Functions

We can define functions using `def` and `lam` (lambda).

```lisp
(def one Nat (succ zero))

(def inc (-> Nat Nat)
  (lam n Nat (succ n)))
```

## 3. Pattern Matching

We use `match` to deconstruct inductive types.

```lisp
(def is-zero (-> Nat Bool)
  (lam n Nat
    (match n
      (zero true)
      (succ _ false))))
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

Macros allow you to extend the syntax. Let's define a simple macro that doubles a number.

```lisp
(defmacro double (x)
  (list 'add x x))

(double 5)
;; Expands to: (add 5 5)
;; Evaluates to: 10
```

Macros operate on syntax objects (`x` is syntax) and return new syntax.

## 6. Dependent Types

LRL is dependently typed, meaning types can depend on values.

```lisp
;; A vector of length n
(inductive Vec (-> (Type 0) Nat (Type 0))
  (nil (Vec A zero))
  (cons (-> A (Vec A n) (Vec A (succ n)))))
```

The type of `cons` ensures that if you add an element to a vector of length `n`, you get a vector of length `n+1`. The compiler enforces this at compile time.
