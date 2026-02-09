# Macros and Metaprogramming

LRL is a Lisp, so code is data. Macros allow you to transform code at compile time.

## Defining Macros

Use `defmacro`.

```lisp
(defmacro mk-inc (val)
  (quasiquote (add (unquote val) (succ zero))))
```

Example use:

```lisp
(def x Nat (succ (succ zero)))
(def y Nat (mk-inc x))
;; expands to: (add x (succ zero))
```

Macro expansion runs before type checking.

## Hygiene

LRL macros are **hygienic**. This means variables introduced by macros don't accidentally capture variables from the user's code, and vice versa.

```lisp
(defmacro m1 (body) (lam x Nat body))
(def y Nat 10)
(def always-y (pi _ Nat Nat) (m1 y))
(def r1 Nat (app always-y 99)) ;; 10

(defmacro m2 () (lam x Nat x))
(def x Nat 5)
(def id-from-macro (pi _ Nat Nat) (m2))
(def r2 Nat (app id-from-macro 100)) ;; 100

(def z Nat 7)
(defmacro m3 () z)
(def r3 Nat (app (lam z Nat (m3)) 8)) ;; 7
```

In `r1`, the macro's internal binder does not capture `y`. In `r2`, call-site `x` does not capture the macro-generated `x`. In `r3`, local `z` does not capture macro `z`.

## Debugging Macros

If a macro behaves unexpectedly, inspect expansions:

```bash
cargo run -p cli -- --expand-1 my_file.lrl
cargo run -p cli -- --expand-full my_file.lrl
cargo run -p cli -- --trace-macros my_file.lrl
```

This gives a deterministic view of exactly what code the type checker receives.
