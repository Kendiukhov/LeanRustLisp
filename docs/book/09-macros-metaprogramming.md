# Macros and Metaprogramming

LRL is a Lisp, so code is data. Macros allow you to transform code at compile time.

## Defining Macros

Use `defmacro`.

```lisp
(defmacro assert (cond msg)
  (list 'if cond
        '(return unit)
        (list 'panic msg)))
```

When you write `(assert (eq x 0) "x must be 0")`, it expands to the `if` expression *before* the compiler checks types.

## Hygiene

LRL macros are **hygienic**. This means variables introduced by macros don't accidentally capture variables from the user's code, and vice versa.

```lisp
(defmacro safe-inc (x)
  (let temp 1
    (list 'add x temp)))

(let temp 100
  (safe-inc 5))
```

This expands safely. The `temp` inside the macro is distinct from the `temp` (100) in the user code, even though they have the same name. They have different *syntax contexts*.

## Debugging Macros

If a macro acts weird, check its expansion:

```bash
cargo run -p cli -- --expand-1 my_file.lrl
```

This is invaluable for seeing exactly what your macro generated.
