# Basic Syntax

LRL uses S-expressions (symbolic expressions, or "sexprs") as its surface syntax. If you've used Lisp or Scheme, this will feel familiar. If not, don't worry—it's very simple.

## Atoms and Lists

The code is made of **atoms** and **lists**.

### Atoms
- **Integers**: `0`, `42`, `-123`
- **Strings**: `"Hello world"`
- **Symbols**: `foo`, `Nat`, `add`, `+`
- **Keywords**: There are a few reserved keywords like `def`, `lam`, `match`, but most "keywords" are just symbols that macros recognize.

### Lists
A list is parentheses surrounding zero or more elements separated by whitespace.
- `()` : The empty list (nil).
- `(add 1 2)` : A list with three elements.
- `(lam x (sort 0) x)` : Nested lists.

## Comments

Line comments start with `;`.
```lisp
; This is a comment
(def x Nat zero) ; This is also a comment
```

## Binding Forms

### Lambda (`lam`)
Constructs an anonymous function.
```lisp
(lam parameter type body)
```
Example:
```lisp
(lam x Nat (succ x))
```

### Let (`let`)
Local bindings.
```lisp
(let x 1
  (add x x))
```
*Note: `let` syntax might vary depending on macro definition in prelude, but conceptually it binds a value to a name in a scope.*

## Definitions (`def`)

Top-level definitions bind a name to a value globally.
```lisp
(def name type value)
```
Example:
```lisp
(def my-num Nat (succ zero))
```

## Reading Error Messages

LRL tries to provide helpful error spans.

```
Error: Type mismatch
  --> my_file.lrl:10:5
   |
10 | (add true 1)
   |      ^^^^
   |
   = Expected type: Int
   = Found type: Bool
```

When macros are involved, the error might point to the expansion or the original source, depending on where the error was detected. Use `--trace-macros` if you are confused about where an error is coming form.
