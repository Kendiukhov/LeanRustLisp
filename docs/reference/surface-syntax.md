# Surface Syntax

This document lists the special forms recognized by the **desugarer** and **compiler**.

## Binding Forms

### `lam`
Lambda abstraction.
```lisp
(lam <name> <type> <body>)
```

### `let`
Local binding.
```lisp
(let <name> <value> <body>)
```

## Top-Level Declarations

### `def`
Global definition.
```lisp
(def <name> <type> <value>)
```

### `inductive`
Inductive type definition.
```lisp
(inductive <name> <type> <constructor>*)
```
Where constructor is `(<name> <type>)`.

### `defmacro`
Macro definition.
```lisp
(defmacro <name> (<args>*) <body>)
```

## Control Flow

### `match`
Pattern matching.
```lisp
(match <scrutinee>
  (<pattern> <body>)*)
```

## Types

### `pi` / `->`
Function types.
```lisp
(pi (<name> <type>) <body>)
(-> <type> ... <ret_type>)
```

### `sort` / `Type` / `Prop`
Universes.
```lisp
(sort <level>)
(Type <level>) ; sugar for (sort (succ level)) ??? Check implementation
Prop           ; sugar for (sort 0)
```
