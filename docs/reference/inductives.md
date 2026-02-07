# Inductives

Inductive reference.

## Declaration

```lisp
(inductive Name (Sort u)
  (ctor1 (-> Arg1 Name))
  ...)
```

## Universes

Inductives can live in `Prop` or `Type u`.
- **Prop Inductives**: Must not have large elimination (cannot eliminate to `Type` unless singleton/empty).
- **Strict Positivity**: Recursive occurrences of the inductive type in constructors must be strictly positive (nested to the left of arrows).

## Eliminators

For every inductive `T`, the kernel generates a recursor `T.rec`.
Surface `match` expressions are elaborated into applications of `T.rec`.
