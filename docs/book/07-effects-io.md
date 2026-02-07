# Effects and IO

LRL separates pure logic from side effects.

## The `IO` Effect

IO is not just a function returning a value; it's a description of an action.

*Note: The effect system is still in early alpha. Currently, we largely model IO via monads, but a full algebraic effect system is planned.*

## Purity

LRL, like Lean/Coq, is pure. A function `Nat -> Nat` always returns the same output for the same input and has no observable side effects.

To do IO (print to console, read files), you must use the `IO` type (or equivalent effect).

```lisp
(def main (IO Unit)
  (print "Hello World"))
```

## Why separation?

Strict separation allows the compiler to erase proofs and pure computations that aren't needed at runtime, while guaranteeing that "safe" code doesn't accidentally wipe your hard drive.
