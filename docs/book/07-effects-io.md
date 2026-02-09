# Effects and IO

LRL separates pure logic from side effects.

## The `IO` Effect

Conceptually, IO is not "just another value transform"; it marks interaction with the outside world.

*Note: The effect system is still in early alpha. Currently, we largely model IO via monads, but a full algebraic effect system is planned.*

## Purity

LRL, like Lean/Coq, is pure. A function `Nat -> Nat` always returns the same output for the same input and has no observable side effects.

```lisp
(def double (pi n Nat Nat)
  (lam n Nat
    (add n n)))
```

## Current Alpha Surface

In current builds, common effectful operations are exposed through prelude functions such as `print`, `read_file`, and `write_file`.

```lisp
(def echo-file Text
  (let contents Text (read_file "input.txt")
    (write_file "output.txt" contents)))

(def entry Text
  (print "Hello, world!"))
```

## Why separation?

Strict separation allows the compiler to erase proofs and pure computations that aren't needed at runtime, while guaranteeing that "safe" code doesn't accidentally wipe your hard drive.

It also gives a practical benefit today: the same source can be validated in a more pure/dynamic environment and then compiled on the typed backend where platform hooks perform real side effects.
