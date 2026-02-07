# Effect System

LRL plans to use an Algebraic Effect System (or Monadic representation in the interim).

## Goal
Track side effects (IO, State, Exceptions) in the type system.
`f : A -> {E} B`

## Current Status
Currently emulated via the `IO` monad opaque type.
