# Input/Output

LRL encapsulates side effects.

## The `IO` Type

`IO A` is a primitive opaque type representing a computation that performs effects and produces an `A`.

## Execution

The `main` function must have type `IO Unit`. The runtime executes this action.

*(Note: The current IO model is a placeholder. Future versions may use algebraic effects or monad transformers).*
