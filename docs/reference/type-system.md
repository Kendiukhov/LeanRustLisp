# Type System

The core of LRL is a Calculus of Inductive Constructions (CIC).

## Universes

There is a hierarchy of universes:
- `Prop` (Sort 0): Logical propositions. Erased at runtime.
- `Type 0` (Sort 1): Basics types (Nat, Bool).
- `Type n` (Sort n+1): Higher universes.

`Prop` is impredicative. `Type` levels are predicative.

## Dependent Products (Pi)

The fundamental type constructor is `Pi` (Π).
`forall (x : A), B x`.
If `B` is constant, this is `A -> B`.

## Definitional Equality

Two terms are definitionally equal if they compute to the same normal form. The kernel checks this by normalizing both terms (with limits on "fuel").

Reductions:
- Beta: `(\x. b) a ~~> b[x/a]`
- Delta: `def x := v` -> `x ~~> v`
- Iota: Recursor reduction (pattern matching).
- Eta: `(\x. f x) ~~> f` (for functions).

## Inductive Types

Inductive types are defined by their introduction rules (constructors). Their elimination rule (recursor) is automatically generated.
Recursion must be well-founded (guarded by structural decrease or a measure).
