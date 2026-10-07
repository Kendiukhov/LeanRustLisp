/-!
# LRL syntax — simply-typed fragment

This file defines a small simply-typed lambda calculus in de Bruijn form.
It is the scaffold the `Mechanized.lean` aggregator builds on.
The dependent-type fragment of the paper lives in `Dependent.lean` and is
a stretch goal; this file stays simple so the proofs in `Typing.lean`
remain tractable.

Decisions:
* de Bruijn indices, no named variables
* one base type and function types
* no letE, no fixpoints, no inductives — just the STLC core
-/

namespace LRL

/-- Types of the simply-typed fragment. -/
inductive Ty : Type where
  | base : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- Terms of the simply-typed fragment, in de Bruijn form. -/
inductive Term : Type where
  | var : Nat → Term
  | lam : Ty → Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

end LRL
