# Elaboration

Elaboration is the process of converting the user-friendly surface syntax into the fully explicit core calculus.

## Type Inference

LRL uses **bidirectional type checking**.
- **Inference**: Computing the type of a term from its structure.
- **Checking**: Verifying a term against a known expected type.

Top-level definitions `(def name type val)` are checked against the provided signature.

## Holes (`_`)

The underscore `_` allows you to ask the compiler to infer a term or type.
- In expressions: `(cons 1 _)` (infers the tail is nil/empty if constrained).
- In types: `(Vec _ n)` (infers the element type).

If the elaborator cannot solve a hole (unresolved metavariable), it reports an error.

## Implicit Arguments

Functions declare implicit binders with braces (`(pi {A (sort 1)} ...)`, `(lam {A} (sort 1) ...)`). At a call site the elaborator inserts a metavariable for each implicit argument that is not given explicitly (`{arg}` gives it explicitly) and solves it by unification with the types of the explicit arguments and the expected type. This works in values, in the types of definitions (also under binders, e.g. `(pi n Nat (Eq Nat (idn n) n))`), in `match` scrutinees and in explicit `(motive ...)` clauses. A constraint that cannot be decided yet (for example `pred ?n =?= m`, or `min1 ?k =?= succ zero` with a definition applied to an unsolved metavariable) is postponed and retried, with every solved metavariable substituted, once the other arguments and the expected type have been checked; constraints that stay blocked are reported as `F0217` (unsolved constraints), and constraints that turn out to be false as type errors (`F0214`/`F0205`). Different constructors never unify, whatever metavariables appear below them (`zero =?= succ ?n` fails at once with `F0214`).
