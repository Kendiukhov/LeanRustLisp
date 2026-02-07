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

Functions can declare implicit arguments (syntax to be finalized, usually `{x : A}`). The elaborator attempts to insert these arguments automatically at call sites.
