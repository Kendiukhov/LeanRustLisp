# Substitution and De Bruijn Indices

## Representation

LRL uses de Bruijn indices for bound variables.
- `Var(0)` is the innermost binder.
- `Var(1)` is the next binder out.

## Operations

### Lifting (Shifting)
When a term moves under a new binder (e.g. going inside a Lambda), free variables must be "shifted" (incremented).
`shift(term, cutoff, amount)`

### Substitution
`subst(term, index, replacement)`
Replaces `Var(index)` with `replacement`. Variables > `index` are decremented. `replacement` must be shifted when entering scopes.

## Correctness
The kernel implementation must strictly follow these rules to avoid capturing variables (although NBE uses closures which handles this differently, the AST operations must be correct for printing/manipulation).
