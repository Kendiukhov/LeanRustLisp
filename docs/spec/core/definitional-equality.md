# Definitional Equality

## Reductions

The relation `t ≡ u` is defined by normalizing both `t` and `u` to a common form.

### Beta (β)
`(\x. b) a` reduces to `b[x/a]`.

### Delta (δ)
Constants are unfolded if transparency permits.
`def x := v`. `x` reduces to `v`.

### Iota (ι)
Recursor on constructor.
`Rec(Ctor(i, args))` reduces to the `i`-th minor premise applied to `args`.

### Zeta (ζ)
`let x := v in b` reduces to `b[x/v]`.

### Eta (η)
`(\x. f x)` reduces to `f`.

## Algorithmic Equality

The implementation uses NbE (Normalization by Evaluation) with a fuel limit.
1. Evaluate terms to Weak Head Normal Form (WHNF).
2. If heads are different (and stubborn), they are not equal.
3. If heads are equal, recurse on arguments.
