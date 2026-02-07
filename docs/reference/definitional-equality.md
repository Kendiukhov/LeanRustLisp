# Definitional Equality

Definitional equality is the equivalence relation used by the type checker.

## Reductions

- **Beta (β)**: Function application. `(\x. b) a ≡ b[x/a]`.
- **Delta (δ)**: Constant unfolding. If `def x := v`, then `x ≡ v`.
  - Unfolding is controlled by **Transparency**. `Opaque` definitions are not unfolded.
  - **Fuel**: The checker uses a fuel metric to prevent infinite loops during unfolding of partial or cyclic terms.
- **Iota (ι)**: Inductive elimination. The application of a recursor `Rec` to a constructor `Ctor` reduces to the corresponding minor premise.
- **Eta (η)**: Extensionality. `(\x. f x) ≡ f`.
- **Zeta (ζ)**: Let-expansion. `let x := v in b ≡ b[x/v]`.

## Totality

Only **Total** definitions are legally unfolded during type checking. Partial definitions cannot be unfolded (to prevent unsoundness/loops in the type checker).
