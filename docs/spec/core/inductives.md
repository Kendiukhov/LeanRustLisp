# Inductive Types

## Well-Formedness

An inductive definition `Ind` with constructors `C_1 ... C_n` is well-formed if:
1. The type of `Ind` is `Type u` or `Prop`.
2. Each constructor `C_i` returns `Ind`.
3. Inductive parameters are uniform.
4. Recursive occurrences of `Ind` in constructor arguments are **Strictly Positive**.

## Strict Positivity
`Ind` occurs strictly positive in `T` if:
- `T` is `Ind ...`.
- `T` is `A -> B` and `Ind` does not occur in `A`, and occurs strictly positive in `B`.

It must NOT occur in the domain of an arrow (negative occurrence).

## Elimination (Rec)

For `Ind` with constructors `C_1 : A_1 -> Ind ...`, the recursor `Ind.rec` has type:
`Pi (motive : Ind -> Sort u) ... (minor_1 : Pi args, motive (C_1 args)) ... -> Pi (x : Ind), motive x`
