# Pattern Matching

Pattern matching is a surface-level feature that compiles to recursors. The precise syntax is in
`docs/spec/syntax_contract_0_1.md` ("(match ...)").

```lisp
(match scrutinee ReturnType (case (Ctor x1 ... xk) body) ...)      ; constant motive
(match scrutinee (motive M) (case (Ctor x1 ... xk) body) ...)      ; explicit dependent motive
```

## Patterns

A pattern is one constructor applied to variables: the constructor's explicit fields in order,
each recursive field followed by its induction hypothesis (`(case (succ k ih) ...)`). Patterns are
not nested; nested matching is written with nested `match`.

## Exhaustiveness

A match must have exactly one case per constructor of the inductive type. Missing, duplicate or
unknown cases are compile-time errors. Cases that are impossible for the scrutinee's indices must
still be written (against the motive, e.g. returning a unit value).

## Motives

With a constant return type, every case and the whole match have that type. With
`(motive M)`, `M` is a function over the scrutinee type's indices and the scrutinee, returning a
sort; each case is checked against `M` at its constructor's indices and value, induction
hypotheses have type `M` at the recursive field, and the match has type `M` at the scrutinee's
indices and the scrutinee. This is how dependent results are written (a total `head` on
`Vec A (succ n)`, `append` with result length `add n m`, proofs by induction).

## Compilation

A `match` elaborates to one application of the inductive's recursor (`Rec`): parameters, motive,
one minor premise per case (a function of the pattern variables), the scrutinee's indices and the
scrutinee. Recursion happens only through induction hypotheses, so every match is structurally
recursive; general recursion needs `fix` in a `partial` definition.
