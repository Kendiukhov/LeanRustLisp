AGENT TASK: Implement Impredicative `Prop` (Lean-style) in the Kernel - Completed

Primary area: kernel/src/checker.rs, kernel/src/ast.rs, kernel/src/parser.rs (core syntax), plus tests.

Goal
Make `Prop` impredicative in the kernel semantics: Π-types whose codomain is `Prop` should themselves be in `Prop`, even if the domain ranges over higher universes (within the intended Lean-style rule). Ensure this is reflected consistently in:
- universe level computation for Π
- definitional equality / normalization (if applicable)
- parser surface/core handling for `Prop` and `Type`
- tests that pin the intended behavior

Current state assumption
- `Prop` is represented as `Sort(Level::Zero)` (as in current parser/checker tests).
- `Type 0` is represented as `Sort(Succ(Zero))` or similar.
- There is already a helper `level_imax(l1, l2)` with the “if codomain is Prop -> Prop” behavior, but verify it is applied correctly everywhere and matches Lean’s intended semantics.

Deliverables
A) Short design note (Markdown or top-of-file comment) answering:
1) What is `Prop` in this kernel? (Sort level conventions)
2) Exact Π universe rule used (impredicative Prop rule via imax)
3) What is allowed / disallowed regarding elimination from `Prop` into `Type`? (Even if not implemented yet, document planned restriction, since impredicativity + proof erasure needs it.)
4) How this differs from predicative Prop.

B) Implementation changes
1) Confirm or adjust universe conventions
- Ensure `Prop` is consistently `Sort(Zero)` at the core term level.
- Ensure `Type 0` is consistently `Sort(Succ(Zero))`.
- Fix any inconsistencies (notably: frontend elaborator currently maps "Type" to Sort(Zero); that likely must be Type 0 instead—investigate and correct).

2) Implement/verify Π universe rule (impredicative Prop)
In kernel type inference for `Pi(ty, body)`:
- Let `s1 = infer(A)` and `s2 = infer(B)` return sorts `Sort u` and `Sort v`.
- Universe of Π is `Sort(imax(u, v))` where:
  - `imax(u, 0) = 0` (Prop is impredicative)
  - otherwise `imax(u, v) = max(u, v)` (or your chosen universe max rule)
- Ensure this rule is the single source of truth (do not scatter).
- Ensure `reduce_level` correctly normalizes `IMax`/`Max` shapes to keep equality stable.

3) Ensure definitional equality respects universe behavior
- If definitional equality compares sorts, it should compare reduced levels (or canonical forms).
- If you introduce `IMax` explicitly in levels, ensure defeq normalization reduces it consistently.

4) Update core parser / frontend elaborator to avoid “Type means Prop” mistakes
- kernel/src/parser.rs currently maps `Prop` and `Type` in a simplified way; ensure:
  - `Prop` maps to `Sort(Zero)`
  - `Type` maps to `Sort(Succ(Zero))` (Type 0)
- frontend/src/elaborator.rs currently resolves "Type" incorrectly (it maps to Sort(Zero)). Fix it to map to `Type 0`.
- Any surface syntax that uses `(sort 0)` or `(sort 1)` must be documented and consistent.

C) Tests (must add; do not rely only on existing tests)
Add kernel-level tests covering impredicativity:
1) Impredicative Π stays in Prop:
   - Term: `Π (A : Type 0), Prop` should have type `Type 0` (as a term), but the Π itself should be `Prop` when codomain is `Prop`.
   - Concretely: build `Pi(Type0, Prop)` and verify `infer` returns `Sort(Zero)` for the Π term’s sort.

2) (p : Prop) → p is Prop:
   - Term: `Pi(Prop, Var(0))` should infer to `Prop`.

3) (A : Type 0) → A is Type 1 (not Prop)
   - Term: `Pi(Type0, Var(0))` should infer to `Sort(Succ(Type0))` or equivalent (depending on your level conventions), but critically: NOT Prop.

4) Mixed universe:
   - `Pi(Prop, Type0)` should infer to `Type0` (or the appropriate max/imax result), not Prop.

5) Regression test for `Type` token resolution in frontend elaborator:
   - A simple surface term referencing `Type` should elaborate to core `Sort(Succ(Zero))`, not `Sort(Zero)`.

Acceptance criteria (“done means done”)
- Π universe inference uses an explicit impredicative Prop rule (imax codomain=Prop => Prop).
- `Prop` and `Type` are consistently represented across kernel parser, elaborator, and tests.
- Tests demonstrating impredicativity pass and remain stable.
- A design note exists stating the rule and planned elimination restrictions.

Optional but recommended follow-ups (if time remains)
- Add the initial restriction for elimination from `Prop` into `Type` (to preserve proof erasure sanity): i.e., forbid pattern matching on proofs to compute data. Even a placeholder “Not yet implemented; rejected by checker” is better than silently allowing it.
- Add a “Sort pretty printer” or debugging helper that prints `Prop`, `Type 0`, `Type 1` clearly.

Important note
Impredicative Prop is only half the story; to keep the system coherent (and enable proof erasure), you will likely need a policy like proof-irrelevance / restricted elimination from Prop. Document this now even if you implement it later.

