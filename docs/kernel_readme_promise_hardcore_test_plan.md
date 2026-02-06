# Kernel README Promise Hardcore Tests - Parallel Plan

## Goal
Build an expanded, adversarial kernel test suite that probes extreme/edge cases for README promises (soundness, total/partial/unsafe boundaries, Prop/computation separation, inductives, defeq, reserved primitives, axiom tracking). The focus is kernel-level invariants; compiler/erasure passes are out of scope.

## Rules of Engagement
- Tests live in `kernel/tests/readme_promises_tests.rs` unless a dedicated file is justified.
- Prefer minimal core terms; avoid frontend/macro assumptions.
- Each test should target a single invariant and include at least one adversarial/edge variant.
- Add explicit comments describing which README promise/invariant the test defends.
- Keep failures crisp: match specific `TypeError` when possible.

---

## Stream A - Prop / Computational Irrelevance Boundaries
Owner: Agent A

Scope: Prove the kernel enforces computational irrelevance of Prop and limited elimination.

Tasks
1) Prop field rejection under reduction
   - Construct a data inductive where a field type reduces to Prop (via a transparent def), verify `PropFieldInData` is raised.
   - Add a control case where the def is opaque (should not reduce to Prop), and ensure the check still holds if intended.
2) Elimination restrictions
   - Negative: eliminate a non-singleton Prop into Type (already in suite) but add a case with indices/parameters.
   - Positive: singleton Prop elimination into Type (already added) plus a variant with Prop-only fields.
3) Prop universe vs Type universe edge
   - Build a Pi whose codomain reduces to Prop to confirm resulting Sort is Prop and does not permit data extraction.
4) Axiom tracking around Prop
   - Define a Prop axiom tagged Classical, use it through a chain of defs; ensure tags propagate to the final def.

Deliverables
- New tests for reduced-to-Prop fields, indexed Prop elimination, and transitive classical tag propagation.

---

## Stream B - Definitional Equality & Transparency Extremes
Owner: Agent B

Scope: Stress defeq against transparency modes, zeta/eta, and fuel exhaustion.

Tasks
1) Transparency boundaries
   - Same term compared under `Transparency::None` vs `Reducible` vs `All`, prove defeq differs only where intended.
   - Opaque def should fail defeq unless `All` (if supported).
2) Zeta / Eta in nested contexts
   - Let-bound nested in Pi/Lam; ensure defeq handles zeta only with appropriate transparency.
   - Eta for higher-order functions with dependent types.
3) Defeq fuel exhaustion surfaces
   - Add a tiny looping defeq case that exhausts fuel and assert `DefEqFuelExhausted { context: ... }` context is correct.

Deliverables
- Tests that clearly show defeq behavior varies by transparency and fuel.

---

## Stream C - Totality, Termination & Well-Founded Recursion
Owner: Agent C

Scope: Extreme recursion/termination cases and proof checks.

Tasks
1) Mutual recursion chain
   - Two or three defs with structural recursion on different params; ensure termination check rejects invalid recursion paths.
2) Indirect recursion via aliases
   - Chain of lets/defs that re-alias a recursive call; ensure termination catches it (generalizes the existing negative case).
3) Well-founded recursion proof mismatch
   - Provide an Acc proof for a different target or relation; ensure `WellFoundedError::AccProofMismatch` (or equivalent) is raised.
4) Acc proof missing param
   - Define a wf recursion with missing Acc parameter and assert correct error.

Deliverables
- New termination tests emphasizing alias chains, mutual recursion, and wf proof mismatch.

---

## Stream D - Inductives: Positivity, Indices, Universes
Owner: Agent D

Scope: Check the kernel’s inductive soundness rules at the boundaries.

Tasks
1) Nested negative occurrence
   - Construct a strictly non-positive inductive that hides the occurrence under multiple Pis/apps.
2) Param/index arity mismatch
   - Inductive whose constructor returns an inductive applied to wrong number of params/indices; assert error.
3) Recursor level count mismatch
   - For an inductive with universe params, give wrong recursor level list; assert error.
4) Data vs Prop field constraints
   - Data inductive with a field whose type reduces to Prop via a def (overlaps Stream A but on indices to vary coverage).

Deliverables
- Expanded inductive edge-case tests; ensure coverage beyond existing positivity and recursor tests.

---

## Stream E - Effects, Reserved Primitives, Axiom Tags
Owner: Agent E

Scope: Ensure safety/effect boundaries and primitive gating are ironclad.

Tasks
1) Effect boundary across defs
   - Chain Total -> Total -> Partial -> Unsafe (through intermediate defs), verify effect errors are raised at each boundary.
2) Reserved primitives gating
   - Ensure `allow_reserved_primitives` is required, unsafe tag required for index primitives, and signature checks on borrow/index fail when malformed.
   - Add a shadowing attempt test (reserved name redefinition) that fails when already defined.
3) Axiom tag propagation
   - Mix classical + unsafe tags in defs and inductives; verify `axiom_dependencies_with_tag` isolates each.

Deliverables
- New tests for multi-hop effect chains and reserved primitive name/unsafe/signature invariants.

---

## Integration & Execution
- Each agent should add tests in a feature-consistent style and run `cargo test -p kernel --test readme_promises_tests`.
- Coordinate for duplicate coverage: note shared areas between A/D and A/E.
- Once all streams land, run `cargo test -p kernel --test readme_promises_tests` and optionally `cargo test -p kernel --tests` for regression.

## Definition of Done
- Each stream adds 2–4 robust edge-case tests.
- All tests pass locally.
- README promise coverage includes Prop irrelevance, totality/effects, inductive soundness, defeq/transparency, axiom tracking, and reserved primitives.
