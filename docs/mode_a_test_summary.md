# Mode A Test Engineer Summary

## Scope Covered
- Kernel semantics coverage (impredicative Prop, defeq beta/delta/zeta/iota, substitution, inductive soundness).
- Prop elimination restrictions (large elimination errors + singleton Prop allowance).
- Frontend macro expansion determinism + hygiene snapshots and elaboration stability.
- MIR lowering + NLL borrow checker corpus (accept/reject) and panic-free lint checks.
- Unified pipeline stability via file-driven golden snapshots and negative diagnostics.

## New/Updated Tests
- `kernel/tests/semantic_tests.rs`
  - Added Nat.rec iota reduction on zero case.
  - Added allowed large elimination for singleton Prop.
  - Added Prop-elimination restriction regression (Prop -> Type rejected).
- `frontend/tests/elaboration_tests.rs`
  - Added Prop-elimination restriction rejection during elaboration.
  - Added match exhaustiveness + duplicate-case rejection.
- `kernel/tests/negative_tests.rs`
  - Added non-positive occurrence detection for inductives.
  - Added constructor not returning inductive + arity mismatch checks.
  - Added partial-in-type rejection.
  - Added large elimination rejection for Prop with multiple constructors.
- `cli/tests/golden/kernel/list_length.lrl`
  - Parametric List + length using match on `List Nat`.
- `cli/tests/golden/frontend/match_let_shadow.lrl`
  - Match/let shadowing edge cases.
- `cli/tests/golden/mir/match_nested_let.lrl`
  - Nested match/let lowering for MIR stability.
- `cli/tests/pending_borrow_surface.rs` + `tests/pending/borrow_surface.lrl`
  - Ignored placeholder for future surface borrow syntax.
- `cli/tests/pipeline_golden.rs`
  - Added classical axiom dependency artifact snapshot.
- `kernel/tests/semantic_tests.rs`
  - Implemented classical axiom tracking (classical vs non-classical) regression.

## Known Gaps / Next Steps
- Surface ref/borrow syntax not available yet; enable pending test when parser lands.
- Classical dependency tagging is now surfaced in pipeline artifacts.
- Expand golden corpus further once new surface syntax and features stabilize.
