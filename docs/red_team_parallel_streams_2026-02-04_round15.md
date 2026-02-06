# Red Team Round 15: Parallel Streams Plan

This is a parallelization plan for the fix tasks listed in `red_team_mode_a_report_2026-02-04_round15.md`. Streams are designed to avoid overlap; dependencies are stated **between streams** below.

**Stream A — Kernel/TCB Integrity (Names + Redefinition + Axiom Tags)**
- A1. Reject redefinition of existing definitions/inductives by default in `kernel/src/checker.rs` (`add_definition`, `add_inductive`).
- A2. Reserve core prelude names (`Comp`, `Eq`, `Nat`, `Bool`, `List`, `False`, etc.) in `kernel/src/ast.rs` and enforce in `add_*`.
- A3. Snapshot axiom tag dependencies at definition time (avoid dynamic lookup in `axiom_dependencies_with_tag`) so tags can’t be laundered after redefinition.

**Stream B — Borrow/NLL Closure Soundness**
- B1. Model closure self-borrow in MIR types (explicit `&self` or region parameter tied to the closure value) in `mir/src/types.rs` + `mir/src/lower.rs`.
- B2. Update NLL to create loans or lifetime constraints for `CallOperand::Borrow` when returns are ref-typed (`mir/src/analysis/nll.rs`).
- B3. Update `call_operand_type` and `normalize_callable_type` to preserve self-borrow semantics for closures.

**Stream C — Opaque Semantics Consistency**
- C1. Decide and implement consistent `opaque` behavior for Prop checks and borrow-shape inference.
  - Option 1 (strict): do not unfold `opaque` in `is_prop_like` and MIR borrow shape.
  - Option 2 (documented exception): keep unfolding, but add explicit diagnostics and documentation.
- C2. Update README and error messages if exceptions are retained.

**Stream D — CLI/Driver Boundary Controls**
- D1. Add a “prelude frozen” guard after prelude load in `cli/src/driver.rs` to block redefinitions unless an explicit flag is set.
- D2. Emit diagnostics when redefinition is attempted post-prelude.

**Stream E — Tests & Corpus Expansion**
- E1. Borrowck corpus tests for closure returning ref to owned capture (should fail).
- E2. Kernel tests for redefinition rejection and reserved names.
- E3. Tests for axiom tag stability against redefinition.
- E4. README promise tests for `opaque` semantics (Prop field + defeq transparency).

**Stream F — Diagnostics & Docs Cleanup**
- F1. Update README trust-boundary statements (ownership/effects in kernel) until refactor lands.
- F2. Add diagnostics for `opaque` unfolding if exception remains.
- F3. Add docs note on panic-free profile restrictions (RefCell/index/borrow).

**Stream Dependencies (Between Streams Only)**
- Stream D depends on Stream A (kernel-level redefinition/TCB guard must exist before CLI policy enforcement is consistent).
- Stream E depends on Streams A, B, and C (tests must match the finalized semantics).
- Stream F depends on Stream C decisions (docs/diagnostics must reflect `opaque` policy).
- Stream B is independent of Streams A/C/D; can run in parallel.
- Stream C is independent of Streams A/B/D; can run in parallel.

