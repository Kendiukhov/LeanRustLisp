# Red Team Mode A — Parallel Streams (Round 9)

This plan parallelizes the fix tasks from the Round 9 report. Streams are non‑overlapping; dependencies are listed only when real.

## Stream A — Structural Lifetime Labels
**Goal:** make lifetime labels part of the core term structure and preserve them through transformations.

Tasks:
1) Extend core term representation (or Ref node) to carry optional lifetime labels.
2) Update `shift`/`subst` and any term rebuilders to preserve labels.
3) Update MIR lowering to read labels from the term itself (stop using pointer maps).

Files/folders:
- `kernel/src/ast.rs`
- `kernel/src/checker.rs`
- `frontend/src/elaborator.rs`
- `mir/src/lower.rs`
- `docs/spec/ownership_model.md`
- `docs/spec/mir/typing.md`

Dependencies:
- Blocks Stream D lifetime regression tests (labels must be structural first).

## Stream B — Kernel Validation of Lifetime Labels
**Goal:** ensure labels are well‑formed and reject ambiguous/misapplied labels at the kernel boundary.

Tasks:
1) Add kernel validation for label usage (only on Ref, no stale/unknown labels).
2) Validate elision invariants on core terms (mirror elaborator checks).

Files/folders:
- `kernel/src/checker.rs`

Dependencies:
- Depends on Stream A if labels move into core; otherwise can proceed in parallel.

## Stream C — Definitional Equality Policy & Diagnostics
**Goal:** make defeq fuel behavior explicit and user‑controllable.

Tasks:
1) Define defeq policy (fuel/transparency) and emit actionable diagnostics.
2) Expose CLI/env knob and document it.

Files/folders:
- `kernel/src/nbe.rs`
- `kernel/src/checker.rs`
- `cli/src/main.rs`
- `README.md`
- `docs/spec/core_calculus.md`

Dependencies:
- None.

## Stream D — MIR Typing Coverage & Lifetime Tests
**Goal:** reduce reliance on lowering correctness; add lifetime regression tests.

Tasks:
1) Extend MIR typing checker to validate statements (not only call terminators).
2) Add labeled‑lifetime regression tests in MIR/CLI.

Files/folders:
- `mir/src/analysis/typing.rs`
- `mir/tests/borrowck_corpus.rs`
- `cli/tests/pipeline_golden.rs`
- `cli/tests/pipeline_negative.rs`

Dependencies:
- Lifetime tests depend on Stream A (labels must be structural).

## Stream E — Spec Alignment
**Goal:** remove spec drift and document lifetime label syntax.

Tasks:
1) Update core calculus spec to include `FnMut`.
2) Document `Ref #label Shared T` / elision rules in ownership + MIR specs.

Files/folders:
- `docs/spec/core_calculus.md`
- `docs/spec/ownership_model.md`
- `docs/spec/mir/typing.md`
- `docs/spec/mir/borrows-regions.md`

Dependencies:
- None.

