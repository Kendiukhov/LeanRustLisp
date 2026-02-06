# Parallel Streams — Mode A Fix Plan (2026-02-03 Round 1)

Goal: Split the fix plan from the latest Mode A report into parallel, non-overlapping streams. If any stream touches shared files, tasks are scoped to distinct sections and dependencies are noted.

## Stream A — Termination & Defeq Soundness
**Scope:** Close totality holes; add regression tests; improve defeq error reporting.
- Task A1: Reject bare self-reference in total defs (termination checker must not accept `def f := f`).
- Task A2: Validate recursive calls through `let` aliasing (no indirect recursion escapes).
- Task A3: Add regression tests for non-terminating total defs (negative tests).
- Task A4: Improve defeq fuel exhaustion error reporting (more context in diagnostics).

**Dependencies:**
- A3 depends on A1+A2 (tests should reflect the fixed behavior).
- A4 independent.

**Primary files/folders:**
- `kernel/src/checker.rs` (termination + error mapping sections)
- `kernel/tests/negative_tests.rs`
- `kernel/tests/defeq_budget_tests.rs`

## Stream B — Borrowing & Ref Copy Semantics
**Scope:** Make borrowing usable in safe code (or enforce explicit unsafe), align Copy semantics across kernel/MIR/spec, update docs/tests.
- Task B1: Decide borrowing policy; either make `borrow_shared`/`borrow_mut` total or require `unsafe` surface for `&`/`&mut`.
- Task B2: Teach kernel Copy checker that `Ref Shared A` is Copy and `Ref Mut A` is not.
- Task B3: Add cross-phase regression tests for shared-ref Copy (kernel + MIR).
- Task B4: Update spec docs to match chosen borrowing policy.

**Dependencies:**
- B2 precedes B3 (tests depend on semantics).
- B1 precedes B4 (docs depend on policy).

**Primary files/folders:**
- `stdlib/prelude.lrl`
- `frontend/src/desugar.rs`
- `kernel/src/checker.rs` (is_copy_type + effect boundaries)
- `mir/src/types.rs`
- `kernel/tests/semantic_tests.rs`
- `mir/tests/borrowck_corpus.rs`
- `docs/spec/ownership_model.md`
- `docs/spec/kernel_boundary.md`

## Stream C — Macro Explicitness & Reserved Forms
**Scope:** Prevent core-form shadowing; ensure macro outputs preserve explicit unsafe/classical forms; add tests.
- Task C1: Reserve core forms (`def`, `axiom`, `unsafe`, `partial`, `instance`, `inductive`, etc.).
- Task C2: Emit diagnostics when macros expand into unsafe/classical constructs.
- Task C3: Add macro compliance tests (reserved names + explicitness).

**Dependencies:**
- C3 depends on C1 (tests expect reservation behavior).
- C2 independent, but better after C1 to avoid confusing diagnostics on already-reserved names.

**Primary files/folders:**
- `frontend/src/macro_expander.rs`
- `frontend/tests/*`
- `docs/spec/macro_system.md`

## Stream D — Function Kinds (FnMut)
**Scope:** Implement FnMut per roadmap and adjust inference/coercions.
- Task D1: Add `FnMut` to `FunctionKind` and update parser/desugar.
- Task D2: Update ownership/inference to classify mutable captures as FnMut.
- Task D3: Add tests for Fn/FnMut/FnOnce coercions and mutable-capture behavior.

**Dependencies:**
- D2 depends on D1.
- D3 depends on D1+D2.

**Primary files/folders:**
- `kernel/src/ast.rs`
- `kernel/src/checker.rs` (function kind inference)
- `frontend/src/desugar.rs`
- `frontend/src/elaborator.rs`
- `docs/spec/function_kinds.md`
- `frontend/tests/*`
- `kernel/tests/*`

## Cross-stream coordination notes
- `kernel/src/checker.rs` is touched in Streams A, B, and D, but in distinct sections (termination, Copy/effects, function-kinds). Parallel edits are okay if agents avoid overlapping hunks and rebase before merge.
- `frontend/src/desugar.rs` is touched in Streams B and D (borrow syntax vs function kinds). Coordinate to avoid adjacent edits.
