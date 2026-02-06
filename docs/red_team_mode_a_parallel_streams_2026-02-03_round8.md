# Red Team Mode A — Parallel Streams (Round 8)

This plan parallelizes the fix tasks from the latest Mode A report. Streams are non‑overlapping; dependencies are noted only when real.

## Stream A — Lifetime Params & Function Type Expressiveness
**Goal:** remove type‑based lifetime interning; support independent lifetimes for same‑type refs.

Tasks:
1) Introduce explicit or positional lifetime parameters on function types (surface + core + MIR).
2) Replace type‑based `RegionInterner` with explicit/positional lifetime IDs in lowering.
3) Add lifetime‑param inference rules (or minimal annotation support) in elaboration.

Files/folders:
- `frontend/src/desugar.rs`
- `frontend/src/elaborator.rs`
- `kernel/src/ast.rs`
- `mir/src/types.rs`
- `mir/src/lower.rs`
- `docs/spec/function_kinds.md`
- `docs/spec/mir/typing.md`
- `docs/spec/mir/borrows-regions.md`

Dependencies:
- Blocks Stream D lifetime tests (must land before those tests can pass).

## Stream B — Definitional Equality Policy & Fuel
**Goal:** avoid defeq false negatives; make fuel behavior explicit and configurable.

Tasks:
1) Define and implement a defeq policy (fuel, transparency behavior, diagnostics).
2) Expose a user‑level knob (CLI/env) and document it.

Files/folders:
- `kernel/src/nbe.rs`
- `kernel/src/checker.rs`
- `cli/src/main.rs`
- `cli/src/compiler.rs`
- `docs/spec/core_calculus.md`
- `README.md`

Dependencies:
- None.

## Stream C — Prelude Trust Boundary & Macro Safety
**Goal:** make macro boundary policy explicit for prelude; shrink/clarify TCB.

Tasks:
1) Document prelude trust boundary in spec/README.
2) Optionally switch prelude macro boundary to `Deny` with explicit allowlist.

Files/folders:
- `cli/src/compiler.rs`
- `frontend/src/macro_expander.rs`
- `docs/spec/kernel_boundary.md`
- `README.md`

Dependencies:
- None (can proceed independently; only coordinate if CLI flag semantics change).

## Stream D — MIR Typing Coverage & Tests
**Goal:** validate more of MIR lowering (beyond call terminators) and add lifetime tests.

Tasks:
1) Extend MIR typing checker to validate statement‑level typing.
2) Add negative/positive lifetime tests (e.g., `choose_left` scenario) once Stream A lands.

Files/folders:
- `mir/src/analysis/typing.rs`
- `mir/tests/borrowck_corpus.rs`
- `cli/tests/pipeline_negative.rs`
- `cli/tests/pipeline_golden.rs`

Dependencies:
- Lifetime tests depend on Stream A changes.

## Stream E — Spec Alignment & Guardrails
**Goal:** remove spec drift and add guards against future drift.

Tasks:
1) Update core calculus spec to include `FnMut`.
2) (Optional) add a CI guard or doc test to detect spec/impl drift.

Files/folders:
- `docs/spec/core_calculus.md`
- `docs/`
- (optional) CI config or new doc test location

Dependencies:
- None.

