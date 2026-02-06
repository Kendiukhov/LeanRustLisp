# Red Team Fix Plan — Parallel Streams (2026-02-02)

This splits the fix plan into non-overlapping parallel streams so multiple agents can work independently.

## Stream A — Ownership/Copy Soundness (Kernel)
- Validate `copy` inductives structurally or mark `copy` as unsafe.
  - Touchpoints: `kernel/src/checker.rs`, `kernel/src/ast.rs`.
  - Tests: negative test for `copy` wrapper around non-copy resource.
- Refine ownership checks for inductive fields; deny `copy` when any ctor field is non-copy.
  - Touchpoints: `kernel/src/checker.rs` (inductive soundness).

## Stream B — Axiom/Effect Boundary Enforcement
- Move borrow/index primitives out of axiom/total fragment.
  - Touchpoints: `stdlib/prelude.lrl`, `frontend/src/declaration_parser.rs`, `kernel/src/checker.rs` (effect checks).
  - Tests: total defs calling `borrow_*` / `index_*` rejected.
- Add effect-type boundary for `eval`.
  - Touchpoints: `frontend/src/desugar.rs`, `frontend/src/elaborator.rs`, `kernel/src/checker.rs`.
  - Tests: `eval` in type position rejected.

## Stream C — Axiom & Classical Dependency Tracking
- Track axiom dependencies through inductives and recursors.
  - Touchpoints: `kernel/src/ast.rs`, `kernel/src/checker.rs`, `cli/src/driver.rs`.
  - Tests: inductive depending on classical axiom reports deps.
- Add axiom audit pass for stdlib (tags + diagnostics).
  - Touchpoints: `stdlib/prelude.lrl`, `cli/src/driver.rs` reporting.

## Stream D — Prop & Invariant Validation in Kernel
- Run core invariant validation on inductive types/ctors (metas/recursor levels).
  - Touchpoints: `kernel/src/checker.rs` (`Env::add_inductive`).
- Ensure Prop inductive constructors are type-safe (partial defs disallowed).
  - Touchpoints: `kernel/src/checker.rs` (universe check or separate pass).

## Stream E — Recursor Universe Levels (Elaboration)
- Fix recursor universe levels in elaborator (params + motive).
  - Touchpoints: `frontend/src/elaborator.rs` (`elaborate_match`, `infer_rec_application`).
  - Tests: polymorphic inductive + match succeeds.

## Stream F — Primitive Name Hardening (Driver/Kernel)
- Reserve primitive names at kernel/driver level to prevent shadowing (`borrow_*`, `index_*`).
  - Touchpoints: `cli/src/driver.rs` or kernel env API.
  - Tests: redefining `borrow_mut` errors.

## Stream G — Defeq Budget Diagnostics
- Surface defeq fuel exhaustion as a distinct error with actionable diagnostics.
  - Touchpoints: `kernel/src/checker.rs`, `cli/src/driver.rs`.
  - Tests: defeq fuel exhaustion emits clear error.

## Stream H — Panic-Free Lints & Tests (MIR)
- Add panic-free lint coverage for indexing/borrow axioms.
  - Touchpoints: `mir/src/lints.rs`, `mir/tests/*`.
  - Tests: `panic_free` mode rejects unsafe indexing/borrow usage.

