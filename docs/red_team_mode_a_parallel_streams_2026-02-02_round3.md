# Red Team Fix Plan — Parallel Streams (Round 3, 2026-02-02)

This plan parallelizes the Round 3 fix tasks (fix/totality + closure-kind soundness). Streams are designed to avoid overlap; dependencies are explicit where needed.

## Stream A — Kernel Gate: `fix` in Total Fragment
- Tasks: Reject `fix` in `def` (total) values; align `check_effects` with partial-only recursion; add kernel error paths.
- Files/Folders: `kernel/src/checker.rs`, `kernel/src/ast.rs`, `kernel/src/nbe.rs` (guardrails).
- Dependencies: None (can proceed independently).

## Stream B — Kernel Revalidation of Function Kinds
- Tasks: Recompute/validate required kind in kernel (conservative); reject `Fn` closures that consume captures; add diagnostics.
- Files/Folders: `kernel/src/checker.rs`, `kernel/src/ownership.rs`.
- Dependencies: None (can proceed independently).

## Stream C — Implicit Binder Enforcement
- Tasks: Define and enforce implicit binder semantics (observational-only or Prop-only) in kernel; add clear errors.
- Files/Folders: `kernel/src/checker.rs`, `kernel/src/ast.rs` (if binder constraints are encoded).
- Dependencies: None, but must align with Stream D’s inference behavior.

## Stream D — Elaborator Kind Inference + Implicit Arg Rules
- Tasks: Update `infer_needs_fn_once` to treat implicit args conservatively; block under-approximation of `FnOnce`.
- Files/Folders: `frontend/src/elaborator.rs`, `frontend/src/desugar.rs` (if syntax changes needed).
- Dependencies: Stream C (kernel-level implicit binder semantics).

## Stream E — Parsing/Elaboration Guardrails for `fix`
- Tasks: Early error on `fix` inside total `def`; allow for `partial def` only.
- Files/Folders: `frontend/src/elaborator.rs`, `frontend/src/declaration_parser.rs`, `cli/src/driver.rs` (diagnostics).
- Dependencies: Stream A (kernel policy is source of truth).

## Stream F — Defeq DoS Guardrails
- Tasks: Add explicit defeq guardrails for `fix` (fail fast); ensure diagnostics are actionable.
- Files/Folders: `kernel/src/nbe.rs`, `kernel/src/checker.rs`, `cli/src/driver.rs`.
- Dependencies: Stream A (semantic policy for `fix`).

## Stream G — Tests & Regression Suite
- Tasks: Add tests for `fix` rejection in total defs; implicit-arg closure kind repro; defeq fuel diagnostics; kernel kind validation failures.
- Files/Folders: `tests/`, `kernel/tests`, `frontend/tests`, `cli/tests`.
- Dependencies: Streams A–F (depends on concrete behavior).

## Stream H — Documentation Updates
- Tasks: Specify implicit binder semantics; update function-kind spec (incl. FnMut roadmap if desired); document `fix` as partial-only.
- Files/Folders: `docs/spec/function_kinds.md`, `docs/spec/ownership_model.md`, `docs/spec/core_calculus.md`, `docs/production.md`.
- Dependencies: Streams A–D (align doc with final rules).
