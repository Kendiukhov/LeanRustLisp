# LRL Release-Bar Audit Report (Pre-Codegen Semantic Soundness) — 2026-02-04

**Date:** February 4, 2026  
**Role:** LRL Release-Bar Auditor (Semantic Soundness Only, Pre-Codegen)  
**Scope:** kernel + frontend/elaboration/macro boundary + MIR lowering + NLL borrow checking + CLI/driver pipeline

## Executive Verdict

**GO for stdlib expansion**

- Kernel re-check is enforced for definitions and top-level expressions in the driver.
- Kernel boundary remains intact: definitions are admitted only via `Env::add_definition` and validated.
- Prop elimination restrictions are enforced at kernel and elaborator, with dedicated tests.
- Totality boundary (fix/partial/well-founded) is enforced in the kernel and exercised in CLI tests.
- MIR lowering now preserves ownership semantics for unknown types by using `MirType::Opaque` (non-Copy).
- NLL borrow checking is projection/deref aware and is run for both top-level bodies and closures.
- Macro boundary for prelude is explicit and enforced with deny + allowlist.
- Macro hygiene and determinism are covered by frontend macro expansion tests.

## Docs Reviewed (Current Specs & Updates)

- `docs/spec/core_calculus.md`
- `docs/spec/function_kinds.md`
- `docs/spec/kernel_boundary.md`
- `docs/spec/macro_system.md`
- `docs/spec/phase_boundaries.md`
- `docs/spec/ownership_model.md`
- `docs/spec/mir/borrows-regions.md`
- `docs/spec/mir/typing.md`
- `docs/macro_system.md`
- `docs/production.md`

## Release Bar Checklist

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| A1 | Kernel rechecks every definition and top-level expression | **PASS** | `cli/src/driver.rs` `Declaration::Expr` calls `kernel::checker::check` in empty `Context` and definitions use `Env::add_definition`. |
| A2 | No production path can bypass kernel checks | **PASS** | `kernel/src/checker.rs` `Env` keeps `definitions` private; admission via `add_definition` only. |
| A3 | Prelude macro boundary explicit + enforced (deny + allowlist) | **PASS** | `cli/src/compiler.rs` sets `MacroBoundaryPolicy::Deny` for prelude; `cli/src/lib.rs` allowlist exists (empty). |
| B4 | Prop elimination restriction enforced | **PASS** | `kernel/src/checker.rs` `check_elimination_restriction` called for `Term::Rec`; `frontend/src/elaborator.rs` checks before recursor application. |
| B5 | Prop restriction tests not ignored | **PASS** | Prop-elim tests in `kernel/tests/semantic_tests.rs` and `kernel/tests/negative_tests.rs`; no `#[ignore]` found in test suites. |
| B6 | `eval`/Dyn blocked in types/defeq; no macro smuggling | **PASS** | `frontend/src/elaborator.rs` rejects `Eval` in type context; `kernel/src/checker.rs` `contains_partial_def` rejects `eval` in types. |
| C7 | Total `def` forbids `fix` | **PASS** | `kernel/src/checker.rs` termination check rejects `Fix` in Total/WellFounded; CLI negative tests in `cli/tests/pipeline_negative.rs`. |
| C8 | Partial terms cannot appear in types/defeq | **PASS** | `kernel/src/checker.rs` `contains_partial_def` applied to definition types before admission. |
| C9 | Well-founded recursion checked if supported | **PASS** | `kernel/src/checker.rs` `add_definition` invokes `check_wellfounded_termination` for `Totality::WellFounded`. |
| D10 | MIR lowering preserves ownership semantics (no Unit erasure bypass) | **PASS** | `mir/src/lower.rs` lowers unknown apps/vars to `MirType::Opaque`; `mir/src/types.rs` marks `Opaque` as non-Copy. |
| D11 | NLL projection-aware and deref-aliasing aware | **PASS** | `mir/src/analysis/nll.rs` `resolve_place_at` expands deref chains; `places_conflict_base` handles projections. |
| D12 | Copy semantics + Fn/FnOnce enforced, no Copy-by-fiat | **PASS** | `kernel/src/checker.rs` validates function kinds; `mir/src/lower.rs` uses call operands by kind; `cli/tests/typing_mir_calls.rs` covers call typing. |
| D13 | Statement-level MIR typing/invariant checks exist | **PASS** | `mir/src/analysis/typing.rs` used in `cli/src/compiler.rs` and `cli/src/driver.rs` for bodies and closures. |
| E14 | Macro-introduced identifiers don’t capture call-site binders | **PASS** | `frontend/src/macro_expander.rs` assigns fresh scopes; `frontend/src/desugar.rs` resolves by scope compatibility. |
| E15 | Quasiquote/unquote respects hygiene | **PASS** | `frontend/src/macro_expander.rs` quasiquote expansion preserves scopes and inserts syntax objects. |
| E16 | Macro expansion deterministic and tested | **PASS** | `frontend/tests/macro_expansion_tests.rs` includes determinism and hygiene snapshots. |

## Blockers (Must Fix Before Stdlib Expansion)

- None found for the current release bar.

## High Severity Issues

- None found for the current release bar.

## Tests Status

Soundness tests present:
- Kernel: `kernel/tests/semantic_tests.rs`, `kernel/tests/negative_tests.rs`, `kernel/tests/readme_promises_tests.rs`
- Frontend: `frontend/tests/macro_expansion_tests.rs`, `frontend/tests/elaboration_tests.rs`
- MIR: `mir/tests/borrowck_corpus.rs`, `mir/src/analysis/nll_tests.rs`, `mir/src/analysis/typing.rs` tests
- CLI: `cli/tests/pipeline_golden.rs`, `cli/tests/pipeline_negative.rs`, `cli/tests/typing_mir_calls.rs`

Missing tests:
- A regression test that asserts unknown/opaque type lowering does not permit Copy on projections (MIR-level).
- A small MIR-level test that confirms function values are not copied when used as arguments (per `docs/spec/mir/borrows-regions.md`).

Ignored tests:
- None found (`#[ignore]` not present in kernel/frontend/mir/cli tests).

## Suggested GitHub Issues

1. **Add MIR regression to lock opaque-type non-Copy behavior**
   Severity: Medium  
   Subsystem: MIR Lowering / Ownership  
   Acceptance criteria: add a MIR test where a field type lowers to `Opaque` and a `Copy` operand on that projection is rejected by ownership or typing.

2. **Align MIR argument lowering with non-Copy function value policy**
   Severity: Medium  
   Subsystem: MIR Lowering / Ownership  
   Acceptance criteria: ensure `local_operand` does not use `Copy` for `MirType::Fn` (or update spec to explicitly allow copy-like use); add a regression test that passes a function value as an argument and ensures move semantics are respected in MIR.
