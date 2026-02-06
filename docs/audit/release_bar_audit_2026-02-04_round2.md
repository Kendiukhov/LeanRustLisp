# LRL Release-Bar Audit Report (Pre-Codegen Semantic Soundness) — 2026-02-04 Round 2

**Date:** February 4, 2026  
**Role:** LRL Release-Bar Auditor (Semantic Soundness Only, Pre-Codegen)  
**Scope:** kernel + frontend/elaboration/macro boundary + MIR lowering + NLL borrow checking + CLI/driver pipeline

## Executive Verdict

**GO for stdlib expansion**

- The updated function/closure kind spec aligns with implementation: elaborator infers minimal kind, kernel validates, MIR preserves call modes.
- Implicit binder observational-only rule is enforced in elaboration and kernel ownership checking, with negative tests.
- Kernel boundary remains enforced: the driver re-checks definitions and top-level expressions in the kernel.
- Prop-elimination restrictions are enforced in kernel and elaborator; tests cover Prop/Type boundaries.
- Totality boundary is enforced; partial terms are rejected in types and well-founded termination is checked.
- MIR lowering uses `Opaque` for unknown/runtime-erased types, preserving non-Copy semantics.
- NLL borrow checking remains projection/deref-aware and is executed for bodies and closures.
- Macro boundary for prelude is explicit (deny + allowlist), and macro hygiene/determinism tests remain in place.

## Docs Reviewed (Current Specs & Updates)

- `docs/spec/function_kinds.md` (updated Feb 4, 2026)
- `docs/spec/core_calculus.md`
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
| A1 | Kernel rechecks every definition and top-level expression | **PASS** | `cli/src/driver.rs` `Declaration::Expr` invokes `kernel::checker::check`; definitions admitted via `Env::add_definition`. |
| A2 | No production path can bypass kernel checks | **PASS** | `kernel/src/checker.rs` `Env::add_definition` rechecks type/value; `definitions` are private to `Env`. |
| A3 | Prelude macro boundary explicit + enforced (deny + allowlist) | **PASS** | `cli/src/compiler.rs` sets `MacroBoundaryPolicy::Deny` during prelude load and calls `set_prelude_macro_boundary_allowlist` (empty allowlist in `cli/src/lib.rs`). |
| B4 | Prop elimination restriction enforced | **PASS** | `kernel/src/checker.rs` `check_elimination_restriction`; `frontend/src/elaborator.rs` calls it before recursor use. |
| B5 | Prop restriction tests not ignored | **PASS** | No `#[ignore]` in kernel/frontend/mir/cli tests; Prop tests live in `kernel/tests/semantic_tests.rs` and `kernel/tests/negative_tests.rs`. |
| B6 | `eval`/Dyn blocked in types/defeq; no macro smuggling | **PASS** | `frontend/src/elaborator.rs` rejects `Eval` in type context; `kernel/src/checker.rs` `contains_partial_def` blocks `eval` in types. |
| C7 | Total `def` forbids `fix` | **PASS** | `kernel/src/checker.rs` `check_termination_with_hint` rejects `Fix` for Total; CLI negative tests in `cli/tests/pipeline_negative.rs`. |
| C8 | Partial terms cannot appear in types/defeq | **PASS** | `kernel/src/checker.rs` `contains_partial_def` on definition types before admission. |
| C9 | Well-founded recursion checked if supported | **PASS** | `kernel/src/checker.rs` `check_wellfounded_termination` for `Totality::WellFounded`. |
| D10 | MIR lowering preserves ownership semantics (no Unit/Copy erasure bypass) | **PASS** | `mir/src/lower.rs` lowers unsupported types to `MirType::Opaque`; `mir/src/types.rs` marks `Opaque` non-Copy. |
| D11 | NLL projection-aware and deref-aliasing aware | **PASS** | `mir/src/analysis/nll.rs` uses `resolve_place_at` and projection-aware conflict checks. |
| D12 | Copy semantics + Fn/FnOnce enforced, no Copy-by-fiat | **PASS** | `mir/src/types.rs` treats `Fn` non-Copy, `FnItem` Copy, `Closure` non-Copy; `mir/src/lower.rs` uses call operand kind (borrow/move). |
| D13 | Statement-level MIR typing/invariant checks exist | **PASS** | `mir/src/analysis/typing.rs` used during CLI compilation in `cli/src/compiler.rs` and `cli/src/driver.rs`. |
| E14 | Macro-introduced identifiers don’t capture call-site binders | **PASS** | `frontend/src/macro_expander.rs` scopes identifiers; `frontend/src/desugar.rs` resolves by scope compatibility. |
| E15 | Quasiquote/unquote respects hygiene | **PASS** | `frontend/src/macro_expander.rs` preserves scopes in quasiquote expansion. |
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
- Spec alignment: `kernel/tests/spec_alignment_tests.rs`

Missing tests:
- A MIR-level regression that asserts closures remain non-Copy even when their inferred kind is `Fn` and captures are Copy.
- A CLI-level regression for implicit binder observational-only behavior with a mut-borrow path (erroring before any FnMut inference).

Ignored tests:
- None found (`#[ignore]` not present in kernel/frontend/mir/cli tests).

## Suggested GitHub Issues

1. **Add MIR regression for closure non-Copy policy**  
   Severity: Medium  
   Subsystem: MIR Lowering / Ownership  
   Acceptance criteria: add a test that lowers an `Fn` closure capturing only Copy values and ensures the resulting local is non-Copy (Move used in MIR operands).

2. **Add explicit test for implicit binder mut-borrow rejection**  
   Severity: Low  
   Subsystem: Frontend / Kernel Ownership  
   Acceptance criteria: add a CLI or kernel test where an implicit non-Copy binder is passed to a parameter requiring mutable borrow and ensure the error is raised (not kind-upgraded).
