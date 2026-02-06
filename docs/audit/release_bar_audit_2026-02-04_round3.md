# LRL Release-Bar Audit Report (Pre-Codegen Semantic Soundness) — 2026-02-04 Round 3

**Date:** February 4, 2026  
**Role:** LRL Release-Bar Auditor (Semantic Soundness Only, Pre-Codegen)  
**Scope:** kernel + frontend/elaboration/macro boundary + MIR lowering + NLL borrow checking + CLI/driver pipeline

## Executive Verdict

**GO for stdlib expansion**

- Kernel boundary remains enforced: driver rechecks defs/exprs and `Env::add_definition` validates invariants before admission.
- Prop safety strengthened through opaque-aware `is_prop_like`, applied in elimination checks, Prop-field prohibition, and MIR erasure tagging.
- Eval/Dyn boundary is hardened across frontend, kernel type-safety, NbE (opaque eval), and macro boundary checks.
- Macro system matches the Syntax→Syntax spec; hygiene uses scope sets with deterministic expansion and traceable diagnostics.
- Borrow-shape lowering now sees through opaque aliases for `Ref` and interior mutability; NLL creates loans for all `Rvalue::Ref` and injects runtime checks.
- Function kinds (`Fn/FnMut/FnOnce`) are inferred and enforced in elaboration, validated in kernel, and preserved in MIR call operands.
- MIR typing + ownership + NLL are run for definitions and closures in the driver pipeline.

## Docs Reviewed (Current Specs & Updates)

- `docs/spec/core_calculus.md`
- `docs/spec/function_kinds.md`
- `docs/spec/kernel_boundary.md`
- `docs/spec/macro_system.md`
- `docs/spec/ownership_model.md`
- `docs/spec/phase_boundaries.md`
- `docs/spec/mode_boundaries.md`
- `docs/spec/mir/borrows-regions.md`
- `docs/spec/mir/nll-constraints.md`
- `docs/spec/mir/typing.md`
- `docs/macro_system.md`
- `docs/parallel_streams_macro_pre_codegen.md`
- `docs/parallel_streams_red_team_2026-02-04.md`
- `docs/report_eval_boundary.md`
- `docs/production.md`

## Release Bar Checklist

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| A1 | Kernel rechecks every definition and top-level expression | **PASS** | `cli/src/driver.rs` `process_code` re-checks definition types/values via `kernel::checker::infer/check` before `Env::add_definition`; expressions are rechecked in `Declaration::Expr`. |
| A2 | No production path can bypass kernel checks | **PASS** | `kernel/src/checker.rs` `Env::add_definition` validates core invariants, types, ownership, effects, termination; `definitions` is private (only exposed by getters). |
| A3 | Prelude macro boundary explicit + enforced (deny + allowlist) | **PASS** | `cli/src/main.rs` + `cli/src/compiler.rs` set `MacroBoundaryPolicy::Deny` for prelude; `cli/src/lib.rs` `set_prelude_macro_boundary_allowlist` (empty allowlist). |
| B4 | Prop elimination restriction enforced | **PASS** | `kernel/src/checker.rs` `check_elimination_restriction` + `is_prop_like` (opaque-aware); `frontend/src/elaborator.rs` calls restriction before recursor use. |
| B5 | Prop restriction tests not ignored | **PASS** | No `#[ignore]` in kernel/frontend/mir/cli tests; Prop/opaque-Prop tests in `kernel/tests/negative_tests.rs` and `kernel/tests/readme_promises_tests.rs`. |
| B6 | `eval`/Dyn blocked in types/defeq; no macro smuggling | **PASS** | `frontend/src/elaborator.rs` rejects `Eval` in type context; `kernel/src/checker.rs` `contains_partial_def` treats `eval` as unsafe; `kernel/src/nbe.rs` keeps `eval` opaque; `frontend/src/macro_expander.rs` flags `eval` as boundary form. |
| C7 | Total `def` forbids `fix` | **PASS** | `kernel/src/checker.rs` `check_effects` rejects `Fix` in Total/WellFounded; `contains_partial_def` treats `fix` as partial in types. |
| C8 | Partial terms cannot appear in types/defeq | **PASS** | `kernel/src/checker.rs` `ensure_type_safe` used in `infer/check` prevents partial defs in types. |
| C9 | Well-founded recursion checked if supported | **PASS** | `kernel/src/checker.rs` `Env::add_definition` enforces `check_wellfounded_termination` for `Totality::WellFounded`. |
| D10 | MIR lowering preserves ownership semantics (no Unit/Copy erasure bypass) | **PASS** | `mir/src/lower.rs` lowers unknown runtime types to `MirType::Opaque` and `compute_is_copy_for_mir` marks opaque non-Copy; `push_local` uses `is_prop_like` for erasure tagging. |
| D11 | NLL projection-aware and deref-aliasing aware | **PASS** | `mir/src/analysis/nll.rs` `resolve_place_at` expands deref chains; conflict checks consider projections and deref reborrows. |
| D12 | Copy semantics + Fn/FnOnce enforced, no Copy-by-fiat | **PASS** | `kernel/src/checker.rs` enforces minimum `FunctionKind`; `frontend/src/elaborator.rs` infers required kind; `mir/src/lower.rs` maps kind to borrow/move calls; `mir/src/types.rs` keeps closures non-Copy. |
| D13 | Statement-level MIR typing/invariant checks exist | **PASS** | `mir/src/analysis/typing.rs` TypingChecker; invoked for defs + closures in `cli/src/driver.rs` and compiler pipelines. |
| E14 | Macro-introduced identifiers don’t capture call-site binders | **PASS** | `frontend/src/macro_expander.rs` adds fresh scope to macro-introduced syntax while leaving arguments untouched; `frontend/src/desugar.rs` resolves by scope-compatibility. |
| E15 | Quasiquote/unquote respects hygiene | **PASS** | `frontend/src/macro_expander.rs` `expand_quasiquote_with_depth` preserves syntax objects and scopes; hygiene tests in `frontend/tests/macro_quasiquote_hygiene.rs`. |
| E16 | Macro expansion deterministic and tested | **PASS** | `frontend/tests/determinism_tests.rs`; macro env uses `BTreeMap`/`BTreeSet` for deterministic iteration. |
| F17 | Defeq respects `Ref` lifetime labels | **PENDING** | `kernel/tests/semantic_tests.rs` (label-sensitive defeq regression from Stream 1). |
| F18 | Lifetime labels preserved core → MIR | **PENDING** | `mir/tests/borrowck_corpus.rs` (label flow cases from Stream 2); `cli/tests/lifetime_labels.rs`. |
| F19 | Label laundering negative test exists | **PENDING** | `cli/tests/pipeline_negative.rs` (mismatched label coercion from Stream 1). |

## Blockers (Must Fix Before Stdlib Expansion)

- None found for the current release bar.

## High Severity Issues

- None found for the current release bar.

## Tests Status

Soundness tests present:
- Kernel: `kernel/tests/negative_tests.rs`, `kernel/tests/semantic_tests.rs`, `kernel/tests/readme_promises_tests.rs`, `kernel/tests/spec_alignment_tests.rs`
- Frontend: `frontend/tests/macro_expansion_tests.rs`, `frontend/tests/macro_quasiquote_hygiene.rs`, `frontend/tests/elaboration_tests.rs`, `frontend/tests/determinism_tests.rs`
- MIR: `mir/tests/borrowck_corpus.rs`, `mir/src/analysis/nll_tests.rs`, `mir/src/analysis/typing.rs` tests
- CLI: `cli/tests/pipeline_golden.rs`, `cli/tests/pipeline_negative.rs`, `cli/tests/typing_mir_calls.rs`, `cli/tests/lowering_borrow_regions.rs`

Missing tests:
- Regression asserting closures remain non-Copy even when their captures are Copy (MIR or CLI-level).

Ignored tests:
- None found (`#[ignore]` not present in kernel/frontend/mir/cli tests).

## Suggested GitHub Issues

1. **Add regression for closure non-Copy policy**  
   Severity: Medium  
   Subsystem: MIR / Ownership  
   Acceptance criteria (test-based): add a MIR or CLI test that attempts to copy a closure value (e.g., assign the same closure into two locals) and asserts a TypingChecker or Ownership error.

2. **Align ownership spec with NLL implementation**  
   Severity: Low  
   Subsystem: Docs / Spec alignment  
   Acceptance criteria (test-based): update `docs/spec/ownership_model.md` to describe NLL as the active borrow checker and add a spec-alignment test (e.g., in `kernel/tests/spec_alignment_tests.rs`) that asserts the doc references NLL rather than `borrow.rs`.
