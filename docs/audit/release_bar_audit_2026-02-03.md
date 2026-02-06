# LRL Release-Bar Audit Report (Pre-Codegen Semantic Soundness)

**Date:** February 3, 2026  
**Role:** LRL Release-Bar Auditor (Semantic Soundness Only, Pre-Codegen)  
**Scope:** kernel + frontend/elaboration/macro boundary + MIR lowering + NLL borrow checking + CLI/driver pipeline

## Executive Verdict

**NO-GO for stdlib expansion**

- Top-level expressions are accepted without a kernel re-check, violating the TCB boundary.
- MIR lowering erases some runtime types to `Unit`, which can mask borrow/ownership semantics in projections.
- Kernel boundary for definitions is solid, but the expression path still trusts elaboration only.
- Prop-elimination restrictions appear correctly enforced in the kernel and elaborator, with regression tests present.
- Totality boundaries (fix/partial/well-founded) are enforced in the kernel and guarded in the driver.
- Macro boundary for the prelude is explicit and enforced (deny + empty allowlist).
- MIR has a statement-level typing checker and NLL is projection/deref aware, but type erasure undermines the guarantee.

## Docs Reviewed (Recent Updates)

- `docs/spec/core_calculus.md`
- `docs/spec/function_kinds.md`
- `docs/spec/kernel_boundary.md`
- `docs/spec/macro_system.md`
- `docs/macro_system.md`
- `docs/mode_a_test_summary.md`
- `docs/test_plan_mode_a.md`
- `docs/kernel_readme_promise_hardcore_test_plan.md`

## Release Bar Checklist

| ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| A1 | Kernel rechecks every definition and top-level expression | **FAIL** | `cli/src/driver.rs` `Declaration::Expr` elaborates/infer only; no `kernel::checker::check` call. |
| A2 | No production path can bypass kernel checks | **PASS** | `kernel/src/checker.rs` `Env` fields are private; production code uses `Env::add_definition`. |
| A3 | Prelude macro boundary explicit + enforced (deny + allowlist) | **PASS** | `cli/src/compiler.rs` prelude path forces `MacroBoundaryPolicy::Deny`; `cli/src/lib.rs` allowlist empty. |
| B4 | Prop elimination restriction enforced | **PASS** | `kernel/src/checker.rs` `check_elimination_restriction` called in `infer` for `Term::Rec`; elaborator calls it for matches. |
| B5 | Prop restriction tests not ignored | **PASS** | No `#[ignore]` in tests; coverage in `kernel/tests/semantic_tests.rs` and `kernel/tests/negative_tests.rs`. |
| B6 | `eval`/Dyn blocked in types/defeq and not smuggled via macros | **PASS** | `frontend/src/elaborator.rs` rejects `Eval` in type context; `kernel/src/checker.rs` `contains_partial_def` rejects `eval` in types. |
| C7 | Total `def` forbids `fix` | **PASS** | `cli/src/driver.rs` rejects `fix` in non-partial defs; `kernel/src/checker.rs` `check_effects` rejects `Fix` in Total/WellFounded. |
| C8 | Partial terms cannot appear in types/defeq | **PASS** | `kernel/src/checker.rs` `add_definition` calls `contains_partial_def` on `def.ty`. |
| C9 | Well-founded recursion checked if supported | **PASS** | `kernel/src/checker.rs` `add_definition` validates `Totality::WellFounded` via `check_wellfounded_termination`. |
| D10 | MIR lowering preserves ownership semantics (no Unit erasure bypass) | **FAIL** | `mir/src/lower.rs` maps non-`Ind` applications to `MirType::Unit` (“Generic application or dependent type -> Unit/Erased”). |
| D11 | NLL projection-aware and deref-aliasing aware | **PASS** | `mir/src/analysis/nll.rs` resolves `PlaceElem::Deref/Field/Index`; tests in `mir/tests/borrowck_corpus.rs`. |
| D12 | Copy semantics + Fn/FnOnce enforced, no Copy-by-fiat | **PASS** | Kernel requires `unsafe` for explicit Copy; MIR call operand uses `FunctionKind`; typing tests in `cli/tests/typing_mir_calls.rs`. |
| D13 | Statement-level MIR typing/invariant checks exist | **PASS** | `mir/src/analysis/typing.rs` invoked in driver for bodies and closures. |
| E14 | Macro-introduced identifiers don’t capture call-site binders | **PASS** | `frontend/src/macro_expander.rs` adds fresh scope to introduced syntax; `frontend/src/desugar.rs` resolves only compatible scopes. |
| E15 | Quasiquote/unquote respects hygiene | **PASS** | Quasiquote expansion preserves scopes; unquote inserts argument syntax unchanged. |
| E16 | Macro expansion deterministic and tested | **PASS** | Determinism/hygiene snapshots in `frontend/tests/macro_expansion_tests.rs`. |

## Blockers (Must Fix Before Stdlib Expansion)

1. **Kernel boundary gap for top-level expressions (A1)**
   Evidence: `cli/src/driver.rs` `Declaration::Expr` elaborates + validates invariants but never calls `kernel::checker::check`.
   Minimal repro (policy gap): any file with a top-level expression (e.g. `(id)` after a definition) is accepted without kernel recheck.
   Suggested test: CLI pipeline test that injects an expression failing kernel check but passing elaboration, and asserts a kernel error is surfaced.

2. **MIR type erasure to `Unit` can mask ownership/borrow semantics (D10)**
   Evidence: `mir/src/lower.rs` `lower_type_general` returns `MirType::Unit` for non-`Ind` applications; `lower_type_template` also defaults to `Unit`.
   Minimal repro (MIR): a body where a field type is `MirType::Unit` but originates from a non-Copy type, enabling `Operand::Copy` on a field without ownership errors.
   Suggested test: MIR regression that builds an ADT with a `Param` field instantiated to a non-Copy type and asserts that copying a field is rejected.

## High Severity Issues

No additional high-severity issues beyond the blockers above.

## Tests Status

Soundness tests present:
- Kernel: `kernel/tests/semantic_tests.rs`, `kernel/tests/negative_tests.rs`, `kernel/tests/readme_promises_tests.rs`
- Frontend: `frontend/tests/macro_expansion_tests.rs`, `frontend/tests/elaboration_tests.rs`
- MIR: `mir/src/analysis/nll_tests.rs`, `mir/tests/borrowck_corpus.rs`, `mir/src/lints.rs` (panic-free profile)
- CLI: `cli/tests/golden_suite.rs`, `cli/tests/pipeline_golden.rs`, `cli/tests/pipeline_negative.rs`, `cli/tests/typing_mir_calls.rs`

Missing tests:
- Kernel recheck enforcement for top-level expressions (A1).
- MIR lowering: ensure type erasure cannot bypass borrow/ownership on projections (D10).

Ignored tests:
- None found (`#[ignore]` not present in test files searched).

## Suggested GitHub Issues

1. **[Blocker] Enforce kernel re-check for top-level expressions**
   Severity: Blocker  
   Subsystem: CLI/Driver  
   Acceptance criteria: add a pipeline test that feeds a top-level expression which elaborates but fails kernel checking, and ensure the driver reports a kernel error.

2. **[Blocker] Remove/contain MIR `Unit` erasure for non-structural types**
   Severity: Blocker  
   Subsystem: MIR Lowering / Borrow Checking  
   Acceptance criteria: add a MIR test that attempts to copy a field whose type is abstract/non-Copy and ensure ownership/typing rejects it; adjust lowering to preserve enough type structure (or error) so the test passes.
