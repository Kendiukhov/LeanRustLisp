# LRL Release-Bar Audit Report (Pre-Codegen Semantic Soundness) — Run 3

**Date:** February 3, 2026  
**Role:** LRL Release-Bar Auditor (Semantic Soundness Only, Pre-Codegen)  
**Scope:** kernel + frontend/elaboration/macro boundary + MIR lowering + NLL borrow checking + CLI/driver pipeline

## Executive Verdict

**NO-GO for stdlib expansion**

- Kernel re-check is enforced for both definitions and top-level expressions in the driver.
- Macro boundary for prelude is explicit and enforced (deny + allowlist).
- Prop elimination restrictions are enforced in the kernel and elaborator; regression tests exist.
- Totality boundary (fix/partial/well-founded) is enforced in kernel and guarded in driver.
- MIR includes statement-level typing checks and NLL is projection/deref aware.
- **Blocker:** MIR lowering erases some runtime types to `Unit`, which can mask ownership/borrow semantics on projections.

## Docs Reviewed (Current Specs)

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
| A1 | Kernel rechecks every definition and top-level expression | **PASS** | `cli/src/driver.rs` `Declaration::Expr` calls `kernel::checker::check` in empty `Context`. |
| A2 | No production path can bypass kernel checks | **PASS** | `kernel/src/checker.rs` keeps `Env.definitions` private; production code uses `Env::add_definition`. |
| A3 | Prelude macro boundary explicit + enforced (deny + allowlist) | **PASS** | `cli/src/compiler.rs` sets `MacroBoundaryPolicy::Deny` for prelude; `cli/src/lib.rs` allowlist exists (empty). |
| B4 | Prop elimination restriction enforced | **PASS** | `kernel/src/checker.rs` `check_elimination_restriction` called for `Term::Rec`; elaborator uses it for match. |
| B5 | Prop restriction tests not ignored | **PASS** | No `#[ignore]` found in tests; coverage in kernel/frontend suites. |
| B6 | `eval`/Dyn blocked in types/defeq; no macro smuggling | **PASS** | `frontend/src/elaborator.rs` rejects `Eval` in type context; `kernel/src/checker.rs` `contains_partial_def` rejects `eval` in types. |
| C7 | Total `def` forbids `fix` | **PASS** | `cli/src/driver.rs` rejects `fix` in non-partial defs; `kernel/src/checker.rs` `check_effects` rejects `Fix` in Total/WellFounded. |
| C8 | Partial terms cannot appear in types/defeq | **PASS** | `kernel/src/checker.rs` `add_definition` calls `contains_partial_def` on `def.ty`. |
| C9 | Well-founded recursion checked if supported | **PASS** | `kernel/src/checker.rs` validates `Totality::WellFounded` via `check_wellfounded_termination`. |
| D10 | MIR lowering preserves ownership semantics (no Unit erasure bypass) | **FAIL** | `mir/src/lower.rs` `lower_type_general`/`lower_type_template` fall back to `MirType::Unit` for non-`Ind` applications and `Term::Var`. |
| D11 | NLL projection-aware and deref-aliasing aware | **PASS** | `mir/src/analysis/nll.rs` resolves `Deref/Field/Index`; corpus tests in `mir/tests/borrowck_corpus.rs`. |
| D12 | Copy semantics + Fn/FnOnce enforced, no Copy-by-fiat | **PASS** | Kernel enforces explicit Copy via unsafe; MIR call operand uses `FunctionKind`; typing test in `cli/tests/typing_mir_calls.rs`. |
| D13 | Statement-level MIR typing/invariant checks exist | **PASS** | `mir/src/analysis/typing.rs` run for bodies/closures in `cli/src/driver.rs`. |
| E14 | Macro-introduced identifiers don’t capture call-site binders | **PASS** | `frontend/src/macro_expander.rs` adds fresh scopes; `frontend/src/desugar.rs` resolves by scope compatibility. |
| E15 | Quasiquote/unquote respects hygiene | **PASS** | `frontend/src/macro_expander.rs` quasiquote expansion preserves scopes; unquote inserts syntax objects. |
| E16 | Macro expansion deterministic and tested | **PASS** | Determinism/hygiene snapshots in `frontend/tests/macro_expansion_tests.rs`. |

## Blockers (Must Fix Before Stdlib Expansion)

1. **MIR type erasure to `Unit` can mask ownership/borrow semantics (D10)**
   Evidence: `mir/src/lower.rs` `lower_type_general` and `lower_type_template` return `MirType::Unit` for `Term::Var` and non-`Ind` applications (“Generic application or dependent type -> Unit/Erased”). `MirType::Unit` is Copy, and projection copy checks use `MirType::is_copy`, risking silent duplication of non-Copy fields.
   Minimal repro (MIR):
   ```text
   LocalDecl { ty: Adt(Box, [Unit]) }  // A generic Box<A> with A erased to Unit
   // Copy the payload field:
   Assign(_1, Use(Copy(Place { local: box_local, projection: [Field(0)] })))
   // Ownership checker treats field type as Unit (Copy) -> no error.
   ```
   Suggested test: a MIR-level regression that constructs an ADT with a `Param` field instantiated to a non-Copy type, then attempts to `Copy` the field projection and expects an ownership error (or a typing error if the type is not preserved).

## High Severity Issues

No additional high-severity issues beyond the blocker above.

## Tests Status

Soundness tests present:
- Kernel: `kernel/tests/semantic_tests.rs`, `kernel/tests/negative_tests.rs`, `kernel/tests/readme_promises_tests.rs`
- Frontend: `frontend/tests/macro_expansion_tests.rs`, `frontend/tests/elaboration_tests.rs`
- MIR: `mir/src/analysis/nll_tests.rs`, `mir/tests/borrowck_corpus.rs`, `mir/src/lints.rs`
- CLI: `cli/tests/golden_suite.rs`, `cli/tests/pipeline_golden.rs`, `cli/tests/pipeline_negative.rs`, `cli/tests/typing_mir_calls.rs`

Missing tests:
- Explicit regression that prevents MIR type erasure from allowing `Copy` on non-Copy projections (D10).
- Optional guard test that top-level expressions are kernel rechecked (A1), even though the code currently does so.

Ignored tests:
- None found (`#[ignore]` not present in test files searched).

## Suggested GitHub Issues

1. **[Blocker] Prevent MIR `Unit` erasure from bypassing ownership**
   Severity: Blocker  
   Subsystem: MIR Lowering / Ownership  
   Acceptance criteria: add a MIR test that attempts to copy a field whose type is abstract/non-Copy (erased to `Unit` today) and ensure ownership/typing rejects it; update lowering to preserve enough type structure (or error) so the test passes.

2. **[Medium] Add regression for kernel re-check on expressions**
   Severity: Medium  
   Subsystem: CLI/Driver  
   Acceptance criteria: add a pipeline test where a top-level expression fails kernel check but passes elaboration; ensure a kernel error is reported.
