# Parallel streams for red_team_mode_a_report.md

## Stream 1 - Frontend elaborator correctness and transparency
- P2: enforce match case body typing against the motive in `elaborate_match`.
- P3 (frontend side): compute recursor levels from the motive, pass explicit levels in `Term::Rec`, and call elimination restriction checks from elaboration.
- P6: use `Transparency::Reducible` (or user-selected transparency) for whnf/defeq/unify.
- Fix placeholder recursor typing (`build_recursor_type` / `build_minor_premise_type`) or block direct `rec` until fully typed.
- Tests: add new negative tests for `bad_match` and Prop-to-Type elimination (new files only).
- Files: `frontend/src/elaborator.rs`, `frontend/tests/*`, `tests/*` (new files).

## Stream 2 - Parser, CLI pipeline, and definition metadata
- P1: kernel re-check after elaboration in the CLI driver.
- P4: add `unsafe` surface syntax; propagate to `Definition::unsafe_def` through the pipeline.
- P5: add `opaque`/`transparent` surface attributes; store in `Definition::transparency`.
- P11: surface axiom dependency reporting (CLI command or warning) and required metadata plumbing.
- Tests: parser tests for `unsafe`/`opaque`; CLI tests for kernel re-check and axiom reporting.
- Files: `frontend/src/declaration_parser.rs`, `cli/src/driver.rs`, `kernel/src/ast.rs` (and any definition metadata storage).

## Stream 3 - Kernel checker: elimination and partial safety
- P3 (kernel side): use explicit recursor levels to enforce Prop-elimination restrictions in `kernel::checker`.
- Enforce partial/unsafe separation in kernel inference (reject partials in type positions).
- Tests: unignore `negative_large_elim_from_prop`; add a negative test for partial-in-type usage.
- Files: `kernel/src/checker.rs`, `kernel/tests/*` (new/updated tests).

## Stream 4 - Kernel NbE/defeq correctness and performance
- P7: fix `try_reduce_rec` to propagate real indices into IH arguments (no dummy indices).
- P8: preserve lambda domain types in `Value::Lam` and in `quote`/`whnf`.
- P12: add defeq fuel/memoization or detection of exponential unfolding.
- Tests: indexed inductive reduction tests; `whnf` binder-type preservation test; defeq performance regression (e.g., `boom_eq`).
- Files: `kernel/src/nbe.rs`, `kernel/tests/*` (new/updated tests).

## Stream 5 - MIR borrow checker and NLL aliasing
- P9: make `places_conflict` projection/deref-aware; treat `*r` as conflicting with loans on the referent.
- P10: implement projection-aware `place_type`; handle `Deref`/`Field`/reborrow in NLL.
- Tests: MIR-level aliasing tests (shared loan + deref write, field conflicts, reborrow).
- Files: `mir/src/analysis/borrow.rs`, `mir/src/analysis/nll.rs`, `mir/tests/*` (new tests).

## Stream 6 - Macro hygiene (quasiquote)
- Fix quasiquote expansion to attach macro scopes to generated identifiers (`cons`, `append`, `quote`, etc.).
- Tests: add a macro-hygiene regression (capture via quasiquote) as a new test file.
- Files: `frontend/src/macro_expander.rs`, `frontend/tests/*` (new tests).

## Coordination points (no file overlap)
- Stream 1 should consume `Definition::transparency` from Stream 2 once available.
- Stream 1 and Stream 3 both touch Prop-elimination, but in distinct layers (frontend vs kernel); agree on the API and level encoding.
