# Parallel Streams for Red Team Fix Plan (Round 16)

This plan groups the previously outlined tasks into independent streams. Dependencies are explicitly stated.

**Stream A: Macro Boundary Enforcement**
1. Apply macro boundary checks after full expansion in `frontend/src/macro_expander.rs`.
2. Remove the `quote`/`quasiquote` early return or explicitly expand `quasiquote` before boundary scanning in `frontend/src/macro_expander.rs`.
3. Add boundary tests for `quasiquote` smuggling of `axiom`, `unsafe`, and `import classical` in `frontend/tests`.
4. Bind allowlist entries to module/origin rather than macro name in `frontend/src/macro_expander.rs`.
5. Emit diagnostics if an allowlisted macro name is redefined outside the prelude.

Dependencies: None. This stream can run independently.

**Stream B: Axiom Usage Policy and Enforcement**
1. Implement **Option A (Noncomputable gate)**: any definition with axiom dependencies is marked noncomputable (or lives in a Comp{Axiom} effect).
2. Enforce compile-time opt-in: reject codegen/run for axiom-dependent defs unless explicitly opted in (e.g., `noncomputable` marker or `--allow-axioms`).
3. Elevate classical/unsafe axiom dependencies to hard errors in total definitions unless explicitly marked noncomputable/unsafe.

Dependencies: None. This stream can run independently.

**Stream C: Borrow Checker Stress Tests**
1. Expand NLL adversarial tests with CFG-induced aliasing, early returns, and reborrow chains in `mir/src/analysis/nll_tests.rs`.
2. Add fuzz or regression tests for borrow checking edge cases in `mir/src/analysis` test suite.

Dependencies: None. This stream can run independently.

**Stream D: Documentation and CI Gates**
1. Document **Option A (Noncomputable gate)** and opt-in requirements in `README.md` and `docs/production.md`.
2. Add CI gate to fail on any macro-boundary violation in the prelude, including staged (`quasiquote`) expansions.

Dependencies: Stream D depends on decisions from Stream A and Stream B so documentation and CI behavior reflect final policy.
