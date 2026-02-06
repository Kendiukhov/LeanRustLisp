# Parallel Streams Plan (Red Team Round 19)

**Stream 1: Kernel Defeq + Lifetime Labels**
- Make definitional equality label-aware by comparing `SpineItem.label` in `kernel/src/nbe.rs::check_eq_spine`.
- Preserve labels in application-spine utilities (add a label-aware variant instead of `collect_app_spine` or extend it) so defeq does not erase them. Target: `kernel/src/checker.rs`.
- Add kernel unit tests for label-sensitive defeq in `kernel/tests/semantic_tests.rs`.
Dependencies: None.

**Stream 2: CLI/MIR Lifetime Label Tests**
- Add pipeline negative test that demonstrates label laundering is rejected (e.g., `Ref #[a]` coerced to `Ref #[b]`) in `cli/tests/pipeline_negative.rs`.
- Add labeled-lifetime stress tests across polymorphic calls and higher-order functions in `cli/tests/lifetime_labels.rs` and `mir/tests/borrowck_corpus.rs`.
Dependencies: Stream 1 for tests to pass cleanly.

**Stream 3: Capture-Mode Trust Boundary**
- Decide the enforcement location: either move capture-mode strength checking into the kernel or recompute required capture modes in MIR and ignore annotations for soundness.
- If kernel enforcement is chosen, extend `kernel/src/checker.rs::validate_capture_modes` to check strength, not just existence.
- If MIR-only enforcement is chosen, delete/ignore capture annotations in the kernel boundary and recompute in `mir/src/lower.rs` with clear diagnostics.
Dependencies: None, but this is a design decision that should be made before implementation.

**Stream 4: Interior Mutability Runtime Checks**
- Implement `runtime_refcell_borrow_check` and `runtime_mutex_lock` in `mir/src/codegen.rs`, or explicitly reject these types unless `unsafe`.
- Add MIR/codegen tests verifying runtime checks are emitted for `RefCell`/`Mutex` usage in `mir/tests/borrowck_corpus.rs` and `cli/tests/pipeline_golden.rs`.
Dependencies: None.

**Stream 5: Macro Hygiene Scope Compatibility**
- Replace strict scope equality with a documented compatibility rule (e.g., subset compatibility) in `frontend/src/desugar.rs` and `frontend/src/macro_expander.rs`.
- Add nested macro hygiene regression tests for scope compatibility in `frontend/tests/macro_expansion_tests.rs` and `frontend/tests/hygiene_resolution.rs`.
Dependencies: None.

**Stream 6: Documentation Updates (Low Risk, Can Run Anytime)**
- Document that lifetime labels are part of the type boundary and must be preserved by defeq (update `README.md` and `docs/production.md`).
- Clarify the safe subset around interior mutability (runtime checks required; otherwise `unsafe`/`noncomputable`) in `README.md` and `docs/production.md`.
- If capture-mode enforcement stays outside the kernel, document the TCB implication in `docs/spec/kernel_boundary.md` and `docs/production.md`.
Dependencies: None.
