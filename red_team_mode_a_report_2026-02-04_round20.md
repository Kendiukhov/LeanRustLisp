# Red Team Mode A Report (2026-02-04 Round 20)

**Executive Summary**
- **Fixed:** Definitional equality now compares application labels, closing the lifetime-label laundering hole; a new negative pipeline test covers the mismatch case. Evidence: `kernel/src/nbe.rs::check_eq_spine`, `cli/tests/pipeline_negative.rs::pipeline_negative_lifetime_label_mismatch_defeq`.
- Macro hygiene remains equality-based on scopes, and macro expansion still adds macro scope to user-supplied arguments; nested macro capture risks persist despite new tests. Evidence: `frontend/src/desugar.rs::scopes_compatible`, `frontend/src/macro_expander.rs::substitute_rec_with_scope`, `frontend/tests/macro_expansion_tests.rs::test_nested_macro_hygiene_outer_inner`.
- Interior mutability runtime checks (`RefCell`/`Mutex`) are still TODO stubs in codegen; safety is only enforced by marking such types unsafe/noncomputable. Evidence: `mir/src/codegen.rs::runtime_refcell_borrow_check`, `kernel/src/checker.rs::add_inductive` marker axioms.
- Capture-mode strength is validated in MIR lowering, not in the kernel; kernel only checks that annotations reference free variables. Evidence: `kernel/src/checker.rs::validate_capture_modes`, `mir/src/lower.rs::collect_captures`.
- New “README promises” and “spec alignment” tests improve contract coverage, but do not shrink the trusted boundary. Evidence: `kernel/tests/readme_promises_tests.rs`, `kernel/tests/spec_alignment_tests.rs`.

---

**Contract Violations**
1) **Hygienic macros are still not guaranteed.**
The contract promises hygienic macros, but scope compatibility is exact-equality and macro substitution adds macro scope to *all* nodes, including user arguments, which can cause capture or misresolution in nested expansions. Evidence: `frontend/src/desugar.rs::scopes_compatible`, `frontend/src/macro_expander.rs::substitute_rec_with_scope`.

---

**Soundness / TCB Risks**
- **Borrow/lifetime safety still depends on MIR (outside kernel).** The kernel now enforces label equality, but the borrow checker and region inference still live in MIR, which remains trusted. Evidence: `mir/src/analysis/nll.rs`, `mir/src/lower.rs` (region assigner).
- **Capture-mode correctness is not kernel-enforced.** Kernel only validates annotation existence; MIR enforces strength. This is a cross-boundary trust gap. Evidence: `kernel/src/checker.rs::validate_capture_modes`, `mir/src/lower.rs::collect_captures`.
- **Interior mutability runtime checks are stubbed.** The kernel blocks safe use via unsafe markers, but runtime semantics are still unimplemented. Evidence: `mir/src/codegen.rs::runtime_refcell_borrow_check`, `mir/src/codegen.rs::runtime_mutex_lock`.

---

**Semantic Gaps (Severity)**
- **High:** Macro hygiene resolution uses strict scope equality; nested macro expansion can still capture or misresolve identifiers. Evidence: `frontend/src/desugar.rs`, `frontend/src/macro_expander.rs`.
- **High:** Interior mutability runtime checks are no-ops; safety depends on policy not enforcement. Evidence: `mir/src/codegen.rs`.
- **Medium:** Lifetime label *elision* is not normalized into explicit labels in the kernel; explicit-vs-elided labels are now definitional-inequal, which can reject code that should be accepted under an “elision is sugar” model. Evidence: `frontend/src/elaborator.rs::attach_ref_label` (only for explicit labels), `kernel/src/nbe.rs::check_eq_spine` (label equality).
- **Medium:** Capture-mode enforcement is outside the kernel; the kernel accepts ill-annotated closures if MIR is bypassed. Evidence: `kernel/src/checker.rs::validate_capture_modes`, `mir/src/lower.rs::collect_captures`.

---

**Minimal Reproducible Examples**

1) **Nested macro capture risk (hygiene gap)**
Expected: inner `x` should bind to the `x` introduced by `outer`. Actual: scope-equality hygiene can resolve it to a global `x`.
```lrl
(defmacro inner () x)
(defmacro outer (e) (quasiquote (let x Nat 0 (unquote e))))
(outer (inner))
```
Evidence: `frontend/src/macro_expander.rs::substitute_rec_with_scope`, `frontend/src/desugar.rs::scopes_compatible`.

2) **Elided vs explicit lifetime mismatch (likely regression)**
Expected: elided lifetime should behave like an inferred label and unify with explicit label. Actual: defeq compares labels and may reject.
```lrl
(noncomputable id_ref (pi r (Ref Shared Nat) (Ref Shared Nat))
  (lam r (Ref Shared Nat) r))

(noncomputable use_explicit (pi r (Ref #[a] Shared Nat) (Ref #[a] Shared Nat))
  (lam r (Ref #[a] Shared Nat) (id_ref r)))
```
Evidence: `frontend/src/elaborator.rs::attach_ref_label`, `kernel/src/nbe.rs::check_eq_spine`.

3) **Interior mutability runtime checks are no-ops**
Expected: dynamic borrow or lock checks at runtime. Actual: codegen emits empty stubs.
```lrl
(noncomputable use_refcell
  (pi x (RefCell Nat) Nat)
  (lam x (RefCell Nat) zero))
```
Evidence: `mir/src/codegen.rs::runtime_refcell_borrow_check`, `mir/src/analysis/nll.rs` (runtime check insertion).

---

**Fix Plan (Prioritized)**
1) Normalize elided lifetime labels into explicit labels during elaboration when inference is unambiguous. Where: `frontend/src/elaborator.rs` (`validate_ref_lifetime_elision_for_pi`, `attach_ref_label`). Why: keep defeq stable while preserving elision ergonomics. Tests: add positive case where explicit label matches elided.
2) Add a defeq unit test for elided-vs-explicit label compatibility (if intended). Where: `kernel/tests/semantic_tests.rs`. Why: lock in label elision semantics.
3) Document the new label-equality rule and elision behavior. Where: `README.md`, `docs/spec/mir/borrows-regions.md`, `docs/production.md`. Why: prevent surprises.
4) Replace scope-equality with a compatibility rule (subset/longest-match). Where: `frontend/src/desugar.rs`, `frontend/src/macro_expander.rs`. Why: true hygienic behavior in nested macros. Tests: `frontend/tests/macro_expansion_tests.rs` (outer/inner case).
5) Add a targeted hygiene regression test for the `outer/inner` example. Where: `frontend/tests/macro_expansion_tests.rs` + snapshot. Why: enforce correctness.
6) Implement runtime checks for `RefCell`/`Mutex` or reject them in safe mode with explicit diagnostics. Where: `mir/src/codegen.rs`, `cli/src/driver.rs`. Why: align runtime semantics with policy. Tests: MIR/codegen outputs include runtime checks.
7) Ensure MIR runtime checks are emitted for interior mutability in codegen outputs. Where: `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_golden.rs`. Why: regression protection.
8) Move capture-mode strength enforcement into the kernel or recompute capture modes in MIR and ignore annotations. Where: `kernel/src/checker.rs`, `mir/src/lower.rs`. Why: shrink TCB. Tests: closure annotated weaker than required must be rejected.
9) Add a kernel test that invalid capture modes are rejected (not just unknown). Where: `kernel/tests/negative_tests.rs`. Why: enforce kernel boundary.
10) Update macro-system spec to match hygiene implementation semantics after fix. Where: `docs/spec/macro_system.md`. Why: contract clarity.

---

**Go/No-Go Checklist for Stdlib Expansion**
- [ ] Elided lifetime labels normalize to explicit labels (or docs explicitly state incompatibility).
- [ ] Macro hygiene uses a compatibility rule (not exact equality) and passes nested macro regression tests.
- [ ] Interior mutability runtime checks are implemented or safe usage is explicitly forbidden with diagnostics.
- [ ] Capture-mode enforcement is kernel-tight or annotations are not trusted.
- [ ] Borrow/lifetime tests cover explicit vs elided labels and higher-order calls.

---

**Suggested GitHub Issues**
- “Normalize elided Ref lifetimes to explicit labels (defeq now label-aware)” [labels: design, soundness]
- “Macro hygiene uses strict scope equality; nested macros can capture” [labels: bug, soundness]
- “Implement runtime checks for RefCell/Mutex or forbid safe use” [labels: bug, soundness]
- “Capture-mode strength is enforced only in MIR” [labels: design, soundness]
