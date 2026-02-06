# Red Team Mode A Report (2026-02-04 Round 19)

**Executive Summary**
- Borrow primitives are now classified as runtime primitives rather than logical axioms, so safe borrowing no longer forces `noncomputable`. Evidence: `kernel/src/ast.rs` (`DefinitionKind::Primitive`, `primitive_deps`), `kernel/src/checker.rs` (`Env::add_definition`), `cli/src/driver.rs` (`report_axiom_dependencies`).
- Definitional equality is fuel-bounded with caching and actionable diagnostics; this closes the previous defeq DoS cliff but still leaves usability pressure on `opaque` and fuel tuning. Evidence: `kernel/src/nbe.rs` (`DefEqConfig`, fuel policy), `kernel/src/checker.rs` (`map_nbe_defeq_error`), `cli/src/driver.rs` (`defeq_fuel_diagnostic`).
- Macro boundary enforcement is now explicit and tested (including quasiquote smuggling). Evidence: `frontend/src/macro_expander.rs` (`record_macro_boundary_warning`, `collect_macro_boundary_hits`), `frontend/tests/macro_expansion_tests.rs`.
- **Blocker:** lifetime labels on `Ref` are erased by kernel defeq, enabling lifetime laundering across typed boundaries. Evidence: `kernel/src/ast.rs` (`Term::App` label), `kernel/src/checker.rs` (`collect_app_spine`), `kernel/src/nbe.rs` (`check_eq_spine`), `mir/src/lower.rs` (`parse_ref_type`, `RegionParamAssigner`).
- Capture-mode safety is enforced in MIR lowering, not the kernel; the trusted boundary still includes borrow/lifetime semantics outside the kernel. Evidence: `kernel/src/checker.rs` (`validate_capture_modes`), `mir/src/lower.rs` (`collect_captures`).
- Interior mutability runtime checks are still stubbed in codegen, but now explicitly gated as unsafe/axiom-dependent via markers; this is a policy gap rather than a silent safety hole. Evidence: `kernel/src/checker.rs` (`add_inductive` marker axioms), `mir/src/codegen.rs` (`runtime_refcell_borrow_check`, `runtime_mutex_lock`), `stdlib/prelude.lrl` (marker usage + comments).

**Stop-The-Line (Blockers)**
- **Lifetime label erasure in defeq** allows `Ref #[a]` to be coerced to `Ref #[b]` by definitional equality, undermining the borrow checker’s region tying and violating Rust-grade safety claims. Evidence: `kernel/src/nbe.rs` (`check_eq_spine` ignores labels), `kernel/src/checker.rs` (`collect_app_spine` drops labels), `mir/src/lower.rs` (labels drive region params).

---

**Contract Violations**
1) **“Rust-grade resource discipline” is not enforceable with lifetime labels erased by defeq.**
The README promises Rust-grade ownership/borrowing, but the kernel treats labeled and unlabeled `Ref` applications as definitionally equal. This allows a well-typed function to accept `Ref #[a]` and return `Ref #[b]`, effectively widening a lifetime. Evidence: `kernel/src/ast.rs` (`Term::App` label), `kernel/src/checker.rs` (`collect_app_spine` uses `Term::App(_,_,_)` and ignores labels), `kernel/src/nbe.rs` (`check_eq_spine` only compares args, not `SpineItem.label`), `mir/src/lower.rs` (`parse_ref_type` and `RegionParamAssigner` tie labels to regions).

---

**Soundness / TCB Risks**
- **Kernel defeq ignores lifetime labels while MIR relies on them.** This crosses the kernel/MIR boundary and can invalidate NLL assumptions. Evidence: `kernel/src/nbe.rs` (`check_eq_spine`), `mir/src/lower.rs` (`parse_ref_type`).
- **Capture-mode correctness lives outside the kernel.** The kernel only validates that capture annotations reference existing free variables; MIR lowering enforces strength. If MIR is bypassed or buggy, kernel admits invalid capture modes. Evidence: `kernel/src/checker.rs` (`validate_capture_modes`), `mir/src/lower.rs` (`collect_captures`).
- **Interior mutability runtime enforcement is TODO.** The kernel now forces `RefCell`/`Mutex` usage into `noncomputable`/`unsafe`, but runtime checks remain no-ops; this is acceptable only if treated as explicitly unsafe. Evidence: `kernel/src/checker.rs` (`add_inductive` marker axioms), `mir/src/codegen.rs` (`runtime_refcell_borrow_check`, `runtime_mutex_lock`).
- **Macro hygiene is still equality-based for scopes.** Scope compatibility is exact-match only, which can misresolve identifiers in nested macro expansions and complicates hygiene guarantees. Evidence: `frontend/src/desugar.rs` (`scopes_compatible`), `frontend/src/macro_expander.rs` (`scopes_compatible`).

---

**Semantic Gaps (Severity)**
- **Blocker:** Lifetime labels are not part of definitional equality. This allows label laundering and breaks the borrow checker’s lifetime model. Evidence: `kernel/src/nbe.rs`, `kernel/src/checker.rs`, `mir/src/lower.rs`.
- **High:** Runtime checks for `RefCell`/`Mutex` are stubs. If these types are ever exposed as safe (or if `noncomputable` is treated as safe execution), the runtime semantics are wrong. Evidence: `mir/src/codegen.rs`.
- **Medium:** Macro hygiene uses strict scope equality with no subset compatibility, which can break nested macro intent and may cause unresolved or misresolved names. Evidence: `frontend/src/desugar.rs`, `frontend/src/macro_expander.rs`.
- **Medium:** Capture-mode validation is not in the kernel, enlarging the TCB and risking mismatches between kernel-accepted code and MIR enforcement. Evidence: `kernel/src/checker.rs`, `mir/src/lower.rs`.

---

**Minimal Reproducible Examples**

1) **Lifetime label laundering (should be rejected, likely accepted)**
Expected: rejected because return lifetime label differs from input. Actual: kernel defeq ignores labels, so types unify.
```lrl
(noncomputable coerce
  (pi a (Ref #[a] Shared Nat)
    (Ref #[b] Shared Nat))
  (lam a (Ref #[a] Shared Nat) a))
```
Evidence: `kernel/src/nbe.rs::check_eq_spine`, `kernel/src/checker.rs::collect_app_spine`, `mir/src/lower.rs::parse_ref_type`.

2) **Nested macro scope misresolution (hygiene edge case)**
Expected: inner macro’s `x` should resolve to the `x` introduced by `outer`. With exact scope equality, it resolves to a global `x` instead.
```lrl
(defmacro inner () x)
(defmacro outer (e) `(let x Nat ,e))
(outer (inner))
```
Evidence: `frontend/src/desugar.rs::scopes_compatible` (exact equality), `frontend/src/macro_expander.rs::substitute_rec_with_scope` (macro scope injection).

3) **Runtime checks for interior mutability are no-ops**
Expected: dynamic borrow or lock checks at runtime. Actual: codegen emits stubs.
```lrl
(noncomputable use_refcell
  (pi x (RefCell Nat) Nat)
  (lam x (RefCell Nat) zero))
```
Evidence: `mir/src/analysis/nll.rs` (inserts `RuntimeCheckKind::RefCellBorrow`), `mir/src/codegen.rs` (`runtime_refcell_borrow_check`).

---

**Fix Plan (Prioritized)**
1) What: Make definitional equality label-aware for `Ref` applications; compare `SpineItem.label` and reject mismatches. Where: `kernel/src/nbe.rs` (`check_eq_spine`, `SpineItem`), `kernel/src/checker.rs` (`collect_app_spine` or introduce label-aware variant). Why: Prevent lifetime laundering. Tests: new kernel defeq test + CLI negative test for mismatched labels.
2) What: Preserve labels when collecting application spines used by defeq; do not drop `Term::App` labels. Where: `kernel/src/checker.rs`. Why: label equality must be preserved end-to-end. Tests: defeq on `Ref #[a]` vs `Ref #[b]` must fail.
3) What: Add a pipeline negative test for label mismatch coercion. Where: `cli/tests/pipeline_negative.rs` + snapshot. Why: protect against regressions. Tests: `coerce` example above must error.
4) What: Add a kernel unit test for label-sensitive equality. Where: `kernel/tests/semantic_tests.rs`. Why: ensure core defeq respects labels independent of CLI. Tests: defeq fails when labels differ.
5) What: Enforce capture-mode strength in kernel or remove capture annotations from the kernel boundary and recompute in MIR. Where: `kernel/src/checker.rs` (`validate_capture_modes`), `mir/src/lower.rs`. Why: shrink TCB and avoid kernel/MIR mismatch. Tests: a closure that requires `FnOnce` must be rejected if annotated as weaker.
6) What: Emit runtime checks for `RefCell`/`Mutex` or explicitly reject these types unless `unsafe`. Where: `mir/src/codegen.rs`, `stdlib/prelude.lrl`. Why: align runtime semantics with marker policy. Tests: runtime check emitted or explicit compile-time error.
7) What: Add MIR/codegen tests asserting runtime check emission. Where: `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_golden.rs`. Why: prevent silent regressions. Tests: confirm `Statement::RuntimeCheck` survives to codegen output.
8) What: Define and document the safe subset regarding interior mutability and noncomputable execution. Where: `README.md`, `docs/production.md`. Why: avoid ambiguous “safe but may panic” promises. Tests: documentation-only.
9) What: Implement scope compatibility as subset (or an explicit hygiene policy) rather than equality. Where: `frontend/src/desugar.rs`, `frontend/src/macro_expander.rs`. Why: make nested macros resolve deterministically and hygienically. Tests: add nested macro resolution cases.
10) What: Add a nested macro hygiene regression test for the `outer/inner` example. Where: `frontend/tests/macro_expansion_tests.rs`. Why: lock in intended hygiene semantics. Tests: new snapshot.
11) What: Add lifetime label stress tests for polymorphic calls and higher-order functions. Where: `cli/tests/lifetime_labels.rs`, `mir/tests/borrowck_corpus.rs`. Why: ensure labels survive elaboration → kernel → MIR correctly. Tests: negative and positive cases.
12) What: Tighten diagnostics when label mismatches occur (clear actionable message). Where: `cli/src/driver.rs`. Why: make failures understandable for users. Tests: snapshot message includes label details.

---

**Go/No-Go Checklist for Stdlib Expansion**
- [ ] Definitional equality respects `Ref` lifetime labels; label mismatch is rejected.
- [ ] Lifetime label laundering is covered by negative tests in CLI + kernel.
- [ ] Capture-mode enforcement is either in-kernel or recomputed solely in MIR with no trust in annotations.
- [ ] Interior mutability runtime checks are implemented or types are explicitly gated to `unsafe` with clear diagnostics.
- [ ] Nested macro hygiene resolution has deterministic, documented behavior with tests.
- [ ] NLL borrow checker has regression coverage for labeled lifetimes and higher-order call flows.

---

**Suggested GitHub Issues**
- “Defeq ignores Ref lifetime labels, enabling lifetime laundering” [labels: bug, soundness]
- “Make capture-mode validation kernel-tight or remove trust in capture annotations” [labels: design, soundness]
- “Implement RefCell/Mutex runtime checks or forbid safe use” [labels: bug, soundness]
- “Define scope compatibility for hygienic macros (subset vs equality) and add tests” [labels: design, test]
- “Add labeled-lifetime negative tests at kernel + CLI layers” [labels: test]
