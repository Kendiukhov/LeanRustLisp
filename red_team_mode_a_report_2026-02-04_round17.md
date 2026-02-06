# Red Team Mode A Report (2026-02-04 Round 17)

**Executive Summary**
- Macro-boundary smuggling via `quasiquote` appears fixed: boundary scanning now inspects fully expanded output and the test suite explicitly covers quasiquote smuggling under both Warn/Deny policies. Evidence: `frontend/src/macro_expander.rs` (`record_macro_boundary_warning`, `collect_macro_boundary_hits`, `expand_macros_internal`) and `frontend/tests/macro_expansion_tests.rs` (`test_macro_expansion_quasiquote_smuggling_*`).
- The new noncomputable gate for axiom dependencies is enforced in the kernel, but it currently treats core borrow primitives (`borrow_shared`, `borrow_mut`, `Ref`, `Shared`, `Mut`) as axioms, which forces otherwise-safe programs to be marked `noncomputable` or `unsafe`. This contradicts the README’s “Rust‑grade resource discipline in safe code” and “noncomputable only for axiom-dependent defs” promise. Evidence: `kernel/src/checker.rs` (`Env::add_definition`, `AxiomDependencyRequiresNoncomputable`), `kernel/src/ast.rs` (`RESERVED_PRIMITIVE_NAMES`), `stdlib/prelude.lrl` (axiom declarations), `frontend/src/desugar.rs` (`&`/`&mut` desugar to borrow primitives), `README.md` (Safety Boundaries / Axioms and Noncomputable).
- Interior mutability runtime checks are stubbed: `RefCell`/`Mutex` markers are recognized and runtime checks are inserted, but the codegen implementations are TODO no-ops. This violates the “may panic on borrow violation” semantics and leaves safe code without the promised dynamic enforcement. Evidence: `mir/src/analysis/nll.rs` (runtime checks collection), `mir/src/types.rs` (`IMKind::RefCell` comment), `mir/src/codegen.rs` (`runtime_refcell_borrow_check`, `runtime_mutex_lock`), `stdlib/prelude.lrl` (`interior_mutable`/`may_panic_on_borrow_violation`).
- Definitional equality fuel bounds and `opaque` escape hatch are still enforced with explicit tests for exponential unfolding and fuel exhaustion; no new defeq/perf bypass found. Evidence: `kernel/tests/semantic_tests.rs` (`test_defeq_fuel_limits_unfolding`, `test_boom_eq_exponential_unfolding_is_bounded`).
- The borrow checker remains a bespoke component outside the kernel; with primitives now treated as axioms, the TCB boundary for “safe” code is effectively larger than the README suggests. Evidence: `mir/src/analysis/nll.rs` (custom NLL implementation), `kernel/src/checker.rs` (axiom gating is kernel-enforced, but borrow correctness is not).

**Stop-The-Line (Blockers)**
- Safe borrowing requires `noncomputable`/`unsafe` because borrow primitives are axioms, collapsing the “safe total fragment” into the axiom-dependent fragment. This makes stdlib expansion on safe code effectively impossible without loosening the new gate. Evidence: `kernel/src/checker.rs` (axiom dependency gate), `stdlib/prelude.lrl`, `frontend/src/desugar.rs`, `README.md`.
- Interior mutability runtime checks are unimplemented (no-ops). `RefCell`/`Mutex` are admitted in safe code but do not actually enforce borrow/lock rules. Evidence: `mir/src/codegen.rs` (`runtime_refcell_borrow_check`, `runtime_mutex_lock`), `mir/src/analysis/nll.rs`, `mir/src/types.rs`.

---

**Contract Violations**
1. **Safe borrowing is forced into the axiom-dependent fragment.**
The kernel now rejects any definition that depends on axioms unless it is marked `noncomputable` or `unsafe`. Because `borrow_shared`, `borrow_mut`, `Ref`, `Shared`, and `Mut` are reserved primitives implemented as axioms, ordinary safe borrowing is now blocked unless you opt into noncomputable/unsafe. This contradicts the README’s promise that safe code gets Rust-grade resource discipline and that `noncomputable` is reserved for axiom-dependent code. Evidence: `kernel/src/checker.rs` (`Env::add_definition`, `AxiomDependencyRequiresNoncomputable`), `kernel/src/ast.rs` (`RESERVED_PRIMITIVE_NAMES`), `stdlib/prelude.lrl` (axiom declarations), `frontend/src/desugar.rs` (`&`/`&mut` desugaring), `README.md` (Safety Boundaries; Axioms and Noncomputable).

2. **Interior mutability is declared “may panic” but runtime checks are no-ops.**
`RefCell` is marked as `interior_mutable`/`may_panic_on_borrow_violation` and the MIR pipeline inserts `RuntimeCheckKind::RefCellBorrow`, but `runtime_refcell_borrow_check` and `runtime_mutex_lock` are TODO stubs. That violates the documented runtime behavior for interior mutability. Evidence: `stdlib/prelude.lrl` (markers), `mir/src/analysis/nll.rs` (runtime check insertion), `mir/src/types.rs` (`IMKind::RefCell` comment), `mir/src/codegen.rs` (stubbed runtime checks).

3. **“Syntax as data” is not realized for `quote`.**
`quote` desugars into a `List` of `Nat` character codes, not a `Syntax` object with spans/scopes, and there is no runtime `Syntax` type. This contradicts the README’s “syntax as data / Lisp-grade extensibility” promise at the term level. Evidence: `frontend/src/desugar.rs` (`quote` and `quote_syntax`), `frontend/src/surface.rs` (Syntax exists only at compile time), `README.md` (Core Goals: Lisp-grade extensibility).

---

**Soundness / TCB Risks**
- **Kernel now treats all axioms equally, including runtime primitives.** This pulls borrow primitives into the axiom-dependent fragment and expands the TCB beyond what the README implies for “safe” code. Evidence: `kernel/src/checker.rs` (axiom dependency gate), `kernel/src/ast.rs` (reserved primitives).
- **Borrow correctness lives outside the kernel.** The kernel only enforces effect boundaries and ownership; borrow safety is enforced by custom MIR NLL logic. This is acceptable only if NLL is thoroughly stress‑tested and fuzzed. Evidence: `kernel/src/checker.rs` (ownership/effect checks), `mir/src/analysis/nll.rs` (borrow checker implementation).
- **Interior mutability relies on runtime checks that are currently unimplemented.** This makes any “safe” reliance on `RefCell`/`Mutex` semantics unsound. Evidence: `mir/src/codegen.rs` (TODO checks), `mir/src/analysis/nll.rs` (inserts checks).

---

**Semantic Gaps (Severity)**
- **Blocker:** Borrow primitives are axioms, so safe defs that use `&`/`&mut` are rejected unless `noncomputable`/`unsafe`. This collapses the safe fragment into the axiom fragment. Evidence: `kernel/src/checker.rs`, `kernel/src/ast.rs`, `stdlib/prelude.lrl`, `frontend/src/desugar.rs`.
- **High:** `RefCell`/`Mutex` runtime checks are stubs, so “may panic on borrow violation” is not enforced. Evidence: `mir/src/codegen.rs`, `mir/src/types.rs`, `mir/src/analysis/nll.rs`.
- **Medium:** `quote` produces `List Nat` rather than a syntax object with scopes/spans, so “syntax as data” is not implemented at runtime. Evidence: `frontend/src/desugar.rs`, `frontend/src/surface.rs`.

---

**Minimal Reproducible Examples**

1. **Safe borrowing now requires `noncomputable`/`unsafe`.**
Expected: accepted as a total safe definition. Actual: kernel rejects due to axiom dependency (`borrow_shared` is an axiom). Evidence: `kernel/src/checker.rs` (`AxiomDependencyRequiresNoncomputable`), `frontend/src/desugar.rs`, `stdlib/prelude.lrl`.
```lrl
(def id_ref (pi x Nat (Ref Shared Nat))
  (lam x Nat (& x)))
```

2. **Interior mutability checks are no-ops.**
Expected: `RefCell` use sites trigger runtime borrow checks that can panic on violation. Actual: checks are inserted but compile to no-ops (`runtime_refcell_borrow_check` is TODO). Evidence: `mir/src/analysis/nll.rs`, `mir/src/codegen.rs`.
```lrl
(def use_refcell (pi x (RefCell Nat) Nat)
  (lam x (RefCell Nat)
    (let a (RefCell Nat) x
      (let b (RefCell Nat) x
        zero))))
```

3. **`quote` does not produce syntax objects.**
Expected: a syntax object (datum + span + scopes) as “syntax as data.” Actual: `quote` lowers to `List` of `Nat` character codes. Evidence: `frontend/src/desugar.rs` (`quote_syntax`).
```lrl
(quote foo)
```

---

**Fix Plan (Prioritized)**
1. **Introduce a distinct “primitive” classification** for reserved runtime ops (`Ref`, `Shared`, `Mut`, `borrow_shared`, `borrow_mut`, `index_*`). Where: `kernel/src/ast.rs`, `kernel/src/checker.rs`. Why: avoid treating runtime primitives as logical axioms. Tests: new kernel tests that a total `def` using `&` typechecks without `noncomputable`.
2. **Exclude primitives from axiom dependency gating** (or treat them as trusted builtins). Where: `kernel/src/checker.rs` (`collect_axioms_rec`, `AxiomDependencyRequiresNoncomputable`). Why: keep safe borrowing in the total fragment. Tests: `def` with `&` and `&mut` accepted; axioms still require `noncomputable`.
3. **Distinguish logical axioms vs runtime primitives in diagnostics**. Where: `cli/src/driver.rs`, `cli/src/compiler.rs`. Why: avoid confusing “axiom dependency” warnings for core primitives. Tests: diagnostics report “primitive dependency” vs “axiom dependency.”
4. **Update prelude definitions** to mark primitives explicitly (new tag or builtin flag). Where: `stdlib/prelude.lrl`, `kernel/src/ast.rs`. Why: ensure kernel can identify primitives without name‑based hacks. Tests: prelude loads without `noncomputable` pollution.
5. **Implement `runtime_refcell_borrow_check` and `runtime_mutex_lock`** or ban `RefCell`/`Mutex` in safe mode until implemented. Where: `mir/src/codegen.rs` and runtime representation. Why: enforce interior mutability semantics. Tests: MIR/codegen runtime test that double‑borrow panics.
6. **Add MIR/codegen tests for interior mutability enforcement**. Where: `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_*`. Why: ensure runtime checks fire and fail. Tests: a program that triggers a `RefCell` borrow violation.
7. **Document interior mutability semantics and panic‑free profile**. Where: `README.md`, `docs/production.md`. Why: align with “may panic on borrow violation.” Tests: doc tests or README promise tests.
8. **Define a runtime `Syntax` type or restrict `quote` to compile‑time**. Where: `frontend/src/desugar.rs`, `kernel` or `stdlib`. Why: satisfy “syntax as data” promise or explicitly scope it to macros. Tests: `quote` returns a `Syntax` object; macros can inspect it.
9. **Add a readme‑promise test for `quote` semantics**. Where: `kernel/tests/readme_promises_tests.rs` or `frontend/tests`. Why: prevent regressions in syntax‑as‑data behavior.
10. **Expand adversarial NLL test coverage** (CFG joins, early returns, reborrows, escape through calls). Where: `mir/tests/borrowck_corpus.rs`. Why: reduce TCB risk. Tests: new negative corpus cases.
11. **Add a “safe borrow” integration test** that does not require `noncomputable`. Where: `cli/tests/pipeline_golden.rs`. Why: enforce contract that safe borrowing is in the total fragment.
12. **Clarify the trusted boundary in docs** (kernel vs MIR borrow checker). Where: `README.md`, `docs/production.md`. Why: make the soundness story explicit while primitives are still outside kernel.

---

**Go/No-Go Checklist for Stdlib Expansion**
- [ ] Safe borrowing (`&`, `&mut`) works in total defs without `noncomputable`/`unsafe`.
- [ ] Logical axioms are distinguished from runtime primitives in the kernel and diagnostics.
- [ ] `RefCell`/`Mutex` runtime checks are implemented (or these types are forbidden in safe mode until they are).
- [ ] Macro boundary checks remain enforced after full expansion (including `quasiquote`).
- [ ] Defeq fuel/`opaque` behavior remains bounded with tests for exponential unfolding.
- [ ] NLL borrow checker has adversarial CFG coverage beyond unit tests.
- [ ] `quote` semantics for syntax-as-data are defined and tested (or explicitly scoped to macro‑time only).

---

**Suggested GitHub Issues**
- “Borrow primitives treated as axioms force safe code to be noncomputable/unsafe” [labels: bug, soundness]
- “Implement RefCell/Mutex runtime checks (currently TODO stubs)” [labels: bug, soundness]
- “Define runtime Syntax representation or scope `quote` to macro‑time” [labels: design, docs]
- “Add safe-borrow integration test without noncomputable” [labels: test]
- “Expand NLL adversarial CFG/reborrow test corpus” [labels: test]
