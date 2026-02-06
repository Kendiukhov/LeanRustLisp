# Red Team Mode A Report (2026-02-04 Round 18)

**Executive Summary**
- Macro-boundary smuggling via `quasiquote` looks fixed and is now covered by explicit tests under both Warn/Deny policies. Evidence: `frontend/src/macro_expander.rs` (`record_macro_boundary_warning`, `collect_macro_boundary_hits`, `expand_macros_internal`) and `frontend/tests/macro_expansion_tests.rs` (`test_macro_expansion_quasiquote_smuggling_*`).
- Documentation now explicitly scopes “syntax as data” to compile-time macros, so the prior runtime-syntax mismatch is no longer a contract violation. Evidence: `README.md` and `docs/production.md` updates.
- **Blocker:** Safe borrowing is forced into the axiom-dependent fragment. Because borrow primitives are axioms, any def using `&`/`&mut` trips the kernel’s axiom-dependency gate unless marked `noncomputable`/`unsafe`. This undercuts the README’s “Rust-grade resource discipline in safe code.” Evidence: `stdlib/prelude.lrl` (borrow primitives are axioms), `frontend/src/desugar.rs` (`&`/`&mut` desugaring), `kernel/src/checker.rs` (`Env::add_definition`, `AxiomDependencyRequiresNoncomputable`).
- Interior mutability enforcement remains stubbed: MIR inserts runtime checks for `RefCell`/`Mutex`, but codegen’s runtime hooks are TODO no-ops. This makes “may panic on borrow violation” semantics unenforced. Evidence: `mir/src/analysis/nll.rs` (runtime check insertion), `mir/src/codegen.rs` (`runtime_refcell_borrow_check`, `runtime_mutex_lock`), `mir/src/types.rs` (`IMKind::RefCell` comment).
- Definitional equality still has fuel bounds and explicit tests for exponential unfolding. No new defeq/opaque bypass found. Evidence: `kernel/src/nbe.rs`, `kernel/tests/semantic_tests.rs`.

**Stop-The-Line (Blockers)**
- Safe borrowing requires `noncomputable`/`unsafe` because `borrow_shared`/`borrow_mut` are axioms and the kernel forbids axiom-dependent total defs unless explicitly opted in. This collapses the “safe total fragment” for any code that uses `&`/`&mut`. Evidence: `stdlib/prelude.lrl`, `frontend/src/desugar.rs`, `kernel/src/checker.rs`.
- `RefCell`/`Mutex` runtime checks are inserted but compile to no-ops, so dynamic borrow/lock safety is not enforced. If these types are exposed as safe in stdlib, this violates intended semantics. Evidence: `mir/src/analysis/nll.rs`, `mir/src/codegen.rs`.

---

**Contract Violations**
1) **Safe borrowing is effectively noncomputable/unsafe.**
The README promises Rust-grade resource discipline in safe code, but the kernel’s axiom-dependency gate treats borrow primitives as axioms, forcing any definition that uses `&`/`&mut` to be marked `noncomputable` or `unsafe`. This breaks the “safe fragment” story for everyday borrowing. Evidence: `stdlib/prelude.lrl` (axiom `borrow_shared`, `borrow_mut`, `Ref`, `Shared`, `Mut`), `frontend/src/desugar.rs` (borrows desugar to these primitives), `kernel/src/checker.rs` (`Env::add_definition` → `AxiomDependencyRequiresNoncomputable`).

2) **Interior mutability “may panic on borrow violation” is not enforced at runtime.**
The system claims RefCell-like types may panic on borrow violations, but the runtime check hooks are TODO stubs. If these types are considered safe, this is a mismatch between promised semantics and actual behavior. Evidence: `mir/src/analysis/nll.rs` (generates `RuntimeCheckKind::RefCellBorrow`/`MutexLock`), `mir/src/codegen.rs` (no-op `runtime_refcell_borrow_check`, `runtime_mutex_lock`), `mir/src/types.rs` (RefCell semantics comment).

---

**Soundness / TCB Risks**
- **Borrow primitives treated as axioms expand the trusted base.** The kernel gate makes “safe borrowing” depend on axiom opt-in, effectively pushing core resource safety into the axiom-dependent fragment. Evidence: `kernel/src/checker.rs`, `stdlib/prelude.lrl`.
- **Borrow checker remains outside the kernel.** NLL correctness is not proved by the kernel; it’s a large TCB surface. Evidence: `mir/src/analysis/nll.rs`.
- **Interior mutability enforcement is missing.** Runtime checks are inserted but unenforced, which can silently violate intended safety semantics. Evidence: `mir/src/analysis/nll.rs`, `mir/src/codegen.rs`.
- **Classical axiom tracking is opt-in.** Without `--require-axiom-tags`, untagged axioms are not classified as classical, allowing “classical laundering” by omission. This is policy, but it’s a risk unless enforced in production mode. Evidence: `cli/src/main.rs` (`--require-axiom-tags`), `kernel/src/checker.rs` (`axiom_dependencies_with_tag`).

---

**Semantic Gaps (Severity)**
- **Blocker:** Safe borrowing requires `noncomputable`/`unsafe`. This undermines the safe fragment and makes most Rust-like code “axiom-dependent.” Evidence: `stdlib/prelude.lrl`, `frontend/src/desugar.rs`, `kernel/src/checker.rs`.
- **High:** RefCell/Mutex runtime checks are stubbed; safety semantics are not enforced. Evidence: `mir/src/codegen.rs`, `mir/src/analysis/nll.rs`.
- **Medium:** Classical-axiom tagging is optional; untagged axioms can bypass classical tracking unless `--require-axiom-tags` is used. Evidence: `cli/src/main.rs`, `kernel/src/checker.rs`.

---

**Minimal Reproducible Examples**

1) **Safe borrowing rejected unless `noncomputable`/`unsafe`**
Expected: accepted as a total safe definition. Actual: kernel rejects due to axiom dependency (`borrow_shared` is an axiom). Evidence: `kernel/src/checker.rs` (`AxiomDependencyRequiresNoncomputable`), `frontend/src/desugar.rs`.
```lrl
(def id_ref (pi x Nat (Ref Shared Nat))
  (lam x Nat (& x)))
```

2) **Interior mutability runtime checks are no-ops**
MIR inserts `RuntimeCheckKind::RefCellBorrow` on use sites, but codegen emits `runtime_refcell_borrow_check` which is an empty stub. Evidence: `mir/src/analysis/nll.rs`, `mir/src/codegen.rs`.
```lrl
(def use_refcell (pi x (RefCell Nat) Nat)
  (lam x (RefCell Nat) zero))
```

3) **Classical tagging can be bypassed if tags are omitted**
This is policy-dependent (allowed unless `--require-axiom-tags`), but it means classical dependencies can be hidden. Evidence: `cli/src/main.rs`, `kernel/src/checker.rs`.
```lrl
(axiom choice (sort 0))
(noncomputable uses_choice (sort 0) choice)
```

---

**Fix Plan (Prioritized)**
1) **Introduce a distinct “primitive” classification** for reserved runtime ops (`Ref`, `Shared`, `Mut`, `borrow_shared`, `borrow_mut`, `index_*`) so they do not count as logical axioms. Where: `kernel/src/ast.rs`, `kernel/src/checker.rs`. Why: keep safe borrowing in the total fragment. Tests: total `def` using `&` typechecks without `noncomputable`.
2) **Exclude primitives from axiom dependency gating** (or record a separate “primitive dependency” set). Where: `kernel/src/checker.rs` (`collect_axioms_rec`, `AxiomDependencyRequiresNoncomputable`). Why: avoid labeling core runtime ops as axioms. Tests: borrow-heavy defs compile without `noncomputable`.
3) **Clarify diagnostics for primitives vs axioms**. Where: `cli/src/driver.rs`, `cli/src/compiler.rs`. Why: reduce confusion and prevent “axiom dependency” warnings for core primitives. Tests: diagnostics distinguish “primitive dependency” vs “axiom dependency.”
4) **Add an explicit marker/tag for primitives** in the prelude. Where: `stdlib/prelude.lrl`, `kernel/src/ast.rs`. Why: avoid name-based special cases and make the TCB explicit.
5) **Implement `runtime_refcell_borrow_check` and `runtime_mutex_lock`** or forbid `RefCell`/`Mutex` in safe mode until implemented. Where: `mir/src/codegen.rs` and runtime value representation. Why: enforce “may panic on borrow violation.” Tests: dynamic borrow violation triggers panic.
6) **Add MIR/codegen tests for runtime checks**. Where: `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_*`. Why: ensure runtime checks are emitted and executed. Tests: check codegen output includes runtime checks.
7) **Document the primitive/axiom boundary** in README/production. Where: `README.md`, `docs/production.md`. Why: make the safety story explicit and avoid future regressions.
8) **Make `--require-axiom-tags` mandatory in “production mode.”** Where: `cli/src/main.rs`, `docs/production.md`. Why: prevent classical/unsafe laundering via untagged axioms.
9) **Expand adversarial NLL coverage** (CFG joins, reborrow chains, escape through calls). Where: `mir/tests/borrowck_corpus.rs`. Why: reduce TCB risk for borrow checker.
10) **Add a “safe borrow” integration test** without `noncomputable`. Where: `cli/tests/pipeline_golden.rs`. Why: enforce the intended safe borrowing contract.

---

**Go/No-Go Checklist for Stdlib Expansion**
- [ ] Safe borrowing (`&`, `&mut`) works in total defs without `noncomputable`/`unsafe`.
- [ ] Borrow primitives are not counted as logical axioms in dependency tracking.
- [ ] RefCell/Mutex runtime checks are implemented or these types are forbidden in safe mode.
- [ ] Macro boundary checks remain enforced after full expansion (including `quasiquote`).
- [ ] Defeq fuel and `opaque` behavior remain bounded with regression tests.
- [ ] NLL borrow checker has adversarial CFG/reborrow tests beyond unit cases.
- [ ] Classical axiom tagging is enforced in production mode (or at least documented as mandatory).

---

**Suggested GitHub Issues**
- “Borrow primitives treated as axioms force safe code to be noncomputable/unsafe” [labels: bug, soundness]
- “Implement RefCell/Mutex runtime checks (currently TODO stubs)” [labels: bug, soundness]
- “Distinguish primitive dependencies from logical axioms in diagnostics” [labels: design, docs]
- “Make `--require-axiom-tags` mandatory in production profile” [labels: design, soundness]
- “Expand NLL CFG/reborrow stress tests” [labels: test]
