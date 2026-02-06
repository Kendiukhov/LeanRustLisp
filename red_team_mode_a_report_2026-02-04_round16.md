# Red Team Mode A Report (2026-02-04 Round 16)

**Executive Summary**
- Macro boundary enforcement is bypassable: a macro can emit `quote`/`quasiquote` that later expands into `axiom`, `unsafe`, or `import classical` without triggering the boundary check. This directly contradicts the README’s “macros cannot introduce unsafe/classical forms unless allowlisted” contract.
- The macro boundary allowlist is name-based and macros are freely re-definable; if allowlisting is ever used, a user can shadow an allowlisted macro name and bypass boundary enforcement.
- **Policy choice**: adopt **Option A (Noncomputable gate)**. Any definition that depends on axioms is marked noncomputable (or lives in a Comp{Axiom} effect), and codegen/run is rejected unless explicitly opted in. The current `panic!("Axiom accessed: ...")` stub becomes a backstop, not the primary policy.
- Borrow checking is enforced in the pipeline, but NLL’s custom conflict logic is still bespoke; there is no evidence of stress tests for tricky CFGs or reborrow/escape scenarios beyond unit tests. This is a high-risk area for latent soundness bugs.
- The kernel boundaries are largely in place (termination, effect checks, Prop elimination), but key enforcement (macro boundary; axiom computation policy) is outside the kernel and thus part of the TCB.

**Stop-The-Line (Blockers)**
- Macro boundary bypass via `quasiquote` allows macros to smuggle `axiom`, `unsafe`, and `import classical` despite `Deny` policy. This is a direct contract violation.
- Axioms used in runtime code compile to `panic!` stubs without any explicit `unsafe`/`noncomputable` gate, allowing “safe” code to panic.

**Safe-To-Proceed Checklist (Current Status)**
- Macro boundary enforcement can’t be bypassed by staging (`quote`/`quasiquote`). **Not met**.
- Axiom/classical usage policy is explicit (reject, mark noncomputable, or require `unsafe`). **Not met**.
- NLL borrow checker has adversarial CFG tests and fuzz coverage for reborrows/escapes. **Not met**.

---

**Contract Violations**
1) **Macro boundary policy is bypassable via `quasiquote`**
- README promises macro boundary `Deny` prevents macros from introducing unsafe/classical forms unless allowlisted (`README.md:32-35`).
- The boundary scanner explicitly stops at `quote`/`quasiquote`, and boundary checks happen before `quasiquote` expansion.
- Evidence:
  - `frontend/src/macro_expander.rs:453-473` (`collect_macro_boundary_hits` returns early on `quote`/`quasiquote`).
  - `frontend/src/macro_expander.rs:929-952` (`expand_macros_internal` expands `quasiquote` after boundary check).
  - `frontend/src/macro_expander.rs:1019-1046` (`record_macro_boundary_warning` invoked on raw macro expansion output before deeper expansion).

2) **Allowlisted macro names can be shadowed (porous boundary)**
- The allowlist is checked only by macro name and macros are re-definable without restriction.
- This allows user code to redefine an allowlisted prelude macro and evade boundary checks if/when allowlisting is used.
- Evidence:
  - `frontend/src/macro_expander.rs:388-393` (`add_macro` overwrites by name; no origin check).
  - `frontend/src/macro_expander.rs:414-420` (allowlist check is name-only in `record_macro_boundary_warning`).

3) **Well-typed programs can panic on axiom access**
- Axioms are type-safe by default (Totality::Axiom), and total definitions can call them.
- Codegen emits a panic stub for axioms; thus, using axioms in executable code triggers runtime panics without explicit `unsafe`/`noncomputable` acknowledgment.
- Evidence:
  - `cli/src/compiler.rs:267-272` (axioms emit `panic!("Axiom accessed: ...")`).

---

**Soundness / TCB Risks**
- **Macro boundary enforcement lives outside the kernel** and is bypassable with staging; this expands the TCB to include macro expansion semantics and allows unsound constructs to slip in despite policy. (`frontend/src/macro_expander.rs:453-473`, `:929-952`, `:1019-1046`)
- **Allowlist shadowing risk**: name-only allowlist plus free macro redefinition means any future allowlisted macro becomes a potential privilege escalation. (`frontend/src/macro_expander.rs:388-393`, `:414-420`)
- **Axiom evaluation policy is undefined**: axioms are callable in total definitions and compile to panics. This needs explicit policy and enforcement to avoid “safe” code crashing. (`cli/src/compiler.rs:267-272`)
- **Borrow checking trust boundary**: NLL is bespoke and not obviously validated against adversarial CFGs. There are tests, but no evidence of systematic attack coverage for tricky control-flow or reborrow escape patterns. (Risk area: `mir/src/analysis/nll.rs`)

---

**Semantic Gaps (Severity)**
- **High**: **Noncomputable gate (Option A) is chosen but not implemented**. Axiom-dependent defs still compile to runtime `panic!` without explicit opt-in. (`cli/src/compiler.rs:267-272`)
- **High**: Macro boundary enforcement ignores post-`quasiquote` expansion results, allowing boundary violations to be introduced by macros. (`frontend/src/macro_expander.rs:453-473`, `:929-952`, `:1019-1046`)
- **Medium**: Macro allowlist is name-based; no sealing of origin/module. If allowlisting is ever used, a user can shadow allowlisted names. (`frontend/src/macro_expander.rs:388-393`, `:414-420`)
- **Medium**: Borrow checker coverage is mostly unit-level; no stress testing for CFG-induced aliasing/reborrow edge cases. (Add tests in `mir/src/analysis/nll_tests.rs`)

---

**Minimal Reproducible Examples**

1) **Macro boundary bypass via `quasiquote` (classical axiom)**
```lrl
(defmacro smuggle-classical ()
  (quasiquote (axiom classical bad (sort 0))))

(smuggle-classical)
```
Expected: macro boundary error under `Deny`. Actual: no boundary hit, classical axiom introduced.

2) **Macro boundary bypass via `quasiquote` (import classical)**
```lrl
(defmacro smuggle-import ()
  (quasiquote (import classical)))

(smuggle-import)
```
Expected: macro boundary error under `Deny`. Actual: classical axiom gets imported.

3) **Axiom causes runtime panic in executable code**
```lrl
(axiom foo Nat)
(def f Nat foo)
```
Compiles, but runtime will `panic!("Axiom accessed: foo")` when `f` is evaluated.

---

**Fix Plan (Prioritized)**
1. **Apply macro boundary checks after full expansion**, not just after single macro substitution. Update `expand_macros_internal` to re-run boundary scanning on the fully expanded syntax tree.
2. **Remove the `quote`/`quasiquote` early return in boundary scanning**, or explicitly expand `quasiquote` before boundary evaluation so staged unsafe forms are caught.
3. **Add boundary tests** for `quasiquote` smuggling of `axiom`, `unsafe`, and `import classical` in `frontend/tests`.
4. **Bind allowlist entries to module/origin**, not just macro name. Track macro provenance and reject shadowing in non-prelude modules.
5. **Emit diagnostics if an allowlisted macro name is redefined** outside the prelude (even if allowlist is empty today).
6. **Implement Option A (Noncomputable gate)**: any def with axiom deps is marked noncomputable (or Comp{Axiom}).
7. **Enforce compile-time opt-in**: reject codegen/run for axiom-dependent defs unless explicitly opted in (e.g., `noncomputable` marker or `--allow-axioms`).
8. **Elevate classical/unsafe axiom deps to hard errors** in total definitions unless explicitly marked noncomputable/unsafe.
9. **Expand NLL adversarial tests**: add CFG cases with nested borrows, early returns, and reborrow chains to `mir/src/analysis/nll_tests.rs`.
10. **Add fuzz regression tests** for borrow checking and macro expansion edge cases, including macro-generated borrow patterns.
11. **Document axiom execution policy** in `README.md` and `docs/production.md` (compile-time error vs. runtime panic vs. noncomputable).
12. **Add a CI gate** that fails on any macro-boundary violation in the prelude, including staged (`quasiquote`) expansions.

---

**Go/No-Go Checklist for Stdlib Expansion**
- [ ] Macro boundary enforcement covers staged expansions (`quote`/`quasiquote`).
- [ ] Allowlist is origin-bound and cannot be shadowed by user macros.
- [ ] Axiom usage policy is explicit and enforced (Option A: noncomputable gate with explicit opt-in).
- [ ] Axiom/classical dependencies are surfaced as errors (or explicitly opted in) for executable code.
- [ ] NLL borrow checker has adversarial CFG tests beyond unit examples.
- [ ] CI prevents prelude macro boundary regressions.

---

**Suggested GitHub Issues**
- "Macro boundary bypass via quasiquote" [labels: bug, soundness]
- "Macro allowlist can be shadowed by user macros" [labels: design, soundness]
- "Axioms compile to panic in safe code; define noncomputable/unsafe policy" [labels: design, docs]
- "Expand NLL CFG/reborrow stress tests" [labels: test]
- "Enforce axiom dependencies as errors for total defs (unless opted in)" [labels: soundness]
