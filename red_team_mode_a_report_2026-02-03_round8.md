# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-03 Round 8

## Executive summary
- **Major fixes landed:** MIR now carries region parameters on `Fn`, call‑site instantiation is implemented, and call‑operand kind is validated (good). (`mir/src/types.rs` L570–582; `mir/src/analysis/nll.rs` L1016–1075; `mir/src/analysis/typing.rs` L69–111)
- **Capture‑mode precision is now enforced in lowering** (good): per‑capture modes/requirements are respected. (`mir/src/lower.rs` L463–555)
- **Primary remaining gap:** function lifetime parameters are inferred by *type‑based interning*, which collapses distinct lifetimes for the same inner type; this is not Rust‑grade and rejects valid programs. (`mir/src/lower.rs` L90–131, L322–331)
- **Definitional equality still uses fixed fuel and transparent unfolding by default**, so large/expanding terms can fail with `DefEqFuelExhausted` and break definitional equality. (`kernel/src/nbe.rs` L1003–1017; `kernel/src/checker.rs` L2989–3038; `kernel/src/ast.rs` L188–199)
- **Spec drift:** core calculus spec still documents only `Fn`/`FnOnce` while the implementation is `Fn`/`FnMut`/`FnOnce`. (`docs/spec/core_calculus.md` L15–20; `kernel/src/ast.rs` L457–463)
- **TCB boundary is still fuzzy:** prelude is compiled with macro‑boundary warnings (not errors), so it can introduce unsafe/classical forms without a hard gate. (`cli/src/compiler.rs` L119–134)
- **MIR typing is still narrow:** only call terminators are type‑checked; statement‑level typing is unchecked, leaving lowering bugs undetected. (`mir/src/analysis/typing.rs` L51–79)
- **No‑go for stdlib expansion** until lifetime modeling and defeq policy are clarified, and TCB/documentation gaps are closed.

## Stop‑the‑line list (prioritized)
1. **Lifetime expressiveness is insufficient for Rust‑grade guarantees.** Region params are keyed by inner type, collapsing distinct lifetimes. (`mir/src/lower.rs` L90–131, L322–331)
2. **Defeq fuel limits can reject valid programs.** Transparent unfolding with fixed fuel makes definitional equality brittle. (`kernel/src/nbe.rs` L1003–1017; `kernel/src/checker.rs` L2989–3038)
3. **TCB boundary is unclear for prelude/macros.** Prelude is compiled under macro‑boundary warnings, expanding the trusted surface without explicit policy. (`cli/src/compiler.rs` L119–134)

## Contract violations
1. **Core calculus spec out of sync with implementation.**
   - Spec claims only `Fn`/`FnOnce`. (`docs/spec/core_calculus.md` L15–20)
   - Implementation defines `Fn`/`FnMut`/`FnOnce` as core kinds. (`kernel/src/ast.rs` L457–463)
   - Impact: Lean‑grade spec is no longer aligned with the kernel.

2. **“Rust‑grade resource discipline” not fully met at the function boundary.**
   - Function lifetime parameters are inferred by *type‑based interning* of references, not by explicit or positional lifetime parameters. (`mir/src/lower.rs` L90–131, L322–331)
   - This collapses distinct lifetimes for the same inner type and rejects valid programs (see MRE #1).

## Soundness / TCB risks (with refactors)
- **Lifetime inference is a soundness boundary.**
  - TCB includes `RegionInterner` and the policy that ties region params to inner type. (`mir/src/lower.rs` L90–131, L322–331)
  - Refactor: introduce explicit lifetime parameters (surface + core) or at least position‑based lifetime parameters, then unify only when specified.

- **Prelude trust boundary is implicit.**
  - Prelude is compiled with `MacroBoundaryPolicy::Warn`, so unsafe/classical macro expansion is not blocked. (`cli/src/compiler.rs` L119–134)
  - Refactor: either mark prelude as explicitly trusted in docs/CLI output *or* compile it under `Deny` with an allowlist of forms.

- **MIR typing checker is partial.**
  - `TypingChecker::check` only visits call terminators; statement‑level typing (assignments, borrows, projections) is unchecked. (`mir/src/analysis/typing.rs` L51–79)
  - Refactor: add statement typing validation or an invariant checker to shrink the reliance on lowering correctness.

## Semantic gaps (severity)
- **[High] Lifetime expressiveness gap for same‑type references.**
  - Region params are interning by inner type, so independent lifetimes for `Ref Shared T` are unexpressible. (`mir/src/lower.rs` L90–131, L322–331)
- **[Medium] Defeq fuel‑exhaustion can reject valid programs.**
  - Default fuel is fixed (`100_000`) and used for all defeq; transparency defaults to `Reducible`. (`kernel/src/nbe.rs` L1003–1017; `kernel/src/checker.rs` L2989–3038; `kernel/src/ast.rs` L188–199)
- **[Low] Spec drift for function kinds.**
  - Core calculus spec is out of date relative to the kernel. (`docs/spec/core_calculus.md` L15–20; `kernel/src/ast.rs` L457–463)

## Minimal reproducible examples
1. **Over‑constrained lifetimes for same‑type refs (should be accepted, likely rejected).**
```lisp
(def choose_left (pi a (Ref Shared Nat) (pi b (Ref Shared Nat) (Ref Shared Nat)))
  (lam a (Ref Shared Nat)
    (lam b (Ref Shared Nat) a)))

(def use_choose (pi x Nat (Ref Shared Nat))
  (lam x Nat
    (let tmp Nat zero
      ;; Safe: result should be tied to x, not tmp.
      (choose_left (& x) (& tmp)))))
```
Because lifetimes are interned by inner type, the return lifetime is forced to the intersection of both args, rejecting a safe program.

2. **Defeq fuel exhaustion (scale `n` to exceed default fuel).**
```lisp
(def expand (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m) (add (expand m) (expand m))))))

;; Any defeq relying on full normalization of (expand n) can hit fuel limits
;; when n is large, causing DefEqFuelExhausted.
```
This is a semantic DoS: transparent unfolding + fixed fuel can reject valid terms.

## Fix plan (prioritized)
1. **Introduce explicit lifetime parameters (or position‑based lifetimes) in function types.**
   - **Where:** `frontend/src/desugar.rs`, `kernel/src/ast.rs`, `mir/src/types.rs`, `mir/src/lower.rs`.
   - **Why:** express independent lifetimes for same‑type refs; align with Rust‑grade borrowing.
   - **Tests:** new MIR/CLI tests for `choose_left`‑style signatures and mixed‑lifetime calls.

2. **Replace type‑based region interning with explicit/positional lifetime IDs.**
   - **Where:** `mir/src/lower.rs` (`RegionInterner`, `lower_type_in_fn`).
   - **Why:** avoid collapsing lifetimes across unrelated parameters.
   - **Tests:** borrowck corpus tests for distinct lifetimes of same inner type.

3. **Add lifetime‑param inference rules to elaborator.**
   - **Where:** `frontend/src/elaborator.rs`.
   - **Why:** infer region parameters from capture/return flow when annotations are omitted.
   - **Tests:** inference tests for functions returning one of multiple refs.

4. **Define a defeq policy for transparency + fuel.**
   - **Where:** `kernel/src/nbe.rs`, `kernel/src/checker.rs`, docs in `docs/spec/core_calculus.md`.
   - **Why:** avoid silent false negatives and unbounded compile time.
   - **Tests:** defeq stress tests that either succeed under policy or emit actionable diagnostics.

5. **Expose a user‑level knob for defeq policy.**
   - **Where:** CLI options + `kernel/src/nbe.rs`.
   - **Why:** predictable behavior for large proofs or definitional computation.
   - **Tests:** CLI tests verifying `LRL_DEFEQ_FUEL` and/or new flag behavior.

6. **Document prelude trust boundary explicitly.**
   - **Where:** `README.md`, `docs/spec/kernel_boundary.md`.
   - **Why:** prelude is effectively trusted (macro boundary warnings).
   - **Tests:** none; documentation update + maybe CLI warning.

7. **Optionally enforce `MacroBoundaryPolicy::Deny` for prelude with allowlist.**
   - **Where:** `cli/src/compiler.rs`.
   - **Why:** shrink TCB and keep unsafe/classical forms explicit.
   - **Tests:** prelude compile tests + macro boundary regression tests.

8. **Extend MIR typing checker to validate statements.**
   - **Where:** `mir/src/analysis/typing.rs` (new statement visitor).
   - **Why:** catch lowering bugs before borrowck/codegen.
   - **Tests:** MIR typing tests that intentionally generate bad assignments.

9. **Add negative tests for lifetime‑constrained returns.**
   - **Where:** `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_negative.rs`.
   - **Why:** ensure lifetimes are enforced when intentionally tied.

10. **Update core calculus spec to include FnMut.**
   - **Where:** `docs/spec/core_calculus.md`.
   - **Why:** align spec with implementation.
   - **Tests:** doc review only.

11. **Add “spec vs impl” CI guard (optional).**
   - **Where:** new doc test or lint in CI.
   - **Why:** prevent future spec drift.

12. **Add diagnostics for lifetime collapsing.**
   - **Where:** `mir/src/lower.rs` / `frontend/src/elaborator.rs`.
   - **Why:** explain when lifetimes are unified by type‑based interning until explicit params exist.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Explicit or positional lifetime parameters are implemented for `Fn` types.
- [ ] `choose_left`‑style example type‑checks (no false rejection from lifetime collapse).
- [ ] Defeq fuel policy documented; diagnostics are actionable.
- [ ] Prelude trust boundary is explicit (docs and/or enforced policy).
- [ ] MIR typing checker validates statements beyond call terminators.
- [ ] Core calculus spec updated for `FnMut`.

## Suggested GitHub issues (titles + labels)
- **“Function lifetime params are type‑interned; independent lifetimes for same type are impossible”** — labels: bug, soundness, mir
- **“Defeq uses fixed fuel + transparent unfolding; add policy/diagnostics”** — labels: design, soundness, kernel
- **“Prelude compiled under macro‑boundary warnings (TCB expansion)”** — labels: design, docs, frontend
- **“MIR typing checker only validates calls; add statement‑level typing”** — labels: bug, soundness, mir
- **“Update core_calculus spec for FnMut”** — labels: docs
