# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-03 Round 9

## Executive summary
- **Major improvement:** explicit lifetime labels + elision rules are now implemented in the elaborator and MIR lowering; function types carry region params derived from labels. (`frontend/src/elaborator.rs` L325–483; `mir/src/lower.rs` L69–386)
- **Macro boundary hardening landed:** prelude now compiles under `MacroBoundaryPolicy::Deny` with an allowlist (currently empty). (`cli/src/compiler.rs` L119–136; `cli/src/lib.rs` L8–12)
- **Call typing is enforced:** MIR typing now validates call operand kind and argument/return types. (`mir/src/analysis/typing.rs` L69–140)
- **Remaining blocker:** lifetime labels are *not structural*—they are stored in a side map keyed by term pointer. Any `shift`/`subst` rebuild drops labels, which can silently weaken lifetime constraints for higher‑order values. (`kernel/src/ast.rs` L614–688; `frontend/src/elaborator.rs` L512–548; `mir/src/lower.rs` L360–365, L425–428)
- **Definitional equality remains fuel‑limited with transparent unfolding by default**, so defeq can fail for valid programs (semantic DoS). (`kernel/src/nbe.rs` L1003–1017; `kernel/src/checker.rs` L2989–3038)
- **Spec drift persists:** core calculus spec still lists only `Fn`/`FnOnce` despite `FnMut` being in the kernel. (`docs/spec/core_calculus.md` L15–20; `kernel/src/ast.rs` L457–463)
- **MIR typing is still partial:** only call terminators are validated; statement‑level typing is unchecked. (`mir/src/analysis/typing.rs` L51–79)

## Contract violations
1. **Core calculus spec does not match the kernel.**
   - Spec says `Pi`/`Lam` carry only `Fn`/`FnOnce`. (`docs/spec/core_calculus.md` L15–20)
   - Kernel defines `Fn`, `FnMut`, `FnOnce`. (`kernel/src/ast.rs` L457–463)
   - This violates the “Lean‑grade specification” promise in README (spec/impl alignment).

2. **Rust‑grade resource discipline is undermined by non‑structural lifetime labels.**
   - Lifetime labels are stored externally (pointer‑keyed map), not in the term structure. (`kernel/src/ast.rs` L1–7; `frontend/src/elaborator.rs` L512–548)
   - Core operations `shift`/`subst` rebuild terms without carrying labels. (`kernel/src/ast.rs` L614–688)
   - Lowering relies on labels to tie regions. (`mir/src/lower.rs` L360–365, L425–428)
   - Result: higher‑order types produced via substitution can lose label ties, weakening lifetime constraints at call sites.

## Soundness / TCB risks
- **Lifetime labels are outside kernel validation.**
  - Definitions carry `ref_lifetime_labels` but the kernel does not validate them (unlike capture modes). (`kernel/src/checker.rs` L730–770; `kernel/src/ast.rs` L170–189)
  - If labels are lost or mis‑propagated by frontend transformations, borrow checking can be under‑constrained. This expands the TCB to include elaborator metadata handling.

- **Defeq fuel exhaustion remains a semantic DoS.**
  - Fixed default fuel (`LRL_DEFEQ_FUEL`, default 100k) + transparent unfolding can reject valid definitional equalities. (`kernel/src/nbe.rs` L1003–1017; `kernel/src/checker.rs` L2989–3038)

- **Partial MIR typing leaves correctness to lowering discipline.**
  - Only call terminators are checked; invalid assignments/refs could slip through if lowering regresses. (`mir/src/analysis/typing.rs` L51–79)

## Semantic gaps (severity)
- **[High] Non‑structural lifetime labels can be dropped by `shift`/`subst`, weakening region ties.**
  - Labels are not embedded in core terms; transformations can silently lose them.
- **[Medium] Defeq fuel can reject valid terms.**
  - Transparent unfolding + fixed fuel yields false negatives.
- **[Low] Spec drift for function kinds.**
  - Core calculus spec still out of sync.

## Minimal reproducible examples
1. **Lifetime label loss through substitution (core‑level).**
   - Core operations rebuild terms without copying labels.
   - Any function type produced via `subst` can drop explicit labels and be lowered with weaker region ties.
   - Evidence: `Term::subst` rebuilds `Ref` occurrences with fresh `Rc` nodes and no label propagation. (`kernel/src/ast.rs` L651–688)

2. **Defeq fuel exhaustion (semantic DoS).**
```lisp
(def expand (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m) (add (expand m) (expand m))))))

;; Large n can cause DefEqFuelExhausted during type checking
;; when definitional equality unfolds `expand` aggressively.
```

## Fix plan (prioritized)
1. **Make lifetime labels structural.**
   - **What:** extend core `Term` or `Ref` representation to carry optional lifetime labels.
   - **Where:** `kernel/src/ast.rs`, `frontend/src/elaborator.rs`, `mir/src/lower.rs`.
   - **Why:** eliminate pointer‑map fragility; preserve labels through `shift`/`subst`.
   - **Tests:** higher‑order function types that preserve labels through substitution.

2. **Add kernel validation for lifetime labels.**
   - **Where:** `kernel/src/checker.rs` near `validate_capture_modes`.
   - **Why:** prevent mis‑labeled refs from weakening MIR constraints.
   - **Tests:** reject labels on non‑Ref terms; reject ambiguous elision in core input.

3. **Audit all term‑rebuilding paths for metadata propagation.**
   - **Where:** `kernel/src/ast.rs` (`shift`, `subst`), `frontend/src/elaborator.rs` (coercions).
   - **Why:** stop silent loss of label metadata.

4. **Document lifetime label surface syntax explicitly.**
   - **Where:** `docs/spec/ownership_model.md`, `docs/spec/mir/typing.md`.
   - **Why:** clarify `Ref #label Shared T` usage.

5. **Defeq fuel policy + diagnostics.**
   - **Where:** `kernel/src/nbe.rs`, `kernel/src/checker.rs`, `cli/src/main.rs`.
   - **Why:** avoid false negatives; allow explicit control.
   - **Tests:** stress tests with configurable fuel.

6. **Extend MIR typing to statements.**
   - **Where:** `mir/src/analysis/typing.rs`.
   - **Why:** reduce reliance on lowering correctness.
   - **Tests:** invalid assignment/borrow statements caught by typing checker.

7. **Update core calculus spec for `FnMut`.**
   - **Where:** `docs/spec/core_calculus.md`.
   - **Why:** spec/impl alignment.

8. **Add regression tests for labeled lifetime propagation.**
   - **Where:** `cli/tests/pipeline_golden.rs`, `mir/tests/borrowck_corpus.rs`.
   - **Why:** catch label‑dropping regressions.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Lifetime labels are structural (no pointer‑map dependence).
- [ ] Kernel validates lifetime labels/elision.
- [ ] Defeq fuel policy documented and configurable.
- [ ] MIR typing validates statements beyond call terminators.
- [ ] Core calculus spec updated for `FnMut`.

## Suggested GitHub issues (titles + labels)
- **“Lifetime labels are pointer‑mapped; `shift`/`subst` drops them”** — labels: bug, soundness, frontend, mir
- **“Add kernel validation for lifetime label annotations”** — labels: design, soundness, kernel
- **“Defeq fuel policy + diagnostics”** — labels: design, kernel
- **“MIR typing checker only validates calls; add statement typing”** — labels: bug, mir
- **“Update core_calculus spec for FnMut”** — labels: docs
