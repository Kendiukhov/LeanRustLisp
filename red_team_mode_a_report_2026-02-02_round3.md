# Red Team Mode A Report (Round 3 — 2026-02-02)

Scope: semantic soundness (pre-codegen). Focused on kernel boundaries, definitional equality, total/partial/unsafe separation, ownership/borrowing, macro hygiene, and NLL.

## 1) Executive Summary
- **Blocker:** Total fragment admits **general recursion via `fix`**; termination checker does not reject it, so non-terminating defs can be marked `def` (total) and used in types/defeq.
- **High:** Closure-kind inference can **under-approximate `FnOnce`** because implicit binders are treated as observational, yet implicit binders are not restricted to observational usage in function bodies. This allows **`Fn` closures that actually consume linear captures**.
- Definitional equality is still **DoS-prone** (transparent unfolding + `fix` eval) though there’s a fuel guard; user-visible errors are OK but still allow attacker-controlled typechecking blowups.
- Prop/elimination restrictions and axiom/classical tracking look materially improved; no obvious laundering found this round.
- Macro hygiene appears deterministic and scope-based; no concrete capture leak found.
- NLL pipeline is integrated for closures and top-level defs; no immediate unsoundness found, but closure-kind bugs can punch through it.

**Verdict:** **No-Go** for larger stdlib expansion until `fix` and implicit-binder/closure-kind soundness issues are resolved.

## 2) Contract Violations (README / spec vs code)

1) **Total fragment allows general recursion (`fix`)**
   - **Contract:** README “Total Fragment” must be strictly terminating and safe for use in types/defeq.
   - **Evidence:**
     - `frontend/src/elaborator.rs:1050-1068` — `SurfaceTermKind::Fix` is elaborated into `Term::Fix` without totality gating.
     - `kernel/src/checker.rs:436-470` — `Env::add_definition` only forbids partials in **types**, not in values; no check forbids `fix` in total defs.
     - `kernel/src/checker.rs:1244-1260, 1348-1351` — termination analysis treats `Term::Fix` like a normal binder; no rejection of general recursion.
     - `kernel/src/checker.rs:3152-3171` — `contains_partial_def` flags `fix` only when it appears syntactically; a total def that *contains* `fix` is still considered type-safe.

2) **Closure kind inference can misclassify `Fn` vs `FnOnce` via implicit binders**
   - **Contract:** “Rust-grade resource discipline” and `docs/spec/function_kinds.md` require capture-based kind inference to prevent unsound duplication of linear values.
   - **Evidence:**
     - `frontend/src/elaborator.rs:532-568` — implicit binders are treated as **observational** in `infer_needs_fn_once`, so passing a capture as an implicit arg does not force `FnOnce`.
     - There is **no kernel-side rule** that implicit binders must be observational-only; `SurfaceTermKind::Pi` accepts any Sort (`frontend/src/elaborator.rs:887-913`).
     - Kernel trusts the inferred kind and uses it to treat captured variables as observational (`kernel/src/checker.rs:2827-2833`), so a mis-inferred `Fn` closure can consume linear captures unsafely.

## 3) Soundness / TCB Risks

- **Kernel trusts elaborator’s function-kind inference.** If inference is wrong (e.g., implicit binder consumption), kernel ownership checking uses the kind annotation and will miss linearity violations. This makes the elaborator part of the **soundness-critical TCB**.
- **`fix` bypasses totality guarantees.** Since `fix` is allowed in total defs, normalization/defeq can diverge on terms that are considered type-safe. This undermines the “small trusted kernel” claim because the kernel accepts non-terminating total terms.
- **Defeq DoS with `fix`.** `nbe::apply_with_config` unfolds `Value::Fix` using fuel; a total def with `fix` can push defeq to fuel exhaustion in type checking (`kernel/src/nbe.rs:1228-1235`). It’s guarded but still an attacker-controlled denial of service.

## 4) Semantic Gaps (with severity)

- **[High] Implicit binder semantics are underspecified in the kernel.** Nothing enforces “implicit = observational only.” This invalidates the closure-kind inference assumption for implicit arguments.
- **[High] `fix` is not tied to partial/unsafe fragments.** There is no `partial`/`unsafe` gating for `fix` in term-level defs.
- **[Med] FnMut is not supported (spec says future).** User’s current direction wants Fn/FnMut/FnOnce; only Fn/FnOnce exist. (Design gap, not a soundness bug.)
- **[Low] Defeq DoS remains possible even with fuel.** “Opaque” is available, but no automatic mitigation or size-based warnings exist.

## 5) Minimal Reproducible Examples

### Repro 1 — `fix` in Total Fragment (Blocker)
```lisp
(def loop
  (pi x Nat Nat)
  (fix f (pi x Nat Nat)
    (lam x Nat (f x))))

(def bad_eq
  (Eq Nat (loop zero) zero)
  (refl Nat zero))
```
- **Expected:** `loop` must be rejected in `def` (total), or `bad_eq` must fail without defeq divergence.
- **Actual:** `loop` is accepted as total; `bad_eq` can trigger defeq fuel exhaustion / nontermination in typechecking.

### Repro 2 — Implicit Binder Consumes Capture But Closure Inferred `Fn`
```lisp
(inductive Box (pi A (sort 1) (sort 1))
  (ctor mk_box (pi {A (sort 1)} (pi x A (Box A)))))

(def consume_imp
  (pi {b (Box Nat)} (Box Nat))
  (lam {b} (Box Nat) b))

(def make
  (pi b (Box Nat) (pi #[fn] _ Nat (Box Nat)))
  (lam b (Box Nat)
    (lam #[fn] _ Nat (consume_imp {b}))))

(def bad
  (pi b (Box Nat) (Box Nat))
  (lam b (Box Nat)
    (let f (pi #[fn] _ Nat (Box Nat)) (make b)
      (let _ (Box Nat) (f zero)
        (f zero)))))
```
- **Expected:** `make` should infer `FnOnce` (or reject `#[fn]`), and `bad` should be rejected.
- **Actual:** inference treats implicit args observationally, so `make` can be `Fn`, allowing repeated calls that consume `b` twice.

## 6) Fix Plan (Prioritized Tasks)

1) **Forbid `fix` in total defs**
   - **What:** Reject `Term::Fix` in `def` / `Totality::Total` values.
   - **Where:** `kernel/src/checker.rs` (`Env::add_definition`, possibly `check_effects`).
   - **Why:** Prevent nontermination in total fragment.
   - **Tests:** new LRL test that `def loop` is rejected; `partial def` accepts it.

2) **Treat `fix` as Partial in effect checks**
   - **What:** Extend `check_effects` to flag `Term::Fix` in total/partial contexts.
   - **Where:** `kernel/src/checker.rs::check_effects`.
   - **Why:** Align `fix` with partial fragment boundary.
   - **Tests:** unit test: total def containing fix fails; partial def succeeds.

3) **Kernel-side validation of function kinds**
   - **What:** Recompute required kind in kernel (conservative) and reject `Fn` when captures are consumed.
   - **Where:** `kernel/src/checker.rs` (new `validate_function_kind` pass or integrate into ownership).
   - **Why:** Shrink TCB; do not trust elaborator for soundness.
   - **Tests:** closure that consumes capture but annotated `Fn` is rejected.

4) **Implicit binder usage restriction**
   - **What:** Enforce that implicit binders are observational-only or restricted to `Prop`/types.
   - **Where:** `kernel/src/checker.rs` (Pi/Lam check) and `frontend/src/elaborator.rs`.
   - **Why:** Prevent implicit-arg laundering of linear consumption.
   - **Tests:** implicit binder with non-Prop runtime type rejected or flagged.

5) **Align kind inference with kernel semantics**
   - **What:** In `infer_needs_fn_once`, treat implicit args as consuming unless proven Copy/Prop.
   - **Where:** `frontend/src/elaborator.rs:532-568`.
   - **Why:** Avoid under-approximating `FnOnce`.
   - **Tests:** Repro 2 should infer `FnOnce` and reject `#[fn]`.

6) **Add `fix` regression test to defeq fuel diagnostics**
   - **What:** Ensure defeq fuel exhaustion produces actionable error and does not crash.
   - **Where:** `kernel/tests` + `cli/tests` golden snapshots.
   - **Why:** Guard against DoS-like behavior.
   - **Tests:** `bad_eq` should error with fuel warning if `fix` slips through (until fixed).

7) **Document implicit binder semantics**
   - **What:** Specify in `docs/spec/function_kinds.md` and `docs/spec/ownership_model.md`.
   - **Where:** `docs/spec/*`.
   - **Why:** Prevent ambiguity that enables soundness gaps.

8) **Block `fix` at parse or elaboration for total defs**
   - **What:** Early error when `fix` appears in `def` (not `partial def`).
   - **Where:** `frontend/src/elaborator.rs` / `frontend/src/declaration_parser.rs`.
   - **Why:** Faster feedback; defense-in-depth.
   - **Tests:** parser/elaborator test for `def` + `fix` rejection.

9) **Add closure-kind tests for implicit-arg paths**
   - **What:** new tests where a capture is only used as implicit arg; should still require FnOnce if callee consumes.
   - **Where:** `tests/`, `frontend/tests`, `cli/tests`.
   - **Why:** Lock down regression.

10) **Audit uses of `Term::Fix` in NBE/defeq**
    - **What:** Add explicit guard or short-circuit for `fix` in total contexts to avoid diverging defeq.
    - **Where:** `kernel/src/nbe.rs`.
    - **Why:** Prevent accidental DoS even if `fix` slips in.
    - **Tests:** defeq on `fix` in total context fails fast with clear error.

11) **Add diagnostic for implicit binder misuse**
    - **What:** explicit error if implicit binder is used in consuming mode inside body.
    - **Where:** `kernel/src/checker.rs` (ownership pass)
    - **Why:** Concrete enforcement of implicit semantics.
    - **Tests:** `consume_imp` example should fail.

12) **Upgrade function kind spec if FnMut is planned**
    - **What:** add `FnMut` to spec + core representation + lowering plan.
    - **Where:** `docs/spec/function_kinds.md`, `kernel/src/ast.rs`, `frontend/src/elaborator.rs`.
    - **Why:** align with user’s “more Rust-like” direction.
    - **Tests:** capture-mut -> FnMut; Fn coercions; MIR call modes.

## 7) Go/No-Go Checklist (stdlib expansion)

**No-Go until all are true:**
- Total defs reject `fix` (and equivalent general recursion) in the kernel.
- Kernel independently validates closure kinds (no reliance on elaborator inference).
- Implicit binder semantics are enforced (implicit args observational-only or Prop-only).
- Regression tests cover implicit-arg capture and `fix`-in-total cases.
- Defeq fuel exhaustion is rare and cannot be triggered by total defs.

**Safe-to-proceed once:**
- All above items pass in CI + golden tests.
- Classical/unsafe axiom dependency reports remain correct.
- Macro expansion remains deterministic/hygienic under new tests.

## Suggested GitHub Issues

1) **“Reject `fix` in total defs (enforce partial-only recursion)”** — labels: bug, soundness, kernel
2) **“Kernel revalidates closure kinds (don’t trust elaborator)”** — labels: bug, soundness, kernel
3) **“Implicit binder enforcement: observational-only or Prop-only”** — labels: bug, soundness, design
4) **“Closure kind inference: implicit args must not under-approximate FnOnce”** — labels: bug, soundness
5) **“Defeq DoS guardrails for fix/transparent unfolding”** — labels: bug, perf, soundness
6) **“FnMut support plan (per design direction)”** — labels: design, docs, tests
