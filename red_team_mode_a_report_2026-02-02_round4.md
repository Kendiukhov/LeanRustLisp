# Red Team Mode A Report (Round 4 — 2026-02-02)

Scope: semantic soundness (pre-codegen). Focused on kernel boundaries, definitional equality, total/partial/unsafe separation, ownership/borrowing, macro hygiene, and NLL.

## 1) Executive Summary
- **Blocker:** Total fragment still accepts **general recursion via `fix`**, violating the “def = total” contract and enabling nontermination inside types/defeq.
- **High:** Closure kind inference can still **misclassify `Fn` vs `FnOnce`** by treating implicit binders as observational while the kernel allows implicit binders to be used in consuming positions.
- **Med:** Definitional equality remains **DoS-prone** under transparent unfolding + `fix`; fuel exists but attacker-controlled fuel exhaustion is still easy.
- **Low:** Prop/large-elimination checks and classical axiom tracking appear consistent this round; no new laundering path found.
- **Low:** Macro hygiene looks deterministic/scope-based; no capture leak found, but still needs targeted adversarial tests.

**Verdict:** **No-Go** for stdlib expansion until `fix`/totality and implicit-binder closure-kind soundness are fixed.

## 2) Contract Violations (README promises vs code)

1) **“def” is not strictly terminating**
   - **Contract:** README says `def` (total fragment) must be strictly terminating and safe for types/defeq.
   - **Evidence:**
     - `frontend/src/elaborator.rs:1050-1068` — `SurfaceTermKind::Fix` elaborates directly to `Term::Fix` in any context.
     - `kernel/src/checker.rs:436-470` — total definitions only reject partials in the **type**, not the value; no guard against `fix` in total values.
     - `kernel/src/checker.rs:1244-1260, 1348-1351` — termination checks treat `Term::Fix` as a normal binder; no rejection of general recursion.
     - `kernel/src/checker.rs:3152-3171` — `contains_partial_def` flags `fix` only when it appears syntactically in a type; a total def with `fix` in its **body** still counts as type-safe.

2) **Rust-grade resource safety undermined by implicit-binder laundering**
   - **Contract:** README + `docs/spec/function_kinds.md` require capture-based kind inference to prevent duplication of linear values.
   - **Evidence:**
     - `frontend/src/elaborator.rs:532-568` — implicit binders are treated as **observational**, so passing a capture as an implicit arg does not force `FnOnce`.
     - No kernel rule enforces “implicit binder = observational-only”; any implicit binder may accept runtime (non-Prop) values.
     - `kernel/src/checker.rs:2827-2833` — kernel trusts the kind annotation and treats captures as observational for `Fn`, so under-inferred `Fn` can consume linear captures unsafely.

## 3) Soundness / TCB Risks

- **Kernel trusts elaborator’s function-kind inference.** A wrong inference becomes a **kernel-level soundness hole** because ownership checking relies on the declared kind.
- **`fix` in total fragment** undermines kernel soundness: nontermination can be embedded in “total” defs that appear in types/defeq.
- **Defeq DoS**: `nbe::apply_with_config` unfolds `Value::Fix` (fuel-driven), enabling attackers to force fuel exhaustion during typechecking (`kernel/src/nbe.rs:1228-1235`).

## 4) Semantic Gaps (severity)

- **[High] Implicit binder semantics are underspecified** — no enforcement that implicit args are observational-only or Prop-only.
- **[High] `fix` is not gated by totality/effect** — allows general recursion in total defs.
- **[Med] Defeq remains vulnerable to transparent-unfolding blowups** — fuel mitigates but doesn’t prevent attacker-triggered slowdown.
- **[Low] No explicit FnMut support yet** — design gap given current direction (Fn/FnMut/FnOnce).

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
- **Expected:** `loop` rejected in `def` or `bad_eq` fails without defeq divergence.
- **Actual:** `loop` accepted; `bad_eq` can trigger defeq fuel exhaustion / nontermination.

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
- **Expected:** `make` should infer `FnOnce` (or reject `#[fn]`); `bad` should fail.
- **Actual:** Implicit args are treated observationally; `make` can remain `Fn`, enabling double-use of `b`.

## 6) Fix Plan (Prioritized Tasks)

1) **Reject `fix` in total defs**
   - **What:** Disallow `Term::Fix` in `Totality::Total` values.
   - **Where:** `kernel/src/checker.rs` (definition add + effect checks).
   - **Why:** Preserve total fragment soundness.
   - **Tests:** `def loop` rejected; `partial def` accepts.

2) **Make `fix` partial-only at effect boundary**
   - **What:** Extend `check_effects` to flag `Term::Fix` unless context is partial/unsafe.
   - **Where:** `kernel/src/checker.rs::check_effects`.
   - **Why:** Align recursion with effect system.
   - **Tests:** total def with fix fails; partial def ok.

3) **Kernel revalidation of function kinds**
   - **What:** Compute conservative required kind in kernel and reject `Fn` when captures are consumed.
   - **Where:** `kernel/src/checker.rs` (ownership / new validation pass).
   - **Why:** Shrink TCB; don’t trust elaborator for soundness.
   - **Tests:** closure consuming capture annotated `Fn` is rejected.

4) **Enforce implicit binder semantics**
   - **What:** Restrict implicit binders to observational-only or Prop-only usage.
   - **Where:** `kernel/src/checker.rs` (Pi/Lam checks) + `frontend/src/elaborator.rs`.
   - **Why:** Prevent implicit-arg laundering of linear consumption.
   - **Tests:** implicit consumption of non-Prop value rejected.

5) **Conservative elaborator inference for implicit args**
   - **What:** Treat implicit args as consuming unless proven Copy/Prop.
   - **Where:** `frontend/src/elaborator.rs:532-568`.
   - **Why:** Avoid under-approximation of `FnOnce`.
   - **Tests:** Repro 2 should infer FnOnce / reject `#[fn]`.

6) **Defeq guardrails for `fix`**
   - **What:** Fail fast (clear error) if defeq tries to unfold fix in total contexts.
   - **Where:** `kernel/src/nbe.rs`, `kernel/src/checker.rs`.
   - **Why:** Prevent DoS in typechecking.
   - **Tests:** defeq with fix triggers explicit error.

7) **Add regression tests**
   - **What:** LRL tests for `fix` in total, implicit-arg capture, kind mismatch errors, defeq fuel diagnostic.
   - **Where:** `tests/`, `kernel/tests`, `frontend/tests`, `cli/tests`.
   - **Why:** Lock in fixes.

8) **Documentation updates**
   - **What:** Document implicit binder semantics and `fix` policy; update `function_kinds.md` and ownership spec.
   - **Where:** `docs/spec/*`, `docs/production.md`.

## 7) Go/No-Go Checklist (stdlib expansion)

**No-Go until:**
- `fix` is rejected in total defs and blocked by effect checks.
- Kernel independently validates function kinds (no elaborator trust).
- Implicit binders have enforced semantics (observational or Prop-only).
- Regression tests cover implicit-arg capture + fix-in-total.

**Safe-to-proceed once:**
- All above pass in CI + golden tests.
- Classical/unsafe axiom tracking still accurate.
- Macro expansion remains deterministic under new tests.

## Suggested GitHub Issues

1) **“Reject `fix` in total defs (partial-only recursion)”** — labels: bug, soundness, kernel
2) **“Kernel revalidates closure kinds (don’t trust elaborator)”** — labels: bug, soundness, kernel
3) **“Implicit binder enforcement (observational-only or Prop-only)”** — labels: bug, soundness, design
4) **“Conservative kind inference for implicit args”** — labels: bug, soundness
5) **“Defeq guardrails for fix/transparent unfolding”** — labels: bug, perf, soundness
6) **“FnMut support roadmap (if desired)”** — labels: design, docs
