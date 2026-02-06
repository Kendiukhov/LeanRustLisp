# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-04 Round 11

## Executive summary
- **Major fixes landed:** macro hygiene now requires exact scope match; macro boundary flags any `axiom` (tagged or not); MIR lowering unfolds transparent aliases via WHNF and uses `MirType::Opaque` instead of `Unit`. (`frontend/src/desugar.rs` L23–25; `frontend/src/macro_expander.rs` L56–74, L499–521; `mir/src/lower.rs` L291–333; `mir/src/types.rs` L595–637)
- **New blocker:** *opaque* type aliases can hide `Ref` from MIR; borrow checker only creates loans when the destination type is `MirType::Ref`, so `borrow_mut` into an opaque alias can bypass borrow checking. (`mir/src/lower.rs` L291–333; `mir/src/analysis/nll.rs` L564–579)
- **Contract violation persists:** effects are described as type‑level (`Comp`) but only syntactic totality checks exist in the kernel. (`README.md` L25–27, L52–53; `kernel/src/checker.rs` L5142–5196)
- **Defeq remains fuel‑bounded** (semantic DoS risk). (`kernel/src/nbe.rs` L1011–1105)
- **Compiler correctness risk:** MIR typing treats `Opaque` as a wildcard outside of references, allowing mismatched assignments or calls to pass. (`mir/src/analysis/typing.rs` L587–598)
- **Per earlier instruction:** not re‑evaluating the “import classical placeholder axiom” issue in this round.

## Contract violations
1. **Effect system promised in types, not enforced.**
   - README says partial defs “live under an effect (e.g., `Comp`).” (`README.md` L25–27, L52–53)
   - Kernel only enforces totality boundaries via `check_effects`; it does **not** require `Comp` in the return type. (`kernel/src/checker.rs` L5142–5196)

2. **Rust‑grade resource discipline undermined by opaque aliases of `Ref`.**
   - README promises Rust‑grade ownership/borrowing guarantees. (`README.md` L49–50)
   - MIR lowering turns opaque type aliases into `MirType::Opaque`, not `MirType::Ref`. (`mir/src/lower.rs` L291–333; `mir/src/types.rs` L595–637)
   - NLL only creates loans when the destination type is `MirType::Ref`. (`mir/src/analysis/nll.rs` L564–579)
   - Result: an `opaque` alias to `Ref Mut A` can bypass borrow checking entirely.

## Soundness / TCB risks
**Kernel soundness**
- **Semantic DoS via defeq fuel** (Medium). Fuel‑bounded defeq can reject valid programs under heavy unfolding. (`kernel/src/nbe.rs` L1011–1105)

**Compiler correctness / safety**
- **Opaque alias bypasses borrow checking** (High). If a type alias to `Ref` is marked `opaque`, MIR lowers it to `MirType::Opaque`, so `borrow_mut` produces no loan. (`mir/src/lower.rs` L291–333; `mir/src/analysis/nll.rs` L564–579)
- **`Opaque` treated as wildcard by MIR typing** (Medium). Outside of references, `types_compatible` returns `true` when either side is `Opaque`, so mismatches can slip into codegen. (`mir/src/analysis/typing.rs` L587–598)

## Semantic gaps (severity)
- **[High] Opaque types can hide reference semantics.** Borrow checking does not track loans for opaque destinations, so `borrow_mut` under an opaque alias can be accepted.
- **[High] Effect typing not enforced.** Partial defs need not return `Comp`, contrary to the design contract.
- **[Medium] Defeq fuel DoS.** Large transparent unfolding can still exhaust fuel in valid developments.
- **[Medium] MIR typing uses `Opaque` as a wildcard.** Type mismatches can pass undetected.

## Minimal reproducible examples
1. **Opaque alias hides `Ref` from borrow checker (should be rejected):**
```lisp
(opaque MyRef (sort 1) (Ref Mut Nat))

(def demo (pi x Nat Nat)
  (lam x Nat
    (let r MyRef (borrow_mut x)
      ;; Should be rejected: x used while mutably borrowed
      x)))
```
Evidence: opaque alias lowers to `MirType::Opaque`; loans only created for `MirType::Ref`. (`mir/src/lower.rs` L291–333; `mir/src/analysis/nll.rs` L564–579)

2. **Partial def without effect type (contract mismatch):**
```lisp
(partial loop (pi n Nat Nat)
  (lam n Nat (loop n)))
```
Kernel only enforces totality boundaries, not effect types. (`kernel/src/checker.rs` L5142–5196)

3. **Defeq fuel exhaustion (semantic DoS):**
```lisp
(def expand (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m) (add (expand m) (expand m))))))
```
Large `n` can exhaust defeq fuel. (`kernel/src/nbe.rs` L1011–1105)

## Fix plan (prioritized)
1. **Unfold opaque aliases for borrow‑shape detection.**
   - **What:** In MIR lowering, use `Transparency::All` (or a dedicated “shape” reducer) when checking for `Ref`/interior‑mutability forms, even if the type is opaque for defeq.
   - **Where:** `mir/src/lower.rs` (`lower_type_general`, `lower_type_in_fn`).
   - **Why:** Prevent opaque aliases from hiding references.
   - **Tests:** `opaque` alias to `Ref Mut` still lowers to `MirType::Ref`; NLL sees loans.

2. **Loan creation fallback for opaque destinations.**
   - **What:** If `Rvalue::Ref` targets a destination whose type is `MirType::Opaque`, still create a loan with a synthetic region derived from the destination (or force lowering to `Ref`).
   - **Where:** `mir/src/analysis/nll.rs` loan creation path; potentially `mir/src/lower.rs`.
   - **Why:** Ensure borrow operations are always tracked.
   - **Tests:** `borrow_mut` into opaque alias triggers borrow conflict when re‑borrowing.

3. **Opaque typing strictness.**
   - **What:** Make `types_compatible` reject `Opaque` mismatches unless both sides share the same opaque reason (or a compatible tag).
   - **Where:** `mir/src/analysis/typing.rs`.
   - **Why:** Prevent type mismatches from slipping into codegen.
   - **Tests:** assignments between distinct opaque types are rejected.

4. **Effect typing enforcement for partial defs.**
   - **What:** Require `partial def` to return `Comp A` (or explicit effect), and reject if not.
   - **Where:** `kernel/src/checker.rs` (definition admission), `frontend/src/elaborator.rs` (surface diagnostics).
   - **Why:** Align with README contract.
   - **Tests:** `partial def` returning `Nat` fails; `Comp Nat` passes.

5. **Document effect policy if full enforcement is deferred.**
   - **Where:** `README.md`, `docs/spec/phase_boundaries.md`.
   - **Why:** Avoid spec/impl mismatch if enforcement is not immediate.

6. **Defeq fuel mitigations.**
   - **What:** Add per‑definition hints or profiling to reduce transparent unfolding hot‑spots; consider per‑def `opaque` recommendations.
   - **Where:** `kernel/src/nbe.rs`, `cli/src/driver.rs`.
   - **Tests:** defeq fuel exhaustion includes policy source and actionable hints.

7. **Add regression tests for opaque ref aliases.**
   - **Where:** `mir/src/lower.rs` tests or `cli/tests/*`.
   - **Why:** Prevent future borrow‑check bypasses.

8. **Audit borrow‑shape detection for reserved primitives.**
   - **Where:** `mir/src/lower.rs`, `kernel/src/checker.rs`.
   - **Why:** Ensure any user‑facing reference type is recognized even under opacity.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Opaque aliases cannot hide `Ref`/borrow semantics from MIR.
- [ ] `partial def` is effect‑typed (or docs updated to reflect current behavior).
- [ ] `Opaque` types are not treated as wildcards in MIR typing.
- [ ] Defeq fuel DoS is documented with mitigations and tests.

## Suggested GitHub issues (titles + labels)
- **“Opaque type aliases can bypass borrow checking (no loans for `borrow_mut`)”** — labels: bug, soundness, mir
- **“Effect typing not enforced for partial defs (Comp missing)”** — labels: design, kernel, docs
- **“MIR typing treats Opaque as wildcard outside refs”** — labels: bug, mir
- **“Defeq fuel DoS: add mitigation + tests”** — labels: design, kernel, test
