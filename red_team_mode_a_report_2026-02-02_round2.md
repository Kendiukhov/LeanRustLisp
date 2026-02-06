# LRL Red Team Report — Mode A (Semantic / Soundness) — Round 2 (2026-02-02)

Scope: kernel, frontend (elaboration/macros), CLI pipeline, MIR borrow checking, stdlib prelude. Focused on semantic guarantees and kernel boundary.

## Executive Summary
- Significant progress: unsafe axioms are now tracked and blocked in types, inductive axiom deps are recorded, Prop constructors are type‑safety checked, recursor levels are fixed, and `eval` is forbidden in type position.
- The **biggest remaining hole is explicit `instance copy`**: it lets users assert Copy for arbitrary inductives (including interior‑mutable), bypassing linearity checks.
- **Function types are still always Copy**, enabling closure duplication of captured linear values—this is a direct mismatch with “Rust‑grade resource discipline.”
- Copy instances (explicit or derived) are **not tracked as axioms/unsafe dependencies**, so critical trust assumptions are invisible to diagnostics.
- Reserved primitive names are enforced, but **kernel behavior depends on the caller toggling `allow_reserved_primitives`**; custom pipelines can still create semantic mismatches with MIR lowering.
- Defeq fuel diagnostics exist, but **transparent unfolding + large fuel still permits defeq‑DoS**; it’s mitigated, not eliminated.
- Net: **Not safe to expand stdlib yet** until Copy instance trust and closure‑capture issues are resolved.

---

## Contract Violations (with Evidence)

1) **Explicit Copy instance bypasses linearity / interior mutability rules**
- Evidence:
  - `Declaration::Instance` directly registers Copy instances with no proof or `unsafe` gate: `cli/src/driver.rs:1029–1167`.
  - Explicit instances are preferred over derived ones: `kernel/src/checker.rs:241–248`.
  - Copy checks consult these instances to allow duplication: `kernel/src/checker.rs:2557–2588`.
  - Interior‑mutable types are blocked only for *derived* Copy; explicit instance still allowed: `kernel/src/checker.rs:3429–3431`.
- Contract breach: “Rust‑grade resource discipline” can be bypassed by user‑declared Copy.

2) **Functions are always Copy, enabling closure duplication of linear captures**
- Evidence:
  - `is_copy_type_inner` returns `Ok(true)` for all `Pi` types: `kernel/src/checker.rs:2559`.
- Contract breach: Rust closures that capture linear values are not Copy; LRL currently treats all functions as Copy.

3) **Copy assumptions are not tracked as axioms/unsafe dependencies**
- Evidence:
  - Axiom tracking collects from defs/inductives only: `kernel/src/checker.rs:3621–3643`.
  - CLI reports axioms from `def.axioms` and `decl.axioms` only: `cli/src/driver.rs:1455–1505`.
  - Copy instances are stored in `env.copy_instances` with no axiom tagging.
- Contract breach: trust assumptions affecting safety are invisible to dependency reporting.

---

## Soundness / TCB Risks
- **Copy instances are de‑facto axioms** (unverified assumptions) but live outside axiom tracking and diagnostics.
- **Closure capture is not modeled**: `Pi` is always Copy; ownership is checked at lambda creation, not at use.
- **Reserved primitive gating depends on caller**: kernel allows reserved primitives if `allow_reserved_primitives` is true (`kernel/src/checker.rs:347–350`). A custom pipeline can accidentally allow user‑defined `borrow_*`/`index_*` that MIR still special‑cases.

---

## Semantic Gaps (Severity)
- **Blocker:** Explicit Copy instance is untrusted and untracked; interior‑mutable types can be marked Copy by fiat.
- **High:** Function types are Copy regardless of captured linear values; closure duplication unsoundness.
- **Medium:** Copy assumptions aren’t reported as axioms/unsafe dependencies (auditability gap).
- **Medium:** Defeq DoS remains possible despite fuel caps; transparency defaults are still “Reducible.”
- **Low:** Capability tokens (`EvalCap`) are not enforced beyond type position; effect safety depends on `unsafe` labeling only.

---

## Minimal Reproducible Examples

### 1) Explicit Copy instance bypass (Blocker)
```lrl
;; RefCell is interior-mutable in prelude.
(instance copy (pi T (sort 1) (RefCell T)))

(def dup_refcell (pi r (RefCell Nat) (List (RefCell Nat)))
  (lam r (RefCell Nat)
    (cons r (cons r (nil)))))
```
Expected: reject (RefCell is not Copy). Actual: explicit instance makes it Copy.

### 2) Closure duplication of linear captures (High)
```lrl
(inductive Box (pi A (sort 1) (sort 1))
  (ctor mk_box (pi {A (sort 1)} (pi x A (Box A))))
)

(def dup_via_closure (pi r (Box Nat) (List (Box Nat)))
  (lam r (Box Nat)
    (let f (pi _ Nat (Box Nat)) (lam _ Nat r)
      (cons (f zero) (cons (f zero) (nil))))))
```
Because `Pi` is Copy, `f` is used twice, duplicating `r`.

---

## Fix Plan (Prioritized, 10–20 Tasks)
1) **Gate explicit Copy instances behind `unsafe`**
   - Where: `cli/src/driver.rs` (instance parsing), `kernel/src/checker.rs` (CopyInstance).
   - Why: prevent untrusted Copy assertions from being treated as safe.
   - Tests: explicit Copy on `RefCell` should fail unless `unsafe`.

2) **Track Copy instances as unsafe/axiom dependencies**
   - Where: `kernel/src/checker.rs`, `cli/src/driver.rs` reporting.
   - Why: make Copy assumptions auditable.
   - Tests: diagnostics show “unsafe: copy_instance(Foo)” or similar.

3) **Make function types non‑Copy by default**
   - Where: `kernel/src/checker.rs` `is_copy_type_inner`.
   - Why: avoid closure duplication of captured linear values.
   - Tests: `dup_via_closure` should be rejected.

4) **Or: add capture‑aware Copy for lambdas**
   - Where: `check_ownership_in_term` / new analysis.
   - Why: allow Copy functions only if closure captures Copy‑only vars.
   - Tests: closure capturing `Nat` is Copy; capturing `Box` is not.

5) **Prevent explicit Copy instances for interior‑mutable types (even unsafe?)**
   - Where: `derive_copy_instance`/instance registration.
   - Why: interior mutability + Copy is unsound without deep guarantees.
   - Tests: explicit instance for `RefCell` fails.

6) **Add instance‑level proof obligations (if intended)**
   - Where: `cli/src/driver.rs` (instance parsing) + kernel proof checker.
   - Why: make Copy instances a verified theorem rather than an axiom.
   - Tests: instance requires proof term.

7) **Harden reserved primitive gating in kernel**
   - Where: `kernel/src/checker.rs` (`allow_reserved_primitives`).
   - Why: prevent accidental enabling in custom pipelines.
   - Tests: ensure user code can’t define reserved primitives outside prelude.

8) **Add negative tests for explicit Copy instances**
   - Where: `cli/tests/pipeline_negative.rs`, `kernel/tests/negative_tests.rs`.
   - Why: lock in safety behavior.

9) **Add ownership regression for closure capture**
   - Where: `kernel/tests/semantic_tests.rs` or new ownership tests.
   - Why: ensure linear values cannot be duplicated via closures.

10) **Defeq DoS hardening**
   - Where: `kernel/src/nbe.rs` / `kernel/src/checker.rs` / CLI flags.
   - Why: still possible to craft large transparent chains.
   - Tests: large unfolding should emit explicit “fuel exhausted” with hint.

---

## Go / No‑Go Checklist (Stdlib Expansion)
- **No‑Go until:** explicit Copy instances are gated/verified, function Copy semantics fixed, Copy assumptions are tracked.
- **Go when:** linearity is enforced for closures, Copy instances are auditable, and reserved primitive gating is hardened.

---

## Suggested GitHub Issues (Title — Labels)
1) “Explicit Copy instances bypass linearity (require unsafe/proof)” — labels: bug, soundness
2) “Function types always Copy (closure capture duplication)” — labels: bug, soundness
3) “Track Copy instances as unsafe dependencies in diagnostics” — labels: design, docs
4) “Harden reserved primitive gating in kernel” — labels: bug, design
5) “Add negative tests for Copy instance and closure capture” — labels: test, soundness
6) “Defeq fuel exhaustion policy + user diagnostics” — labels: design, test

