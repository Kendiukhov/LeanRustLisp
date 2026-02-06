# Red Team Mode A — Parallel Streams (Round 10)

Goal: execute the Round 10 fix plan without overlap, with explicit file/folder ownership and minimal dependencies.

## Stream A — MIR Type Alias / Erasure Fixes (Ownership Soundness)
**Scope:** Make MIR lowering respect transparent aliases; prevent `Unit`-based Copy escalation.

- **A1. Lower via WHNF before erasure**
  - **What:** In `lower_type_general` and `lower_type_in_fn`, call `whnf_in_ctx` on the type to expand transparent aliases before pattern matching.
  - **Where:** `mir/src/lower.rs`
  - **Why:** Prevent alias-to-`Unit` erasure that bypasses borrow/ownership checks.
  - **Tests:** Add MIR snapshot or debug print proving `MyRef := Ref Mut Nat` lowers to `MirType::Ref`.

- **A2. Stop Copy escalation from erased MIR types**
  - **What:** Only set `is_copy = true` if kernel Copy says so, not merely because `MirType::Unit` is Copy. Consider a distinct `MirType::Erased/Opaque`.
  - **Where:** `mir/src/lower.rs` (`push_local`, `push_temp_local`), `mir/src/types.rs`
  - **Why:** Avoid making non-Copy alias types trivially Copy.
  - **Tests:** Regression that alias `Ref Mut` is not Copy in MIR locals.

- **A3. Optional: introduce `MirType::Erased`**
  - **What:** Add explicit `MirType::Erased` for type-erased terms and treat it as non-Copy.
  - **Where:** `mir/src/types.rs`, `mir/src/lower.rs`, `mir/src/analysis/ownership.rs`, `mir/src/analysis/nll.rs`, `mir/src/analysis/typing.rs`
  - **Why:** Preserve erasure semantics without collapsing to `Unit`.
  - **Tests:** Ensure ownership + borrow checks treat `Erased` as non-Copy.

**Files/Folders:** `mir/src/lower.rs`, `mir/src/types.rs`, `mir/src/analysis/*`, `tests/` or `cli/tests/` for regressions.
**Dependencies:** None. (Can run in parallel with other streams.)

---

## Stream B — Macro Hygiene Enforcement
**Scope:** Ensure macro-introduced identifiers cannot capture call-site bindings.

- **B1. Tighten scope compatibility**
  - **What:** Change `scopes_compatible`/`resolve_binding` to require exact match (or documented strict rule) rather than subset match.
  - **Where:** `frontend/src/desugar.rs`
  - **Why:** Align implementation with hygiene spec; prevent capture.
  - **Tests:** Add macro example `(defmacro m () x)` not capturing caller `x`.

- **B2. Update hygiene tests**
  - **What:** Add/adjust `frontend` tests or snapshots for capture vs non-capture cases.
  - **Where:** `frontend/tests/*`, `frontend/tests/snapshots/*`

**Files/Folders:** `frontend/src/desugar.rs`, `frontend/tests/*`.
**Dependencies:** None.

---

## Stream C — Macro Boundary Hardening (Axioms)
**Scope:** Prevent untagged axioms from being macro-injected under `Deny`.

- **C1. Detect all `axiom` forms**
  - **What:** Treat any `(axiom ...)` in macro output as a macro-boundary hit, regardless of tags.
  - **Where:** `frontend/src/macro_expander.rs`
  - **Why:** Close TCB expansion loophole in prelude.
  - **Tests:** Macro producing `(axiom foo ...)` should error under `Deny`.

**Files/Folders:** `frontend/src/macro_expander.rs`, `frontend/tests/*`.
**Dependencies:** None (parallel to Stream B if tests are separate files).

---

## Stream D — Effect Typing Enforcement or Spec Alignment
**Scope:** Align effect system with README promises.

- **D1. Enforce `Comp` return for `partial def` (if chosen)**
  - **What:** In `check_effects` or definition admission, require `partial def` to return `Comp A` (or explicit effect).
  - **Where:** `kernel/src/checker.rs`, `frontend/src/elaborator.rs` (if surface checks needed)
  - **Why:** Match README contract.
  - **Tests:** Partial def returning `Nat` rejected; `Comp Nat` accepted.

- **D2. Or: Document current policy (if enforcement deferred)**
  - **What:** Update README/spec to clarify partial defs are syntactic-only until effect typing is implemented.
  - **Where:** `README.md`, `docs/spec/phase_boundaries.md`

**Files/Folders:** `kernel/src/checker.rs`, `frontend/src/elaborator.rs`, `README.md`, `docs/spec/*`.
**Dependencies:** None.

---

## Stream E — Defeq Fuel Mitigation & Diagnostics
**Scope:** Reduce semantic DoS risk and make mitigation predictable.

- **E1. Improve diagnostics / policy visibility**
  - **What:** Ensure fuel-exhaustion errors include current policy source and actionable guidance.
  - **Where:** `kernel/src/nbe.rs`, `cli/src/driver.rs`, `cli/src/main.rs`

- **E2. Add defeq-stress tests**
  - **What:** Add test that triggers fuel exhaustion with a clear message and another that succeeds with higher fuel.
  - **Where:** `kernel/src/lib.rs` tests or `cli/tests/*`

**Files/Folders:** `kernel/src/nbe.rs`, `cli/src/driver.rs`, `cli/src/main.rs`, `kernel/src/lib.rs` or `cli/tests/`.
**Dependencies:** None.

---

## Notes on Parallelism
- Streams A–E are independent and can run concurrently.
- The only **optional** dependency is if you choose to introduce `MirType::Erased` (A3); then any new tests in other streams that assume `Unit` semantics must be updated accordingly.

