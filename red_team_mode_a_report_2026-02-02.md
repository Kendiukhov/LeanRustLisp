# LRL Red Team Report — Mode A (Semantic / Soundness) — 2026-02-02

Scope: kernel, frontend (parsing/elaboration/macros), MIR borrow checking, stdlib prelude. Focused on semantic guarantees: total/partial separation, Prop restrictions, axiom tracking, ownership/borrowing, macro hygiene, defeq/perf cliffs. This report reflects the current code state.

## Executive Summary (5–10 bullets)
- The kernel boundary is strengthened (core invariant validation + kernel re-check in CLI), but several **soundness-critical semantics are still user-controlled** (e.g., `copy` attribute) without kernel verification.
- **Ownership/linearity can be bypassed** by marking any inductive `copy`; the kernel trusts that flag and allows duplication (no structural validation).
- **Borrowing and indexing primitives are axioms** in the prelude and thus type-safe; they can appear in types and total definitions, violating the declared total/partial boundary and “safe code” semantics.
- **Classical/axiom tracking is incomplete**: inductive declarations that depend on axioms are not tracked, enabling axiom (including classical) laundering through types.
- **Prop inductives skip type-safety checks on constructor domains**, allowing partial defs in Prop types to sneak into the logic (decidability & fragment separation risk).
- Defeq fuel limits are now explicit but leave an **easy DoS/perf cliff** when transparent unfolding is default.
- Macro hygiene is improved and deterministic, but “reserved-by-name” primitives (borrow/index) are still string-matched in lowering, leaving sharp edges if users shadow names.
- **No-go for stdlib expansion** until copy/axiom/effect boundaries and axiom-tracking holes are closed.

## Stop-the-Line (Highest Risk)
1) **Copy attribute is unchecked → linearity bypass**
   - Evidence: `copy` is set from surface syntax with no validation (`frontend/src/declaration_parser.rs:56–74`) and trusted by kernel ownership checks (`kernel/src/checker.rs:2460–2469`).
   - Impact: Users can mark resource-carrying types as `copy` and duplicate linear values; violates “Rust-grade resource discipline.”
2) **Borrow/index primitives are axioms in total fragment**
   - Evidence: `borrow_shared`, `borrow_mut`, `index_*` are declared as axioms in the prelude (`stdlib/prelude.lrl:23–28`, `104–107`). Axioms are type-safe (`kernel/src/ast.rs:231–235`).
   - Impact: Effects/partiality can enter types and total code; runtime panics become possible in “safe” total definitions.
3) **Axiom tracking ignores inductive dependencies (classical laundering)**
   - Evidence: `collect_axioms_rec` only follows `Term::Const` (`kernel/src/checker.rs:3196–3223`) and `InductiveDecl` has no `axioms` field. Definitions using inductives do not inherit axiom deps.
   - Impact: Definitions can depend on classical or other axioms via inductives without being flagged.

## Safe-to-Proceed Checklist (for stdlib expansion)
- [ ] `copy` becomes kernel-verified (structural check) or marked `unsafe`/trusted with explicit warnings.
- [ ] Borrow/index primitives moved to `unsafe`/`partial` fragments or enforced by kernel effect system.
- [ ] Axiom dependencies are tracked through inductive declarations and recursors.
- [ ] Prop inductive constructor domains are checked for partial defs and core invariants.
- [ ] Recursor universe levels are correctly handled by elaborator for polymorphic inductives.
- [ ] Defeq fuel/perf policy documented; opaque-by-default for large defs or a budgeted defeq API.

---

## Contract Violations (w/ Evidence)
1) **Total/partial boundary violated by axioms in prelude**
   - Borrow and index primitives are declared as axioms, so they are “type-safe” and usable in total code/types:
     - `borrow_shared`, `borrow_mut` in `stdlib/prelude.lrl:23–28`
     - `index_vec_dyn`, `index_slice`, `index_array` in `stdlib/prelude.lrl:104–107`
     - Axioms are type-safe in kernel: `Definition::is_type_safe` includes `Totality::Axiom` (`kernel/src/ast.rs:231–235`).
   - Violates README’s “partial def cannot appear in types” and “safe code” constraints.
2) **Ownership/borrowing discipline can be bypassed by user `copy`**
   - `copy` is a surface attribute with no verification (`frontend/src/declaration_parser.rs:56–74`).
   - Kernel trusts `decl.is_copy` to allow duplication (`kernel/src/checker.rs:2460–2469`).
   - Violates “Rust-grade resource discipline” because copy semantics are not proven.
3) **Axiom dependency tracking is incomplete (classical laundering)**
   - Dependencies only collected from `Term::Const` (`kernel/src/checker.rs:3196–3223`); inductive declarations aren’t tracked.
   - A definition that only references an inductive can hide axiom/classical deps.
4) **Prop inductives skip type-safety checks for constructor domains**
   - `check_universe_levels` returns early for Prop (`kernel/src/checker.rs:3049–3051`), so constructor arguments in Prop inductives are not inferred/validated for type safety.
   - Violates strict total/partial separation inside Prop.

---

## Soundness / TCB Risks
- **User-controlled `copy` is in the kernel TCB**
  - The kernel uses `decl.is_copy` to relax linearity (`kernel/src/checker.rs:2460–2469`), but nothing ensures it is safe. This makes the kernel rely on untrusted surface attributes.
- **Axioms used as “library primitives”**
  - Borrow/index are axioms in `stdlib/prelude.lrl`, effectively expanding the trusted base to include runtime behavior not checked by kernel.
- **Axiom tracking ignores inductives**
  - `collect_axioms_rec` ignores `Term::Ind`, `Term::Ctor`, `Term::Rec` (`kernel/src/checker.rs:3196–3223`). The TCB silently includes inductive definitions that depend on axioms.
- **Name-based primitive lowering**
  - MIR lowering special-cases names `borrow_shared` / `borrow_mut` / `index_*` (`mir/src/lower.rs:600–655`). Shadowing or redefining these names can desync kernel semantics vs MIR lowering.

---

## Semantic Gaps (Severity)
- **Blocker:** `copy` attribute not validated (see above).
- **Blocker:** Borrow/index primitives are axioms; effect boundary bypass (see above).
- **High:** Axiom/classical tracking ignores inductive dependencies (`kernel/src/checker.rs:3196–3223`).
- **High:** Prop inductive constructor domains skip type-safety checks (`kernel/src/checker.rs:3049–3051`).
- **Medium:** Recursor levels for polymorphic inductives are not handled in elaborator.
  - `elaborate_match` and `infer_rec_application` only pass `[motive_level]` (`frontend/src/elaborator.rs:999–1004`, `698–707`), but kernel expects `univ_params + 1` levels.
- **Medium:** `eval` surface form is just a function call, no effect gating.
  - `eval` desugars to `SurfaceTermKind::Eval` (`frontend/src/desugar.rs:976–988`) and then to `Var("eval")` application (`frontend/src/elaborator.rs:638–651`).
- **Medium:** Defeq/perf DoS remains easy with transparent defaults.
  - Tests show exponential unfolding needs large fuel (`kernel/tests/semantic_tests.rs:243–301`).

---

## Minimal Reproducible Examples

### 1) Copy attribute allows linearity bypass (Blocker)
```lrl
(inductive copy Wrap (pi A (sort 1) (sort 1))
  (ctor mk_wrap (pi {A (sort 1)} (pi x A (Wrap A))))
)

(inductive Pair (pi A (sort 1) (pi B (sort 1) (sort 1)))
  (ctor mk_pair (pi {A (sort 1)} {B (sort 1)} (pi a A (pi b B (Pair A B)))))
)

(def dup (pi {A (sort 1)} (pi x (Wrap A) (Pair (Wrap A) (Wrap A))))
  (lam {A} (sort 1)
    (lam x (Wrap A)
      (mk_pair x x)))
)
```
Expected: should be rejected if `Wrap A` can contain linear resources. Actual: accepted because `Wrap` is marked `copy`.

### 2) Axiom/classical laundering via inductive (High)
```lrl
(axiom (classical) AxTy (sort 1))

(inductive Bad (sort 1)
  (ctor mk (pi x AxTy Bad))
)

(def uses_bad (pi x Bad Bad)
  (lam x Bad x))
```
Expected: `uses_bad` should be flagged as depending on classical axiom `AxTy`. Actual: dependency is not tracked because inductive deps aren’t collected.

### 3) Partial defs inside Prop inductive constructors (High)
```lrl
(partial def loop (pi A (sort 1) A)
  (lam A (sort 1)
    (fix f (pi x A A) (lam x A (f x)))))

(inductive BadProp (sort 0)
  (ctor mk (pi p (loop (sort 0)) BadProp))
)
```
Expected: reject (partial def appears in type). Actual: Prop inductive path skips type-safety checks.

### 4) Total code uses indexing axiom (Blocker)
```lrl
(def safe_index (pi v (VecDyn Nat) (pi i Nat Nat))
  (lam v (VecDyn Nat)
    (lam i Nat
      (index_vec_dyn v i))))
```
Expected: indexing should be partial/unsafe or effectful. Actual: accepted as total because `index_vec_dyn` is an axiom.

### 5) Defeq fuel cliff / DoS (Medium)
```lrl
(axiom pair (pi A (sort 1) (pi B (sort 1) (sort 1))))
(axiom z Nat)
(def boom0 Nat z)
(def boom1 Nat (pair boom0 boom0))
(def boom2 Nat (pair boom1 boom1))
;; ...repeat...
```
Expected: defeq should have bounded, predictable behavior. Actual: exponential unfolding can exceed fuel (see tests).

---

## Fix Plan (Prioritized Tasks, 10–20)
1) **Validate `copy` structurally**
   - What: derive `is_copy` from constructor field types (only copy fields) or require `unsafe copy`.
   - Where: `kernel/src/checker.rs` (ownership checks), `kernel/src/checker.rs` (inductive soundness), `kernel/src/ast.rs` (InductiveDecl).
   - Why: prevent linearity bypass.
   - Tests: add a negative test where `copy` wrapper around `Ref Mut` is rejected.
2) **Move borrow/index primitives to `unsafe` or `partial`**
   - Where: `stdlib/prelude.lrl` (borrow/index axioms), `frontend/src/declaration_parser.rs` (allow `unsafe`/`partial` attrs), `kernel/src/checker.rs` (effect checks).
   - Why: enforce total/partial boundary.
   - Tests: ensure total definitions calling `borrow_mut`/`index_vec_dyn` are rejected.
3) **Track axiom dependencies through inductives**
   - What: add `axioms: Vec<String>` to `InductiveDecl`, compute deps from `decl.ty` + `ctor.ty`, include in `collect_axioms_rec` for `Term::Ind/Ctor/Rec`.
   - Where: `kernel/src/ast.rs`, `kernel/src/checker.rs`, `cli/src/driver.rs` (artifact reporting).
   - Why: stop axiom/classical laundering.
   - Tests: the `Bad` example should report classical deps.
4) **Run core invariant validation on inductive types/ctors**
   - Where: `Env::add_inductive` in `kernel/src/checker.rs`.
   - Why: prevent metas/missing recursor levels from entering kernel via inductives.
   - Tests: add inductive with a meta in ctor type; must fail.
5) **Ensure Prop inductive constructors are type-safe**
   - What: remove early return in `check_universe_levels` or add a separate `ensure_type_safe` pass for Prop constructors.
   - Where: `kernel/src/checker.rs`.
   - Tests: the `BadProp` example should fail.
6) **Fix recursor universe levels in elaborator**
   - What: compute full level list (params + motive) for `Rec`.
   - Where: `frontend/src/elaborator.rs` (`elaborate_match`, `infer_rec_application`).
   - Why: make polymorphic inductives usable.
   - Tests: new polymorphic inductive + match should succeed.
7) **Reserve primitive names at kernel level**
   - What: prevent user definitions from shadowing `borrow_mut`, `borrow_shared`, `index_*`.
   - Where: `cli/src/driver.rs` or kernel env API.
   - Why: avoid MIR/kernel semantic mismatch.
   - Tests: redefining `borrow_mut` should error.
8) **Defeq budget policy + diagnostics**
   - What: propagate `DefEqFuelExhausted` as a distinct error and suggest `opaque` or fuel override.
   - Where: `kernel/src/checker.rs`, `cli/src/driver.rs` diagnostics.
   - Tests: defeq fuel exhaustion should surface a clear error.
9) **Effect-type boundary for `eval`**
   - What: make `eval` partial/unsafe (or a built-in effect) and disallow it in types.
   - Where: `frontend/src/desugar.rs`, `frontend/src/elaborator.rs`, `kernel/src/checker.rs`.
   - Tests: `eval` in type position rejected.
10) **Axiom audit pass for stdlib**
    - What: annotate axioms with tags (`classical`, `unsafe`) and enforce warnings.
    - Where: `stdlib/prelude.lrl`, `cli/src/driver.rs` reporting.
    - Tests: artifact includes classical/unsafe deps.
11) **Refine ownership for inductive fields**
    - What: optionally add `is_copy` derivation and deny `copy` if any constructor field is non-copy.
    - Where: `kernel/src/checker.rs` inductive soundness.
    - Tests: negative test for `copy` wrapper around non-copy.
12) **Borrow/lint coverage for runtime panics**
    - What: add panic-free lint tests covering index bounds and RefCell borrow violations.
    - Where: `mir/src/lints.rs`, `mir/tests/*`.
    - Tests: `panic_free` mode should reject `index_*` usage without bounds proof/capability.

---

## Go/No-Go Checklist for Stdlib Expansion
- **No-Go until:** copy validation, borrow/index effect gating, inductive axiom dependency tracking, Prop constructor type-safety.
- **Go when:** all above fixed + defeq fuel diagnostics + polymorphic recursors working + tests for all repros.

---

## Suggested GitHub Issues (Title — Labels)
1) “Validate `copy` inductives structurally or mark `copy` as unsafe” — labels: bug, soundness
2) “Move borrow/index primitives out of axiom/total fragment” — labels: soundness, design
3) “Track axiom dependencies through inductives (classical laundering)” — labels: bug, soundness
4) “Prop inductive constructors skip type-safety checks” — labels: bug, soundness
5) “Elaborator emits incomplete recursor universe levels” — labels: bug, design
6) “Reserved primitive names should be enforced at kernel/driver level” — labels: design, bug
7) “Defeq fuel exhaustion should surface explicit diagnostics” — labels: bug, test
8) “Add panic-free lint coverage for indexing and borrow axioms” — labels: test, design

