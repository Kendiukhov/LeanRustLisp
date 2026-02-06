# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-03 Round 6

## Executive summary
- **Call‑site constraints added** in NLL: function calls now relate argument/return types to the callee type. (`mir/src/analysis/nll.rs` L588–596, L1016–1025)
- **Capture extraction bug fixed:** non‑Copy captures are now moved (not copied) when unpacking closure env. (`mir/src/lower.rs` L1083–1091)
- **Implicit non‑Copy binders are now enforced** at elaboration (spec alignment). (`frontend/src/elaborator.rs` L550–579)
- **Remaining blocker:** MIR does not encode lifetime relationships in function types — each `Ref` occurrence gets a fresh region, so `&'a T -> &'a T` cannot be represented. (`mir/src/lower.rs` L162–169; `mir/src/analysis/nll.rs` L1016–1025; `mir/tests/borrowck_corpus.rs` L1254–1260)
- **Capture‑mode precision gap:** `FnMut` capture lowering mut‑borrows *all* non‑Copy captures, even when a capture is read‑only. (`mir/src/lower.rs` L437–456)

## Contract violations
1. **Function types cannot express lifetime relationships.**
   - `lower_type` assigns a fresh region to every `Ref` occurrence, including both param and return of a single function type. (`mir/src/lower.rs` L162–169)
   - NLL call constraints rely on shared region IDs to relate args and returns. (`mir/src/analysis/nll.rs` L1016–1025)
   - The borrowck corpus models call‑return safety by *manually* using the same region for param/ret. (`mir/tests/borrowck_corpus.rs` L1254–1260)
   - Impact: the MIR type system cannot encode the intended `&'a T -> &'a T` contract, so call‑site safety is under‑constrained (or over‑constrained) depending on region allocation.

2. **`FnMut` capture lowering loses per‑capture modes.**
   - All non‑Copy captures in a `FnMut` closure are lowered as `&mut` borrows, regardless of whether they are only read. (`mir/src/lower.rs` L437–456)
   - Spec requires per‑capture mode (shared vs mut vs move); the current lowering only uses the *overall* closure kind, not per‑capture info.

## Soundness / TCB risks
- **Borrow safety across calls depends on lifetime encoding in `MirType`.** The NLL constraints are only as strong as the regions in function types. Without lifetime parameterization, the compiler cannot enforce that returned references are tied to input lifetimes. (`mir/src/lower.rs` L162–169; `mir/src/analysis/nll.rs` L1016–1025)
- **Lowering is still in the TCB for capture semantics.** The compiler infers the minimal closure kind, but does not preserve per‑capture modes into MIR. This can reject correct programs (and hides capture‑mode bugs behind a coarse Fn/FnMut/FnOnce switch). (`mir/src/lower.rs` L437–456)

## Semantic gaps (severity)
- **[High] Lifetime parameters are missing in MIR function types.** There is no way to represent “same lifetime” across input/output references, which is fundamental to Rust‑grade borrowing.
- **[Medium] Per‑capture borrow modes are lost at lowering.** `FnMut` mut‑borrows all non‑Copy captures, even read‑only ones, which is more restrictive than the spec.

## Minimal reproducible examples
1. **Call‑return lifetime relationship is unrepresentable.**
```lisp
(def id_ref (pi r (Ref Shared Nat) (Ref Shared Nat))
  (lam r (Ref Shared Nat) r))

(def bad_escape (pi x Nat (Ref Shared Nat))
  (lam x Nat
    (let r (Ref Shared Nat) (& x)
      (id_ref r))))
```
Expected: reject (returned reference should not outlive `x`). This relies on the MIR type representing the *same* region for both param and return; current lowering assigns fresh regions per `Ref`, so the constraint cannot be encoded.

2. **`FnMut` closure with mixed captures becomes over‑strict.**
```lisp
(def both (pi x Nat (pi y Nat (pi #[mut] _ Nat Nat)))
  (lam x Nat
    (lam y Nat
      ;; mutates x, reads y
      (lam #[mut] _ Nat (add x y)))))
```
Expected: `x` captured mutably, `y` captured shared. Current lowering mut‑borrows all non‑Copy captures for `FnMut`, so `y` is unnecessarily `&mut`, increasing conflicts.

## Fix plan (prioritized)
1. **Add lifetime parameters to `MirType::Fn`.**
   - **What:** Extend `MirType::Fn` with a region‑param list or region variables bound at the function type level.
   - **Where:** `mir/src/types.rs`, `mir/src/lower.rs`, `mir/src/analysis/nll.rs`.
   - **Why:** Encode `&'a T -> &'a T` relationships explicitly.
   - **Tests:** MIR unit tests for identity functions over refs with shared regions.
2. **Lower function types with shared region IDs when appropriate.**
   - **What:** Reuse region variables across repeated `Ref` occurrences in a function type (or bind them as parameters).
   - **Where:** `mir/src/lower.rs` (`lower_type`).
3. **Unify/instantiate region parameters at call sites.**
   - **What:** At `Terminator::Call`, instantiate callee region parameters and relate them to caller arg/ret types.
   - **Where:** `mir/src/analysis/nll.rs` (`relate_call_types`).
4. **Add a MIR type‑checking pass for calls.**
   - **What:** Validate argument types (including region params) against callee signature before NLL.
   - **Where:** `mir/src/analysis` (new pass).
5. **Add pipeline tests for lifetime‑linked calls.**
   - **What:** Positive test for safe `id_ref` usage and negative test for escape through call.
   - **Where:** `cli/tests/pipeline_golden.rs`, `cli/tests/pipeline_negative.rs`.
6. **Carry per‑capture modes from elaboration to MIR.**
   - **What:** Compute capture‑mode info per variable and store it in the core term or side‑table; pass to lowering.
   - **Where:** `frontend/src/elaborator.rs`, `kernel/src/checker.rs`, `mir/src/lower.rs`.
7. **Lower captures using per‑capture mode (shared/mut/move).**
   - **What:** In `collect_captures`, borrow or move each capture based on its mode, not just the closure kind.
   - **Where:** `mir/src/lower.rs`.
8. **Add tests for mixed‑capture FnMut closures.**
   - **What:** Ensure shared captures remain shared even when the closure kind is FnMut.
   - **Where:** `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_golden.rs`.
9. **Document lifetime parameterization in MIR spec.**
   - **Where:** `docs/spec/mir/typing.md`, `docs/spec/mir/nll-constraints.md`.
10. **Add a regression test for region linking in function types.**
   - **Where:** `mir/tests/borrowck_corpus.rs` (LRL‑lowered case, not hand‑written MIR).

## Go / No‑Go checklist (stdlib expansion)
- [ ] MIR function types can express shared lifetimes across args/returns.
- [ ] NLL call constraints instantiate region parameters correctly.
- [ ] Borrow‑escape through call is rejected in LRL‑lowered tests.
- [ ] Per‑capture modes are preserved into MIR (shared vs mut vs move).
- [ ] Mixed‑capture FnMut closures compile without spurious borrow conflicts.

## Suggested GitHub issues (titles + labels)
- **“MIR function types lack lifetime parameters (arg/ret region relation lost)”** — labels: bug, soundness, mir
- **“Lowering uses fresh regions for each Ref occurrence in function types”** — labels: bug, semantics, mir
- **“FnMut capture lowering mut‑borrows all non‑Copy captures”** — labels: bug, semantics, mir
- **“Add region‑param instantiation at call sites (NLL)”** — labels: design, borrowck
