# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-03 Round 7

## Executive summary
- **NLL now relates call‑site types** (good): `relate_call_types` is invoked for `Terminator::Call`, tying args and destination to the callee type. (`mir/src/analysis/nll.rs` L588–596, L1016–1025)
- **Closure capture extraction fixed** for non‑Copy values: env unpack now moves non‑Copy captures. (`mir/src/lower.rs` L1083–1091)
- **Implicit non‑Copy binders are enforced** in elaboration (spec alignment). (`frontend/src/elaborator.rs` L550–579)
- **Blocker remains:** MIR function types cannot express shared lifetimes (`&'a T -> &'a T`) because `lower_type` allocates fresh regions per `Ref` occurrence. This makes call‑site constraints too weak for lifetime safety across calls. (`mir/src/lower.rs` L162–169; `mir/src/analysis/nll.rs` L1016–1025)
- **Capture‑mode precision gap:** `FnMut` capture lowering mut‑borrows *all* non‑Copy captures instead of preserving per‑capture modes. (`mir/src/lower.rs` L437–456)
- **Call‑operand kind is not validated** against `Fn`/`FnMut`/`FnOnce`, so a lowering bug could bypass aliasing rules without detection. (`mir/src/analysis/nll.rs` L1009–1025)

## Contract violations
1. **Function types cannot encode lifetime relationships.**
   - Evidence: `lower_type` creates a fresh region for every `Ref` in a function type. (`mir/src/lower.rs` L162–169)
   - Call constraints rely on shared region IDs to express `arg`–`ret` lifetime links. (`mir/src/analysis/nll.rs` L1016–1025)
   - MIR borrowck tests model `id_ref` by manually reusing a region in the function type, confirming the need for shared regions in the type. (`mir/tests/borrowck_corpus.rs` L1254–1260)
   - Impact: the MIR type system cannot represent `&'a T -> &'a T`; lifetime safety across calls is under‑constrained.

2. **`FnMut` capture lowering loses per‑capture modes.**
   - Evidence: for `FnMut`, all non‑Copy captures become `&mut`, regardless of whether the variable is read‑only. (`mir/src/lower.rs` L437–456)
   - Impact: semantic mismatch with the spec’s per‑capture mode model; causes spurious borrow conflicts and hides mode errors.

## Soundness / TCB risks
- **MIR lifetime encoding is a soundness boundary.** Even with call constraints, the absence of shared regions in function types makes it impossible to express key lifetime relations. This weakens the borrow checker across function boundaries. (`mir/src/lower.rs` L162–169; `mir/src/analysis/nll.rs` L1016–1025)
- **No validation of call‑operand kind vs function kind.** `CallOperand::Borrow` is accepted without checking the callee’s `FnKind`. A mismatch (e.g., shared borrow for `FnMut`) would allow aliasing that should be rejected. (`mir/src/analysis/nll.rs` L1009–1025)

## Semantic gaps (severity)
- **[High] Lifetime parameters missing in `MirType::Fn`.** Cannot represent `&'a T -> &'a T` or relate multiple borrows in a single signature.
- **[Medium] Per‑capture borrow modes not preserved.** `FnMut` collapses all non‑Copy captures into `&mut`, losing shared/consumed distinctions.
- **[Medium] No MIR‑level validation of call‑operand kind.** Lowering bugs could violate aliasing rules without detection.

## Minimal reproducible examples
1. **Borrow escape through call relies on shared lifetime (currently unrepresentable).**
```lisp
(def id_ref (pi r (Ref Shared Nat) (Ref Shared Nat))
  (lam r (Ref Shared Nat) r))

(def bad_escape (pi x Nat (Ref Shared Nat))
  (lam x Nat
    (let r (Ref Shared Nat) (& x)
      (id_ref r))))
```
The intended typing needs `id_ref : &'a Nat -> &'a Nat`. MIR currently assigns fresh regions to each `Ref` occurrence, so the lifetime relationship is not representable.

2. **Mixed captures in `FnMut` become over‑strict.**
```lisp
(def both (pi x Nat (pi y Nat (pi #[mut] _ Nat Nat)))
  (lam x Nat
    (lam y Nat
      ;; x mutated, y read-only
      (lam #[mut] _ Nat (add x y)))))
```
Expected: `x` captured mutably, `y` captured shared. Current lowering mut‑borrows all non‑Copy captures for `FnMut`.

## Fix plan (prioritized)
1. **Add lifetime parameters to `MirType::Fn`.**
   - **Where:** `mir/src/types.rs`.
   - **Why:** Encode shared lifetimes across args/ret.
2. **Lower function types with region parameters instead of fresh regions.**
   - **Where:** `mir/src/lower.rs` (`lower_type`).
3. **Instantiate callee region params at call sites.**
   - **Where:** `mir/src/analysis/nll.rs` (`relate_call_types`).
4. **Add MIR type‑checking pass for calls.**
   - **Where:** new pass in `mir/src/analysis`; invoke from `cli/src/compiler.rs`.
5. **Add tests for lifetime‑linked call behavior.**
   - **Where:** `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_negative.rs`.
6. **Carry per‑capture modes from elaboration to MIR.**
   - **Where:** `frontend/src/elaborator.rs`, `kernel/src/checker.rs`, `mir/src/lower.rs`.
7. **Use per‑capture modes in `collect_captures`.**
   - **Where:** `mir/src/lower.rs`.
8. **Add tests for mixed capture modes (`FnMut`).**
   - **Where:** `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_golden.rs`.
9. **Validate call‑operand kind vs `FnKind`.**
   - **Where:** MIR type checker (or add to NLL `relate_call_types`).
10. **Update MIR spec docs with region parameters and call instantiation.**
    - **Where:** `docs/spec/mir/typing.md`, `docs/spec/mir/nll-constraints.md`.

## Go / No‑Go checklist (stdlib expansion)
- [ ] `MirType::Fn` supports lifetime parameters with shared regions.
- [ ] Call‑site region instantiation is implemented and tested.
- [ ] Borrow‑escape via call is rejected in LRL‑lowered tests.
- [ ] Per‑capture modes are preserved into MIR.
- [ ] Mixed‑capture `FnMut` closures compile without spurious conflicts.
- [ ] Call‑operand kind is validated against function kind.

## Suggested GitHub issues (titles + labels)
- **“MIR function types lack lifetime parameters (arg/ret region relation lost)”** — labels: bug, soundness, mir
- **“Lowering allocates fresh regions per Ref; cannot express `&'a T -> &'a T`”** — labels: bug, semantics, mir
- **“FnMut capture lowering mut‑borrows all non‑Copy captures (missing per‑capture modes)”** — labels: bug, semantics, mir
- **“Add MIR call typing/validation for call‑operand kind vs FnKind”** — labels: bug, soundness, mir
