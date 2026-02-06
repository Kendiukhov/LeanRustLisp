# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-03 Round 4

## Executive summary
- **Fn/FnMut call semantics now borrow in MIR** (good progress): `call_operand_for_func` uses `CallOperand::Borrow` for `Fn`/`FnMut`, aligning with the spec’s call semantics. (`mir/src/lower.rs` L575–586)
- **Critical: closure capture extraction copies non‑Copy values** when unpacking env fields, even if the capture is non‑Copy (`FnOnce`/`FnMut` with `&mut`), violating ownership/aliasing rules. (`mir/src/lower.rs` L989–1008)
- **Borrow regions across function calls are unconstrained**: MIR regions are assigned fresh per `Ref` type occurrence and NLL only relates regions on assignments, not on calls. This makes returned references from functions insufficiently tied to inputs/closure env. (`mir/src/lower.rs` L162–169; `mir/src/analysis/nll.rs` L560–584)
- **Spec mismatch: implicit binders are supposed to be observational‑only, but elaborator treats implicit non‑Copy args as consuming** (upgrades closure kind instead of error). (`docs/spec/function_kinds.md` L111–125; `frontend/src/elaborator.rs` L634–644)
- **Macro boundary warnings are non‑blocking**: macros can expand to `unsafe` or `axiom classical` with warnings only, leaving a large “macro trust” surface. (`frontend/src/macro_expander.rs` L390–412)

## Contract violations
1. **Non‑Copy captures are copied out of closure env (linear/affine violation).**
   - Evidence: captured env fields are always extracted with `Operand::Copy`, regardless of `capture_plan.is_copy[i]`. (`mir/src/lower.rs` L989–1008)
   - Impact: duplicates non‑Copy values (including `&mut`) and undermines Rust‑grade resource discipline.

2. **Borrow lifetimes are not related across call boundaries.**
   - Evidence: each `Ref` type occurrence gets a fresh region in lowering (`mir/src/lower.rs` L162–169), and NLL only adds constraints on `Assign`/`Ref` (no `Call` constraints). (`mir/src/analysis/nll.rs` L560–584)
   - Impact: a function returning a reference can “launder” lifetimes because caller/callee regions are unrelated.

3. **Implicit binders observational‑only rule is not enforced in elaboration.**
   - Spec requires implicit value binders to reject consuming/mut‑borrow use. (`docs/spec/function_kinds.md` L111–125)
   - Implementation treats implicit non‑Copy args as consuming to infer `FnOnce`. (`frontend/src/elaborator.rs` L634–644)

## Soundness / TCB risks
- **MIR lowering is in the TCB for ownership**: `Operand::Copy` on non‑Copy captures is a single‑point unsoundness. A MIR type/ownership verifier should reject Copy on non‑Copy locals. (`mir/src/lower.rs` L989–1008)
- **NLL assumes correct region identity across calls**: without call‑site constraints or region unification, borrow safety across function boundaries is not enforced. (`mir/src/lower.rs` L162–169; `mir/src/analysis/nll.rs` L560–584)
- **Macro expansion can introduce unsafe/classical forms with only warnings**: the macro system is outside the kernel and can expand to axioms/unsafe constructs. This keeps a large implicit trust surface. (`frontend/src/macro_expander.rs` L390–412)

## Semantic gaps (severity)
- **[High] Function call lifetime constraints missing.** Calls do not relate argument/return regions; returning references from functions is under‑constrained. (`mir/src/analysis/nll.rs` L560–584)
- **[High] Non‑Copy capture extraction uses `Copy`.** This violates the ownership model and can duplicate `&mut` or moved values. (`mir/src/lower.rs` L989–1008)
- **[Medium] Implicit binder observational‑only rule not enforced in elaborator.** Leads to spec mismatch and confusing kernel‑side failures. (`docs/spec/function_kinds.md` L111–125; `frontend/src/elaborator.rs` L634–644)
- **[Low] `import classical` installs a dummy `classical_choice : Prop`.** Tracking works, but it does not supply a real classical axiom (design gap). (`cli/src/driver.rs` L1225–1233)

## Minimal reproducible examples
1. **Borrow escape through function boundary (should be rejected).**
```lisp
(def id_ref (pi r (Ref Shared Nat) (Ref Shared Nat))
  (lam r (Ref Shared Nat) r))

(def bad_escape (pi x Nat (Ref Shared Nat))
  (lam x Nat
    (let r (Ref Shared Nat) (& x)
      (id_ref r))))
```
Expected: reject (returned reference escapes `x`). Current NLL lacks call constraints to relate the callee’s return region to the caller’s input region.

2. **Implicit non‑Copy binder consumed (spec says error).**
```lisp
(inductive Box (pi A Type Type)
  (ctor box (pi x A (Box A))))

(def implicit_move
  (pi {b (Box Nat)} (Box Nat))
  (lam {b} (Box Nat) b))
```
Expected: error (implicit non‑Copy consumed). Current elaboration infers consuming use instead of rejecting.

3. **MIR capture extraction copies non‑Copy.**
MIR lowering emits:
```
_#cap = Copy(_env.field0)
```
for all captures (even non‑Copy). (`mir/src/lower.rs` L989–1008)
This duplicates non‑Copy captures, violating linearity.

## Fix plan (prioritized)
1. **Use `Move` for non‑Copy capture extraction.**
   - **What:** In closure env unpack, use `Operand::Move` when `capture_plan.is_copy[i] == false`.
   - **Where:** `mir/src/lower.rs` (capture unpack loop).
   - **Why:** Prevent duplication of non‑Copy values.
   - **Tests:** MIR ownership test that non‑Copy captures are moved (not copied).

2. **Add MIR verifier for `Operand::Copy` on non‑Copy locals.**
   - **Where:** New pass in `mir/src/analysis` (or extend `ownership::check`).
   - **Why:** Catch lowering bugs early; shrink TCB.
   - **Tests:** Unit test that `Copy` of non‑Copy local is rejected.

3. **Introduce call‑site region constraints.**
   - **What:** On `Terminator::Call`, relate caller arg types to callee param types and relate callee return to destination.
   - **Where:** `mir/src/analysis/nll.rs` (constraint generation).
   - **Why:** Prevent reference‑lifetime laundering across calls.
   - **Tests:** Borrow‑escape negative test (`bad_escape`) should fail.

4. **Unify region variables across function types and call sites.**
   - **What:** Establish a mapping between callee regions and caller regions at call boundaries.
   - **Where:** MIR type system + NLL constraint generation.
   - **Why:** Make function types meaningful for lifetimes.

5. **Add MIR typing/compatibility checks for call operands.**
   - **Where:** New pass in `mir/src/analysis`.
   - **Why:** Ensure arg types (incl. regions) match function signature.

6. **Enforce implicit binder observational‑only in elaborator.**
   - **What:** If implicit arg usage requires `MutBorrow`/`Consuming`, emit a dedicated error.
   - **Where:** `frontend/src/elaborator.rs` (function kind inference).
   - **Tests:** Negative test for `implicit_move`.

7. **Align kernel and elaborator diagnostics for implicit binder violations.**
   - **Where:** `kernel/src/ownership.rs` + frontend diagnostics.
   - **Why:** Consistent error surface; avoid late kernel failure surprises.

8. **Add borrow‑region call tests.**
   - **Where:** `mir/tests/borrowck_corpus.rs`, `cli/tests/pipeline_negative.rs`.
   - **What:** Reference identity function + escape case.

9. **Document call‑site region constraints and capture moves.**
   - **Where:** `docs/spec/mir/borrows-regions.md`, `docs/spec/mir/nll-constraints.md`.
   - **Why:** Make the intended semantics explicit.

10. **Macro boundary enforcement decision.**
   - **What:** Optionally require explicit `unsafe`/`classical` opt‑in at macro call sites (upgrade warnings to errors by default or behind a flag).
   - **Where:** `frontend/src/macro_expander.rs`, `cli/src/driver.rs`.
   - **Tests:** Macro boundary warning/deny tests.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Non‑Copy capture extraction uses `Move`, not `Copy`.
- [ ] MIR verifier rejects `Copy` of non‑Copy locals.
- [ ] NLL introduces call‑site region constraints.
- [ ] Borrow‑escape negative tests fail as expected.
- [ ] Implicit binder observational‑only rule enforced at elaboration.
- [ ] Macro boundary policy decided and enforced (warn vs error).

## Suggested GitHub issues (titles + labels)
- **“MIR closure capture extraction uses Copy for non‑Copy values”** — labels: bug, soundness, mir
- **“NLL lacks call‑site region constraints (borrow escape possible)”** — labels: bug, soundness, borrowck
- **“Elaborator allows consuming implicit non‑Copy binders”** — labels: bug, semantics, frontend
- **“Macro boundary warnings not enforced (unsafe/classical laundering risk)”** — labels: design, safety, macros
- **“`import classical` installs placeholder axiom only”** — labels: design, docs
