# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-03 Round 2

## Executive summary
- **Major fixes landed:** termination now rejects bare self-reference and let‑alias recursion (new `BareRecursiveReference` path in `kernel/src/checker.rs`), closing the prior totality hole; borrow primitives are now total (safe `&`/`&mut`), and FnMut + macro‑boundary warnings are implemented.
- **High risk remains:** kernel still special‑cases `Ref`/`Shared`/`Mut` by *string name* without reserving them, so a non‑prelude environment can spoof these names and trick Copy/borrow semantics.
- **High risk:** MIR lowering for `FnMut` captures stores `&mut` in closure env but marks it `is_copy = true`, and `call_operand_for_func` always `Copy`s Fn/FnMut closures. This enables duplicate mutable references in MIR, contradicting the “unique ref is linear” contract.
- **TCB expansion:** interior‑mutability markers that gate Copy derivation are resolved in the frontend (name‑based) and trusted by the kernel. A malicious frontend can omit markers and get Copy for interior‑mutable types.
- **Go/No‑Go:** **No‑Go** for stdlib expansion until `Ref/Shared/Mut` are reserved/validated and FnMut capture aliasing is fixed.

## Contract violations
1. **Unique reference linearity is violated by FnMut capture lowering.**
   - Contract: `&'ρ mut A` is a linear capability that “cannot be aliased” (`docs/spec/ownership_model.md` L25–30).
   - Implementation: FnMut capture of non‑Copy values lowers to `&mut` and marks the capture as Copy (`mir/src/lower.rs` L356–378). Calls to FnMut use `Operand::Copy` regardless of local `is_copy` (`mir/src/lower.rs` L575–579). This allows duplicated `&mut` in MIR without borrow‑checker visibility.

2. **Reference semantics are enforced by name without reservation.**
   - Contract: reserved primitives are explicitly listed; the kernel enforces ownership/linearity (`docs/spec/kernel_boundary.md` L15–20). The only reserved primitive names are `borrow_*` and `index_*` (`kernel/src/ast.rs` L88–96).
   - Implementation: `is_copy_type_inner` and `is_mut_ref_type` special‑case `Ref/Shared/Mut` by name (`kernel/src/checker.rs` L2936–2941, L3234–3235). These names are **not reserved**, so a non‑prelude environment can redefine them and still receive Copy/borrow semantics.

## Soundness / TCB risks
- **Marker trust boundary (Copy derivation).** The kernel blocks Copy derivation only when `TypeMarker::InteriorMutable` is present (`kernel/src/checker.rs` L4364–4367), but marker resolution happens in the frontend via name lookups (`frontend/src/elaborator.rs` L170–202). A malicious frontend can omit markers to bypass Copy safety, expanding the TCB beyond the kernel.
- **String‑based primitive detection.** Ownership semantics depend on the literal names `Ref`, `Shared`, `Mut` (`kernel/src/checker.rs` L2936–2941, L3234–3235). This is fragile and permits spoofing when prelude is absent or definitions are user‑supplied.
- **FnMut capture aliasing in MIR.** The MIR lowering path treats `&mut` captures as Copy and copies FnMut closures on call (`mir/src/lower.rs` L356–378, L575–579). Borrow checking does not track aliasing created by copying references, so mutable aliasing may pass.

## Semantic gaps (severity)
- **[High] Reserved‑primitive gap:** `Ref`/`Shared`/`Mut` are not reserved, yet are treated as semantic primitives by name. This lets user‑defined types silently inherit Copy/borrow semantics.
- **[High] FnMut capture aliasing:** `&mut` capture locals are marked Copy, undermining the “unique reference is linear” guarantee.
- **[Medium] Marker validation lives outside the kernel:** marker resolution is name‑based and unverified by the kernel; Copy derivation trusts it.
- **[Low] Documentation drift:** kernel boundary doc still references only Fn/FnOnce (no FnMut) (`docs/spec/kernel_boundary.md` L19–21), but FnMut is implemented.

## Minimal reproducible examples
1. **Ref spoofing (core AST / LRL):** non‑reserved `Ref` gets Copy semantics by name.
```lisp
;; No prelude; user defines Ref/Shared.
(axiom Shared (sort 1))
(axiom Mut (sort 1))
(opaque def Ref (pi k (sort 1) (pi A (sort 1) (sort 1)))
  (lam k (sort 1) (lam A (sort 1) A)))

;; Kernel treats Ref Shared A as Copy by name (even though Ref is just A).
(def dup_ref (pi A (sort 1) (pi x (Ref Shared A) (Pair (Ref Shared A) (Ref Shared A))))
  (lam A (sort 1)
    (lam x (Ref Shared A)
      (pair x x))))
```
Expected: duplication should be rejected for non‑Copy `A`. Actual: kernel accepts because `Ref Shared _` is hard‑coded as Copy.

2. **FnMut capture aliasing (MIR‑level):** `&mut` capture marked Copy.
```text
Lowering path:
- collect_captures (FnMut, non‑Copy capture) emits:
  Rvalue::Ref(BorrowKind::Mut, Place::from(local))
  plan.is_copy = true
  plan.operands.push(Operand::Copy(ref_local))
- call_operand_for_func uses Operand::Copy for FnMut.
```
This permits multiple handles to the same `&mut` without borrow‑checker visibility.

3. **Marker omission (kernel API):** Copy derivation trusts frontend markers.
```text
InductiveDecl { name: "RefCell", markers: vec![], is_copy: true, ... }
=> kernel derive_copy_instance() allows Copy (no InteriorMutable marker)
```
A malicious frontend can omit markers to bypass interior‑mutability restrictions.

## Fix plan (prioritized)
1. **Reserve `Ref`/`Shared`/`Mut` as primitives** and reject redefinitions outside the prelude.
   - Files: `kernel/src/ast.rs`, `cli/src/driver.rs`, `kernel/src/checker.rs`.
2. **Validate signatures for `Ref`/`Shared`/`Mut`** in the kernel (similar to `borrow_*` signature checks).
   - Files: `kernel/src/checker.rs`.
3. **Replace string‑based Ref detection with DefId‑based validation** (use env‑registered primitive IDs; fail if missing).
   - Files: `kernel/src/checker.rs`, `mir/src/lower.rs`, `frontend/src/elaborator.rs`.
4. **Fix FnMut capture lowering:** do **not** mark `&mut` capture locals as Copy; treat them as non‑Copy.
   - Files: `mir/src/lower.rs` L356–378.
5. **Adjust Fn/FnMut call semantics** to borrow closures without `Operand::Copy` on non‑Copy locals (new operand form or explicit borrow).
   - Files: `mir/src/lower.rs` L575–579, MIR representation.
6. **Add MIR tests**: FnMut closure capturing non‑Copy value must not permit aliasing of `&mut` (new borrow‑ck corpus case).
   - Files: `mir/tests/borrowck_corpus.rs`.
7. **Add kernel tests** for `Ref`/`Shared`/`Mut` spoofing: redefinition should be rejected.
   - Files: `kernel/tests/negative_tests.rs`.
8. **Kernel‑side marker validation:** ensure marker names exist and are prelude‑defined; optionally enforce their definitions as axioms.
   - Files: `kernel/src/checker.rs`, `frontend/src/elaborator.rs`.
9. **Document the new primitive reservation** in `docs/spec/kernel_boundary.md` and `docs/spec/ownership_model.md`.
10. **Update kernel boundary doc** to include FnMut in the trusted function‑kind rules.
11. **Add diagnostics for marker misuse** (conflicting markers, missing prelude markers).
12. **Add a regression test** ensuring `borrow_shared`/`borrow_mut` remain total and safe in Total defs.

## Go / No‑Go checklist (stdlib expansion)
- [ ] `Ref`/`Shared`/`Mut` are reserved and validated in kernel + CLI.
- [ ] FnMut capture lowering no longer marks `&mut` as Copy.
- [ ] MIR borrow checker has explicit regression tests for FnMut capture aliasing.
- [ ] Kernel validates interior‑mutable markers (or moves marker resolution into kernel).
- [ ] Docs updated for FnMut and reserved ref primitives.

## Suggested GitHub issues (titles + labels)
- **“Reserve Ref/Shared/Mut and validate signatures in kernel”** — labels: bug, soundness, kernel.
- **“FnMut capture lowering marks &mut as Copy (mutable aliasing risk)”** — labels: bug, soundness, mir.
- **“Marker resolution is frontend‑trusted; kernel should validate interior_mutable”** — labels: design, soundness, kernel.
- **“Update kernel boundary docs for FnMut + primitive reservations”** — labels: docs.

