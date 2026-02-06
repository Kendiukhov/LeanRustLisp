# Parallel Streams — Mode A Fix Plan (2026-02-03 Round 2)

Goal: Split the latest Mode A fix plan into parallel, non‑overlapping streams. Each stream lists **inter‑stream** dependencies (if any) and target files.

## Stream A — Primitive Reservation & Signature Validation
**Scope:** Reserve `Ref`/`Shared`/`Mut` and validate their kernel signatures; prevent spoofing.
- Task A1: Add `Ref`, `Shared`, `Mut` to reserved primitive names list.
- Task A2: Enforce kernel signature checks for `Ref`/`Shared`/`Mut` (similar to `borrow_*`).
- Task A3: Update CLI diagnostics for reserved primitive misuse.
- Task A4: Add kernel negative tests for spoofing `Ref`/`Shared`/`Mut`.

**Inter‑stream dependencies:**
- Stream D depends on Stream A (docs must reflect the final reserved primitive policy and signatures).

**Primary files/folders:**
- `kernel/src/ast.rs`
- `kernel/src/checker.rs`
- `cli/src/driver.rs`
- `kernel/tests/negative_tests.rs`

## Stream B — FnMut Capture Soundness in MIR
**Scope:** Remove mutable‑aliasing hazards from FnMut captures; adjust call semantics.
- Task B1: Stop marking `&mut` capture locals as Copy in `collect_captures`.
- Task B2: Rework `call_operand_for_func` to avoid `Operand::Copy` for Fn/FnMut closures when non‑Copy (introduce borrow operand or use local `is_copy` instead of kind).
- Task B3: Add MIR borrow‑check regression tests for FnMut capture aliasing.

**Inter‑stream dependencies:**
- None.

**Primary files/folders:**
- `mir/src/lower.rs`
- `mir/src/analysis/borrow.rs`
- `mir/tests/borrowck_corpus.rs`

## Stream C — Kernel Marker Validation (Interior Mutability)
**Scope:** Reduce TCB by validating marker definitions in the kernel.
- Task C1: Verify marker defs (e.g., `interior_mutable`) exist and are prelude‑defined/axioms before accepting Copy derivations.
- Task C2: Add kernel tests for missing/forged markers.

**Inter‑stream dependencies:**
- None.

**Primary files/folders:**
- `kernel/src/checker.rs`
- `kernel/tests/negative_tests.rs`

## Stream D — Documentation Updates
**Scope:** Align specs/docs with new primitives and FnMut semantics.
- Task D1: Update `docs/spec/kernel_boundary.md` to include FnMut in kernel checks.
- Task D2: Update `docs/spec/ownership_model.md` with reserved primitive policy for Ref/Shared/Mut.

**Inter‑stream dependencies:**
- Depends on Stream A (final primitive list + validation rules).

**Primary files/folders:**
- `docs/spec/kernel_boundary.md`
- `docs/spec/ownership_model.md`

