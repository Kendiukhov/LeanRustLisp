# Red Team Mode A Parallel Streams — 2026-02-03 Round 7

Context: Tasks derived from `red_team_mode_a_report_2026-02-03_round7.md` (lifetime parameters in MIR + per‑capture modes + call typing validation).

## Stream A — MIR lifetime parameters (type system core)
**Goal:** Represent shared lifetimes in function types.

**Tasks**
1. Extend `MirType::Fn` with region parameters (or a binder list).
2. Update MIR pretty/printing and snapshots to include region parameters.
3. Update spec docs to describe the new function type form.

**Primary files/folders**
- `mir/src/types.rs`
- `mir/src/pretty.rs`
- `mir/src/snapshots.rs`
- `docs/spec/mir/typing.md`

**Dependencies**
- None.

## Stream B — Lowering of lifetime‑param function types
**Goal:** Preserve shared regions across `Ref` occurrences in function types.

**Tasks**
1. Update `lower_type` to reuse region parameters instead of allocating fresh regions for each `Ref`.
2. Introduce a local region‑param environment in lowering (so `&'a T -> &'a T` is representable).

**Primary files/folders**
- `mir/src/lower.rs`

**Dependencies**
- Depends on Stream A (needs new `MirType::Fn` shape).

## Stream C — NLL call‑site region instantiation
**Goal:** Apply region parameters at call sites and enforce lifetime relations.

**Tasks**
1. Add region‑param instantiation in `relate_call_types`.
2. Ensure call‑site constraints are applied before solving.
3. Update NLL tests for call‑return lifetime linking.

**Primary files/folders**
- `mir/src/analysis/nll.rs`
- `mir/tests/borrowck_corpus.rs`

**Dependencies**
- Depends on Streams A and B.

## Stream D — MIR call typing/validation pass
**Goal:** Validate call operand kinds and arg types before borrow checking.

**Tasks**
1. Add a MIR typing pass that checks `CallOperand` vs `FnKind` (shared/mut/move).
2. Validate arg types (incl. region params) against callee signature.
3. Integrate pass into CLI pipeline before NLL.

**Primary files/folders**
- `mir/src/analysis` (new module)
- `cli/src/compiler.rs`

**Dependencies**
- Depends on Streams A and C (needs region params + instantiation model).

## Stream E — Per‑capture mode plumbing (frontend → kernel → MIR)
**Goal:** Preserve capture modes so `FnMut` doesn’t force all captures to `&mut`.

**Tasks**
1. Compute per‑capture modes in elaboration and store metadata.
2. Validate/record capture modes in kernel (side‑table keyed by DefId is fine).
3. Update MIR lowering to borrow/move each capture based on its mode.

**Primary files/folders**
- `frontend/src/elaborator.rs`
- `kernel/src/checker.rs`
- `mir/src/lower.rs`

**Dependencies**
- None.

## Stream F — Tests & docs alignment
**Goal:** Lock in behavior with pipeline tests and doc updates.

**Tasks**
1. Add pipeline negative test for borrow‑escape through call using LRL lowering.
2. Add golden tests for safe `id_ref` usage with shared lifetimes.
3. Add mixed‑capture `FnMut` tests (shared + mut capture modes).
4. Update MIR spec docs for lifetime params + call instantiation + per‑capture modes.

**Primary files/folders**
- `cli/tests/pipeline_negative.rs`
- `cli/tests/pipeline_golden.rs`
- `mir/tests/borrowck_corpus.rs`
- `docs/spec/mir/typing.md`
- `docs/spec/mir/nll-constraints.md`

**Dependencies**
- Depends on Streams A–C for lifetime‑param behavior.
- Depends on Stream E for mixed‑capture tests.
