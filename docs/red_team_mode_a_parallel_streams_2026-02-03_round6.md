# Red Team Mode A Parallel Streams — 2026-02-03 Round 6

Context: Tasks derived from `red_team_mode_a_report_2026-02-03_round6.md` (lifetime parameterization in MIR + per‑capture modes).

## Stream A — MIR lifetime parameters (core type system)
**Goal:** Make `MirType::Fn` capable of expressing shared lifetimes across args/returns.

**Tasks**
1. Extend `MirType::Fn` with region parameters (or a binder list) to represent shared lifetimes.
2. Update `lower_type` to introduce/track region parameters instead of generating fresh regions for every `Ref` occurrence.
3. Update MIR pretty/printing and snapshots to include region parameters.

**Primary files/folders**
- `mir/src/types.rs`
- `mir/src/lower.rs`
- `mir/src/pretty.rs`
- `mir/src/snapshots.rs`
- `docs/spec/mir/typing.md`

**Dependencies**
- None.

## Stream B — NLL call‑site region instantiation
**Goal:** Instantiate and constrain region parameters at call sites.

**Tasks**
1. Extend NLL type relation logic to substitute/instantiate callee region params with caller regions.
2. Update `relate_call_types` to apply region substitutions before relating args/ret.
3. Add NLL unit tests for function calls with linked lifetimes.

**Primary files/folders**
- `mir/src/analysis/nll.rs`
- `mir/tests/borrowck_corpus.rs`

**Dependencies**
- Depends on Stream A (needs region parameters in `MirType::Fn`).

## Stream C — MIR typing verifier for calls
**Goal:** Introduce a MIR‑level type checker to reject ill‑typed calls early.

**Tasks**
1. Add a MIR typing pass that validates `Terminator::Call` arguments against callee type (including region params).
2. Integrate pass into the CLI pipeline before NLL.
3. Add tests that invalid calls are rejected with clear errors.

**Primary files/folders**
- `mir/src/analysis` (new module or extend existing)
- `cli/src/compiler.rs`
- `cli/tests/pipeline_negative.rs`

**Dependencies**
- Depends on Stream A (needs region params in type representation).
- Optionally depends on Stream B if the verifier reuses instantiation logic.

## Stream D — Per‑capture mode plumbing (frontend → kernel → MIR)
**Goal:** Preserve capture modes so `FnMut` does not force all captures to `&mut`.

**Tasks**
1. Compute per‑capture mode (shared/mut/move) in elaboration and attach it to closures.
2. Validate and store capture mode metadata in the kernel (or a side‑table keyed by DefId).
3. Update MIR lowering to borrow/move each capture based on its mode (not just closure kind).

**Primary files/folders**
- `frontend/src/elaborator.rs`
- `kernel/src/checker.rs`
- `mir/src/lower.rs`

**Dependencies**
- None (can proceed in parallel with Streams A–C).

## Stream E — Tests & docs alignment
**Goal:** Lock in behavior with tests and spec updates.

**Tasks**
1. Add pipeline tests for safe `id_ref` use and negative borrow‑escape through call.
2. Add tests for mixed‑capture `FnMut` closures (shared + mut captures).
3. Update MIR spec docs for lifetime parameters and call instantiation.

**Primary files/folders**
- `cli/tests/pipeline_golden.rs`
- `cli/tests/pipeline_negative.rs`
- `mir/tests/borrowck_corpus.rs`
- `docs/spec/mir/typing.md`
- `docs/spec/mir/nll-constraints.md`

**Dependencies**
- Depends on Streams A and B for lifetime‑param behavior.
- Depends on Stream D for mixed‑capture tests.
