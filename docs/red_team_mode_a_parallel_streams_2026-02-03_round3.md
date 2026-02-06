# Red Team Mode A Parallel Streams — 2026-02-03 Round 3

Context: Tasks derived from `red_team_mode_a_report_2026-02-03_round3.md` (Fn/FnMut call semantics in MIR).

## Stream A — MIR call representation & lowering (core semantics)
**Goal:** Introduce borrow-based call operand for Fn/FnMut and update lowering accordingly.

**Tasks**
1. Define MIR call representation for borrowed function operands (shared for Fn, mutable for FnMut).
2. Update `call_operand_for_func` to emit borrow-call operands for Fn/FnMut.
3. Adjust capture lowering if needed so Fn/FnMut closures can be reused without copying env values.

**Primary files/folders**
- `mir/src/lower.rs`
- `mir/src/pretty.rs`
- `mir/src/codegen.rs`
- `docs/spec/function_kinds.md` (reference only)

**Dependencies**
- None.

## Stream B — Ownership & borrow analysis updates
**Goal:** Teach ownership/NLL borrowck to respect borrow-call semantics for Fn/FnMut.

**Tasks**
1. Update ownership analysis to treat borrow-call operands as non-consuming.
2. Update borrow checker to model FnMut call borrows (mut loan on closure environment).

**Primary files/folders**
- `mir/src/analysis/ownership.rs`
- `mir/src/analysis/borrow.rs`
- `mir/src/analysis/nll.rs`

**Dependencies**
- Depends on Stream A (needs the new call operand representation).

## Stream C — Tests & pipeline verification
**Goal:** Lock in the new semantics with tests across MIR and CLI pipeline.

**Tasks**
1. Update MIR call operand unit tests (remove Move expectations for Fn/FnMut; expect borrow).
2. Add borrow-ck corpus tests for repeated Fn/FnMut calls.
3. Add CLI golden tests (programs with repeated Fn/FnMut calls).
4. Add kernel semantic test to assert multiple Fn/FnMut calls type-check and survive pipeline.

**Primary files/folders**
- `mir/src/lower.rs` (unit tests)
- `mir/tests/borrowck_corpus.rs`
- `cli/tests/pipeline_golden.rs`
- `kernel/tests/semantic_tests.rs`
- `tests/` (new LRL fixtures if needed)

**Dependencies**
- Depends on Streams A and B (tests should match the new lowering + analysis behavior).

## Stream D — Spec/docs alignment
**Goal:** Sync documentation with updated semantics and FnMut coverage.

**Tasks**
1. Update kernel boundary docs to include FnMut and borrow-call semantics.
2. Update MIR typing/docs to describe borrow-call operands.

**Primary files/folders**
- `docs/spec/kernel_boundary.md`
- `docs/spec/mir/typing.md`

**Dependencies**
- Optional dependency on Stream A for exact call representation details.
