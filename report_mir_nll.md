# Progress Report: Typed MIR & NLL (Borrow Architect)

**Date**: 2026-02-01
**Role**: Borrow Architect

## Summary
Successfully migrated the MIR to use a dedicated Type System (`MirType`) and laid the groundwork for NLL (Non-Lexical Lifetimes) Borrow Checking.

## Phase 2: Typed MIR (Completed)

### 1. MIR Data Model
- **`MirType`**: Implemented in `mir/src/types.rs`. Decoupled from `Term`.
- **`LocalDecl` & `Constant`**: Updated to use `MirType`.
- **Lowering**: Implemented `lower_type` (`Term` -> `MirType`) in `mir/src/lower.rs`.

### 2. Analysis & Transforms Update
- Refactored `borrow.rs` (semi-lexical checker), `ownership.rs` (linear types), `dce.rs`, `inline.rs`, `erasure.rs` to work with `MirType`.
- Verified 19 existing tests passed.

## Phase 3: NLL Borrow Checker (In Progress)

### 1. Liveness Analysis (Completed)
- Implemented `mir/src/analysis/liveness.rs`: Standard backward dataflow analysis to compute live variables at each block entry/exit.
- Required for accurate region inference.

### 2. NLL Scaffolding (Completed)
- Created `mir/src/analysis/nll.rs`.
- Defined `RegionInferenceContext`, `Constraint` (Outlives), and `Location`.
- Implemented `renumber_regions`: Instantiates MIR types with fresh Region Variables for inference.
- Added unit test `test_renumber` (Passed).

## Next Steps (Phase 3 Continued)
1.  **Constraint Generation**: Implement `ConstraintGenerator` to walk the MIR body and emit:
    - Subtyping constraints (`'a: 'b`).
    - Liveness constraints (`Region(x) @ P`).
2.  **Solver**: Implement Region Inference Solver (transitive closure / propagation).
3.  **Error Reporting**: Translate constraint violations into diagnostics.
