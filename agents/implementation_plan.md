# Phase 5: Effects, Partial, and Unsafe

## Goal Description
Implement a robust Effect System and strict separation boundaries between Total, Partial, and Unsafe computations.
This ensures that:
1.  **Total** code (pure logic) cannot call Partial or Unsafe code, preserving logical soundness.
2.  **Partial** code (general recursion, IO) is isolated but interoperable via explicit types (e.g., `Comp`).
3.  **Unsafe** code (FFI, raw pointers) is strictly gated.

## User Review Required
> [!IMPORTANT]
> **Effect Boundary Rules**:
> * `def` (Total) can call ONLY `Total`.
> * `partial def` (Partial) can call `Total` and `Partial`.
> * `unsafe def` (Unsafe) can call `Total`, `Partial`, and `Unsafe`.
>
> We will verify this by traversing the body of definitions.

> [!NOTE]
> **Comp Type**:
> We will introduce a `Comp A` type (Computation) to represent effectful values.
> This allows Total functions to *manipulate* effectful programs (as values) without *running* them.
> e.g. `def plan : Comp Nat := return 42` is Total (it returns a description of a computation).

## Proposed Changes

### Kernel
#### [MODIFY] [checker.rs](mir/src/checker.rs)
- Implement `check_effects(term, allowed_totality)`.
- In `check_decl` (or `add_definition`), run `check_effects` on the body.
- Verify that called constants satisfy the totality constraints.

#### [NEW] [kernel/src/effects.rs] (Optional)
- Logic for effect checking if it grows large.

### Prelude
#### [MODIFY] [prelude.lrl](tests/prelude.lrl)
- Add `(inductive Comp (A) ...)` or similar primitive definition if needed.
- Or intrinsic support.

## Verification Plan

### Automated Tests
- `test_total_calls_partial_error`: Verify `def` cannot call `partial def`.
- `test_safe_calls_unsafe_error`: Verify `def` cannot call `unsafe def`.
- `test_partial_calls_total_ok`: Verify `partial def` can call `def`.
- `test_comp_wrapper`: Verify `def` can return `Comp A`.
