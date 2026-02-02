# Non-Lexical Lifetimes (NLL) and Constraints in LRL MIR

## Overview

LRL employs a Non-Lexical Lifetime (NLL) system similar to Rust's to ensure memory safety without strict lexical scopes. This system operates on the Control Flow Graph (CFG) of the Mid-level Intermediate Representation (MIR).

## Regions

Every reference type in MIR is annotated with a **Region** variable:
```rust
Ref(Region, Box<MirType>, Mutability)
```
Regions represent the set of points in the CFG where the reference is valid (live).

## Liveness Analysis

The NLL checker performs **Precise Liveness Analysis**:
1.  **Backward Analysis**: Starting from the end of each basic block, it computes the set of live variables *before* each statement.
2.  **Statement Granularity**: Unlike standard block-level analysis, LRL stores liveness sets for every `Location` (block + statement index).
3.  **Region Liveness**: A region `'r` is considered live at location `L` if any variable `v` whose type contains `'r` is live at `L`.

## Constraint Generation

The checker iterates forward through the MIR body to generate constraints based on assignments (subtyping):

### 1. Subtyping (`dest = src`)
If `dest` has type `&'a T` and `src` has type `&'b T`, the assignment implies that the value from `src` (valid for `'b`) flows into `dest` (valid for `'a`).
Therefore, `'b` must outlive `'a`:
```
'b : 'a  (b >= a)
```
This constraint is added to the `RegionInferenceContext`.

### 2. Loan Creation (`dest = &place`)
When a reference is created via `Rvalue::Ref(kind, place)`:
1.  A **Loan** is recorded:
    ```rust
    Loan {
        place: place,
        region: region_of_dest,
        kind: kind,
        issued_at: current_location
    }
    ```
2.  The region of the destination is constrained to be live wherever the reference is used (via liveness analysis).

## Constraint Solving

The solver computes the transitive closure of the `outlives` constraints.
Algorithm:
1.  Initialize `region_values['r]` with the set of locations where `'r` is required to be live (from liveness analysis).
2.  Iterate to fixpoint:
    - If `'b : 'a` (b outlives a), add all locations from `region_values['a]` into `region_values['b]`.
    - This ensures that if `'a` is live at `L`, and `'b` must outlive `'a`, then `'b` is also live at `L`.

## Conflict Detection (Borrow Checking)

After solving, the checker verifies that no active loan is violated by conflicting accesses.

For every statement at `Location L`:
1.  Identify **Active Loans**: A loan `L` is active if its region is live at `L` (`region_values[loan.region].contains(L)`).
2.  Identify **Accesses**:
    - `Assign(dest, ...)` -> Writes to `dest`.
    - `Use(op)` -> Reads from `op`.
3.  Check for **Conflicts**:
    - **Mutation** of a place conflicts with *any* active loan of that place (Shared or Mut).
    - **Reading** a place conflicts with an active *Mutable* loan of that place.

## Interior Mutability

Types wrapped in `InteriorMutable` (like `RefCell`) bypass static borrow checking for the inner content but are subject to:
-   **Panic-Free Lints**: Verified by `PanicFreeLinter` to ensure safety in restricted profiles.
-   **Runtime Checks**: Codegen inserts runtime guards.

The NLL checker ensures the `InteriorMutable` container itself is borrowed safely, but does not track borrows *inside* it statically.
