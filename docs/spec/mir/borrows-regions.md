# Ownership, Borrows, and Regions in LRL

## Ownership

LRL adopts Rust's ownership model:
-   **Linear/Affine**: Non-copy types must be used exactly once (or moved).
-   **Copy**: Primitive types (Nat, Bool) and shared references are Copy.
-   **Move Semantics**: Assigning a non-copy value moves ownership, invalidating the source.

The `OwnershipAnalysis` pass verifies these properties:
-   Use-after-move detection.
-   Double-move detection.
-   Linear type consumption (must not be dropped implicitly).

## Borrows

Borrows create references to existing data.
-   **Shared Borrow (`&T`)**: Allows multiple readers, no writers. `Copy`.
-   **Mutable Borrow (`&mut T`)**: Allows single writer, no readers. `Not Copy`.

## Regions

Regions (`'r`) denote the lifetime of a reference.
In MIR, regions are explicit:
```rust
Ref(Region(id), T, Mutability)
```

### Static Region
`Region(0)` is reserved for `STATIC` (global constants).

### Region Inference
LRL uses Non-Lexical Lifetimes (NLL). Regions are not tied to blocks but to the control-flow points where the data is actually used.
-   Constraints are generated from data flow.
-   If a reference is used at point P, its region must be live at P.

## Safety Guarantees

The combination of Ownership and NLL guarantees:
1.  **No Dangling Pointers**: Data cannot be dropped while a reference to it is live.
    -   Enforced by checking `StorageDead` against active loans.
2.  **No Data Races**: Mutable borrows exclude all other access.
    -   Enforced by conflict detection.
3.  **No Use-After-Free**: Ownership mechanics ensure moved values aren't accessed.

## Codegen Contract

The backend can assume:
-   If a `Ref` exists, it points to valid memory.
-   If `&mut T` exists, it is unique.
-   No need for runtime borrow flags for normal references.
