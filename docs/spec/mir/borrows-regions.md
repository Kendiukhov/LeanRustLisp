# Ownership, Borrows, and Regions in LRL

## Ownership

LRL adopts Rust's ownership model:
-   **Linear/Affine**: Non-copy types must be used exactly once (or moved).
-   **Copy**: Determined by kernel Copy instances; primitive types (Nat, Bool), shared references, and raw pointers are Copy. Function values are non-Copy.
-   **Move Semantics**: Assigning a non-copy value moves ownership, invalidating the source.

The `OwnershipAnalysis` pass verifies these properties:
-   Use-after-move detection.
-   Double-move detection.
-   Linear type consumption (must not be dropped implicitly).

## Borrows

Borrows create references to existing data.
-   **Shared Borrow (`&T`)**: Allows multiple readers, no writers. `Copy`.
-   **Mutable Borrow (`&mut T`)**: Allows single writer, no readers. `Not Copy`.
 
Borrow creation in MIR must be explicit and assigns a **fresh inference region**
to the new reference, with an origin location (the borrow statement).

## Regions

Regions (`'r`) denote the lifetime of a reference.
In MIR, regions are explicit:
```rust
Ref(Region(id), T, Mutability)
```

### Static Region
`Region(0)` is reserved for `STATIC` (global constants).

### Region Variables and Origins
- Each borrow site creates a fresh region variable (e.g. `'?r1`), tagged with its
  origin `Location` (block + statement index).
- NLL solves region constraints over CFG points; region “values” are sets of CFG
  points inferred by the solver.

### Region Inference
LRL uses Non-Lexical Lifetimes (NLL). Regions are not tied to blocks but to the control-flow points where the data is actually used.
-   Constraints are generated from data flow.
-   If a reference is used at point P, its region must be live at P.

### Call-Site Region Constraints
Function calls relate caller and callee regions:
- Argument types are related to parameter types.
- The destination type is related to the callee return type.

Lowering assigns region parameters based on **explicit `Ref` labels** (surface
`Ref #[label] Shared T` / `Ref #[label] Mut T`) or **positional occurrence**
within the signature. Reusing the same label ties lifetimes together; unlabeled
return references use the single-input elision rule (and otherwise must be
labeled explicitly). This lets NLL constrain returned references by the
intended input regions and prevents reference escape across call boundaries.

**Elision policy:** An elided `Ref` label is treated as a *fresh implicit label
variable* during elaboration. If a context expects an explicit label, the elided
label may unify to that explicit label; explicit-to-explicit mismatches remain
errors. After elaboration, labels are concrete strings and **definitional
equality compares labels strictly**. See `docs/spec/ownership_model.md` §3.1 for
the core term representation and examples.

### Closure Capture Extraction
When lowering closures, captures are extracted from the environment using:
- `Move` for non-`Copy` captures.
- `Copy` only when the capture is `Copy`.

This prevents duplication of linear or affine values (including `&mut`).

### Interior Mutability (Classification)
Interior mutability is recognized via **marker traits/attributes** resolved by the
elaborator into DefId-based metadata (no string matching). The standard marker
definitions live in the prelude. This metadata drives:
- runtime check insertion for RefCell/Mutex types,
- the panic-free profile lint (rejects any interior mutability).
The elaborator rejects `interior_mutable` without a kind marker and rejects
conflicting kind markers (e.g., `may_panic_on_borrow_violation` with
`concurrency_primitive`).

**Panic-free profile restrictions**: Any interior mutability (RefCell/Mutex/Atomic) is rejected, indexing is rejected (bounds checks may panic), and `borrow_shared`/`borrow_mut` are rejected.

### Runtime Layout and Indices (Policy)
Dependent indices do **not** affect runtime layout. `MirType::Adt(AdtId, type_args)`
defines the runtime identity; indices are erased or kept only as compile-time
metadata. If a library needs a runtime index, it must be an explicit field.

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
 -   No semantic decisions are made from raw strings; all identities are via IDs.
