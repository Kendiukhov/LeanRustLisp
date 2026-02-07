# Kernel Boundary and Trust Model

This document defines the boundary of the Trusted Computing Base (TCB) for LeanRustLisp.

## 1. Trusted Core (The Kernel)

The kernel is the minimal set of components that must be correct for the system to be sound.

### Components
1.  **Type Checker (`checker.rs`)**:
    *   Verifies type correctness of terms.
    *   Validates core invariants on incoming terms (e.g., no metas, explicit recursor levels) and checks
        `ty : Sort` plus `value : ty` (when provided) before admission. Closedness is enforced implicitly
        by type-checking in an empty context, not by a separate syntactic pass.
    *   Enforces universe levels (including impredicative `Prop`).
    *   Enforces termination (structural/well-founded) for total definitions.
    *   Enforces effect boundaries (Total vs Partial vs Unsafe).
    *   Enforces elimination restrictions (Prop -> Type).
    *   Enforces ownership/linearity on values.
    *   Validates function kind annotations on `Lam`/`Pi` (Fn/FnMut/FnOnce) and
        rejects misuse without an explicit coercion.
    *   Validates capture-mode annotations only for **structural correctness**
        (closure id exists, capture indices reference actual free variables). It
        does **not** enforce capture-mode *strength*.
    *   Tracks axiom dependencies.
2.  **Definitional Equality (`nbe.rs`)**:
    *   Implements conversion checking via Normalization-by-Evaluation.
    *   Respects **transparency** settings (unfolding vs opaque).
    *   Uses fuel-bounded evaluation to keep defeq total; fuel is configurable via `LRL_DEFEQ_FUEL`.
        Fuel exhaustion is reported with guidance to mark large definitions `opaque` or raise the fuel.
3.  **AST (`ast.rs`)**:
    *   Defines the core term structure (CIC with De Bruijn indices).

### Policies
*   **Transparency**: Default is transparent. Opaque definitions hide implementation details from the kernel's automatic unfolding, but can be forced open if needed (e.g. by reflective tools, though standard checking respects opacity). Prop classification respects `opaque` by default; explicit contexts can opt in to unfolding for checks like large elimination and Prop-in-data. MIR lowering may peek through opaque aliases to detect `Ref`/interior mutability for borrow checking; these checks do not affect definitional equality.
*   **Proof Irrelevance**: Proofs (terms in `Prop`) are computationally irrelevant. They cannot influence the runtime behavior of programs (except via their existence as a precondition).
*   **Axiom Tracking**: The kernel does not forbid axioms, but strictly tracks their usage. Classical
    classification is explicit: axioms carry tags (e.g., `classical`), and dependency analysis only uses
    those tags (no name-based heuristics). A "proven" theorem depending on a tagged axiom is tainted.
    This includes implicit unsafe axioms introduced by explicit Copy instances
    (`copy_instance(TypeName)` with the `unsafe` tag).
*   **Reserved primitives**: Names like `Ref`, `Shared`, `Mut`, `borrow_shared`, `borrow_mut`,
    and `index_*` are reserved. These are treated as compiler intrinsics during MIR lowering.
    The kernel only admits them as axioms with fixed signatures (intended for the prelude); user
    code must not define them.
    `Ref`/`Shared`/`Mut` define the reference type constructor and mutability tags used in
    ownership checks. `borrow_shared`/`borrow_mut` are safe primitives usable in total code, with
    safety enforced by the MIR borrow checker. `index_*` remain `unsafe` axioms until their safety
    contract is enforced.
*   **Capture modes (TCB note)**: Capture-mode *strength* is enforced in MIR lowering
    (which recomputes required capture modes from usage). The kernel only checks that
    capture annotations are well-formed and does not trust them for safety; this places
    capture-mode strength in the periphery until/unless the kernel adopts a conservative
    validator.

### Prelude and Macro Boundary
*   **Prelude stack is trusted**: compile paths load `stdlib/prelude_api.lrl` plus a backend platform
    layer (`stdlib/prelude_impl_dynamic.lrl` or `stdlib/prelude_impl_typed.lrl`) before user code.
    These prelude files are part of the TCB and are compiled with reserved primitives enabled.
    They may define unsafe/classical axioms that user code cannot introduce silently.
*   **Macro boundary is strict for prelude stack**: prelude files are compiled with
    `MacroBoundaryPolicy::Deny`, so macro expansion cannot introduce unsafe/classical forms unless
    the macro is explicitly allowlisted in the compiler. Any such forms must appear explicitly in
    the prelude source or via an allowlisted macro.
*   **User code defaults to Deny**: `--macro-boundary-warn` downgrades macro boundary violations to
    warnings for user code (not for the prelude).

## 2. Untrusted Periphery

These components verify properties or transform code, but their correctness is not critical for the logical consistency of the kernel (though bugs here can produce invalid code that the kernel rejects, or runtime bugs).

1.  **Elaborator**: Infers types, implicit arguments, universe levels, and function kinds. Produces full kernel terms, including explicit universe levels on recursors (kernel rejects missing levels).
2.  **Parser**: Converts text to surface syntax.
3.  **Code Generator**: Compiles core terms to Rust/binary. Relies on the kernel's erasure of proofs.
4.  **Borrow Checker**: Implemented in the `mir` crate as NLL-style analysis. It is outside the TCB
    but enforces the safety contract for `borrow_shared`/`borrow_mut` in compiled code. It also
    enforces function-call borrow semantics: `Fn` calls take a shared borrow of the closure
    environment, `FnMut` calls take a mutable borrow, and `FnOnce` calls consume the closure.
    **Release-bar invariant:** the production pipeline must run MIR typing + NLL for *all* top-level
    definitions and derived closure bodies.

## 3. Interaction

The periphery constructs `Definition` objects and submits them to the kernel (`Env::add_definition`). The
kernel accepts them only if they pass its add-time checks (core invariants, type correctness, ownership,
termination/effects for total definitions), and defeq/whnf are fuel-bounded to avoid divergence. The
environment does not expose mutable access to definitions in the public API, so kernel checks cannot be
skipped by untrusted frontends. Once accepted, a definition is trusted and immutable.

For detailed phase contracts and elaboration invariants, see `docs/spec/phase_boundaries.md`.
