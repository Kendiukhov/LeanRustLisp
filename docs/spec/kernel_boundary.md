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
    *   Tracks axiom dependencies.
2.  **Definitional Equality (`nbe.rs`)**:
    *   Implements conversion checking via Normalization-by-Evaluation.
    *   Respects **transparency** settings (unfolding vs opaque).
    *   Uses fuel-bounded evaluation to keep defeq total; fuel is configurable via `LRL_DEFEQ_FUEL`.
3.  **AST (`ast.rs`)**:
    *   Defines the core term structure (CIC with De Bruijn indices).

### Policies
*   **Transparency**: Default is transparent. Opaque definitions hide implementation details from the kernel's automatic unfolding, but can be forced open if needed (e.g. by reflective tools, though standard checking respects opacity).
*   **Proof Irrelevance**: Proofs (terms in `Prop`) are computationally irrelevant. They cannot influence the runtime behavior of programs (except via their existence as a precondition).
*   **Axiom Tracking**: The kernel does not forbid axioms, but strictly tracks their usage. Classical
    classification is explicit: axioms carry tags (e.g., `classical`), and dependency analysis only uses
    those tags (no name-based heuristics). A "proven" theorem depending on a tagged axiom is tainted.

## 2. Untrusted Periphery

These components verify properties or transform code, but their correctness is not critical for the logical consistency of the kernel (though bugs here can produce invalid code that the kernel rejects, or runtime bugs).

1.  **Elaborator**: Infers types, implicit arguments, and universe levels. Produces full kernel terms, including explicit universe levels on recursors (kernel rejects missing levels).
2.  **Parser**: Converts text to surface syntax.
3.  **Code Generator**: Compiles core terms to Rust/binary. Relies on the kernel's erasure of proofs.
4.  **Borrow Checker**: (Future) Will produce evidence of memory safety.

## 3. Interaction

The periphery constructs `Definition` objects and submits them to the kernel (`Env::add_definition`). The
kernel accepts them only if they pass its add-time checks (core invariants, type correctness, ownership,
termination/effects for total definitions), and defeq/whnf are fuel-bounded to avoid divergence. The
environment does not expose mutable access to definitions in the public API, so kernel checks cannot be
skipped by untrusted frontends. Once accepted, a definition is trusted and immutable.

For detailed phase contracts and elaboration invariants, see `docs/spec/phase_boundaries.md`.
