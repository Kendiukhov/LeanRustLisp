# Kernel Boundary and Trust Model

This document defines the boundary of the Trusted Computing Base (TCB) for LeanRustLisp.

## 1. Trusted Core (The Kernel)

The kernel is the minimal set of components that must be correct for the system to be sound.

### Components
1.  **Type Checker (`checker.rs`)**:
    *   Verifies type correctness of terms.
    *   Enforces universe levels (including impredicative `Prop`).
    *   Enforces termination (structural/well-founded) for total definitions.
    *   Enforces effect boundaries (Total vs Partial vs Unsafe).
    *   Enforces elimination restrictions (Prop -> Type).
    *   Tracks axiom dependencies.
2.  **Definitional Equality (`nbe.rs`)**:
    *   Implements conversion checking via Normalization-by-Evaluation.
    *   Respects **transparency** settings (unfolding vs opaque).
3.  **AST (`ast.rs`)**:
    *   Defines the core term structure (CIC with De Bruijn indices).

### Policies
*   **Transparency**: Default is transparent. Opaque definitions hide implementation details from the kernel's automatic unfolding, but can be forced open if needed (e.g. by reflective tools, though standard checking respects opacity).
*   **Proof Irrelevance**: Proofs (terms in `Prop`) are computationally irrelevant. They cannot influence the runtime behavior of programs (except via their existence as a precondition).
*   **Axiom Tracking**: The kernel does not forbid axioms, but strictly tracks their usage. A "proven" theorem depending on `Choice` is tainted by `Choice`.

## 2. Untrusted Periphery

These components verify properties or transform code, but their correctness is not critical for the logical consistency of the kernel (though bugs here can produce invalid code that the kernel rejects, or runtime bugs).

1.  **Elaborator**: Infers types, implicit arguments, and universe levels. Produces full kernel terms.
2.  **Parser**: Converts text to surface syntax.
3.  **Code Generator**: Compiles core terms to Rust/binary. Relies on the kernel's erasure of proofs.
4.  **Borrow Checker**: (Future) Will produce evidence of memory safety.

## 3. Interaction

The periphery constructs `Definition` objects and submits them to the kernel (`Env::add_definition`). The kernel accepts them only if they pass all checks (Type, Termination, Effects, Soundness). Once accepted, a definition is trusted and immutable.
