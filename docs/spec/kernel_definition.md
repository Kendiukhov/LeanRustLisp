# Minimal Kernel Definition and Trust Boundary

## 1. Trusted Computing Base (TCB)

To ensure "soundness you can bet a civilization on", the TCB must be minimal.

### Trusted Components
1.  **Kernel Type Checker**: Implements the typing rules for the core calculus.
2.  **Definitional Equality Engine**: Decides conversion (`a ≡ b`). Usually implements Normalization-by-Evaluation (NbE).
3.  **Core Primitives**: Axiomatic semantics for `Nat`, `Eq`, and fundamental inductive types.

Everything else is **outside** the TCB.

## 2. Untrusted Components (But Checkable)

These components can be large and complex, but they must produce artifacts that the trusted kernel or a validator can check.

1.  **Elaborator**: Translates surface syntax (implicit args, inference) into fully explicit core terms. The kernel rejects invalid terms.
2.  **Borrow Checker**: Analyzes ownership and lifetimes.
    *   *Strategy*: Emits region/lifetime evidence or passes annotated IR to a small validator. The borrow checker logic itself is not trusted, only its output.
3.  **Optimizer**: LLVM/MLIR passes.
4.  **Macro System**: Expands syntax. Since macros produce surface syntax which is then refined to core terms, they cannot break soundness (only validity).
5.  **Code Generator**: Lowers to machine code.

## 3. Trust Strategy

*   **Proof Erasure**: `Prop` terms are erased.
*   **Separation of Concerns**: The kernel does not know about memory layout or borrow checking constraints, other than verifying the evidence provided.
