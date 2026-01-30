# LeanRustLisp (LRL)

> A language where types can express theorems, resources are real and tracked, and the language is programmable by its users.

The compiler is not your friend; it’s your very expensive, very literal lawyer.

## Core Goals

1.  **Soundness you can bet a civilization on**: Small trusted kernel, proofs checked, no “trust me bro” in the core.
2.  **Systems-level performance**: Predictable layout, no mandatory GC, AOT compilation, good FFI.
3.  **Rust-grade resource discipline**: Ownership/borrowing, lifetime checking, data-race freedom in safe code.
4.  **Lean-grade specification**: Dependent types, inductive types, theorem proving, proof erasure.
5.  **Lisp-grade extensibility**: Hygienic macros, syntax as data, elaborator/tactic plugins.

## Non-Goals

*   **Full type inference for dependent types everywhere**: You will write annotations. The alternative is undecidability plus suffering.
*   **Mutating dependently-typed values in-place without restrictions**: Mutable typestate + dependent indices is a swamp; we’ll do it with explicit patterns that stay decidable.
*   **A single “one ring” mechanism for metaprogramming, effects, optimization, and proofs**: That path ends in a baroque compiler that no one can modify.

## Safety Boundaries

LRL defines three distinct fragments:

1.  **`def` (Total Fragment)**: Definitions used in types/definitional equality must be strictly terminating (structural or well-founded recursion). Can appear in types.
2.  **`partial def` (Partial Fragment)**: General recursion allowed, but cannot appear in types. Lives under an effect (e.g., `Comp`).
3.  **`unsafe def` (Unsafe Fragment)**: FFI, raw pointers, manual memory. Explicitly marked. The kernel remains sound, but safety contract is user-verified.

## License

[Apache 2.0 / MIT]
