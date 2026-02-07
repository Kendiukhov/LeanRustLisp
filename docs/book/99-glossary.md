# Glossary

- **Kernel**: The trusted core component that verifies fully elaborated terms.
- **Elaboration**: The process of converting surface syntax (with implicit arguments) into fully explicit core terms.
- **Definitional Equality**: Two terms are definitionally equal if they reduce to the same form.
- **Prop**: The universe of propositions. Elements are proofs and are erased at runtime.
- **Type**: The universe of types. Elements are data and are preserved at runtime (mostly).
- **Motive**: The return type function for a recursor/match expression.
- **Eliminator**: A function that destructs an inductive value (like `Nat.rec`).
- **MIR**: Mid-level Intermediate Representation. A control-flow graph representation used for optimizations and borrow checking.
- **Region**: A static scope in the program (lifetime).
- **Hygiene**: The property of macros that prevents accidental variable capture.
- **Staging**: The separation of compile-time (macro expansion) and runtime execution.
- **Capability**: A token representing permission to perform an effect.
