# Phase Boundaries and Core Invariants

This document records the contract between compiler phases. It is the source of truth for what each phase must produce and what downstream phases may assume.

## 1. Macro Expansion Boundary

**Input:** surface syntax (S-expressions + macro forms).

**Output:** surface syntax with macros expanded.

**Invariants:**
- Expansion is deterministic (no order-dependent results).
- Hygiene is preserved (introduced binders do not capture).
- Source spans are retained on expanded syntax where possible.
- **Span contract:** nodes originating from existing syntax keep their spans; nodes synthesized by macro
  expansion (including quasiquote list constructors) use the span of the originating form. `unquote`
  and `unquote-splicing` preserve the spans of the inserted syntax.
- Expansion does not introduce core terms; it only produces surface syntax.

## 2. Elaboration Boundary

**Input:** expanded surface syntax.

**Output:** kernel core terms (`kernel::ast::Term`) plus core definitions.

**Invariants:**
- No `Term::Meta` remains (all metas solved).
- All implicit arguments are inserted; the term is fully explicit.
- `match` is fully desugared to `Rec` with an explicit motive.
- Every `Rec` term carries explicit universe levels (no empty level list).
- `Fix` is only used at function types (enforced by the kernel).
- Core-term invariants are validated after elaboration (e.g. `kernel::checker::validate_core_term`).

The elaborator is responsible for computing the recursor universe level from the motive type and attaching it to `Rec`.

## 3. Kernel Boundary

**Input:** fully explicit core terms from elaboration.

**Output:** accepted definitions in the kernel environment (or a rejection).

**Invariants enforced by the kernel:**
- Type checking for all terms.
- Definitional equality (NbE).
- Large elimination restrictions for `Prop`.
- Termination / totality boundaries.
- Explicit recursor levels are required.

## 4. MIR Lowering Boundary

**Input:** kernel-accepted core terms.

**Output:** MIR bodies.

**Invariants expected by MIR lowering:**
- Core terms are explicit and contain no surface constructs.
- `Rec` is the canonical elimination form (pattern matching already desugared).
- Inductive parameters and indices are explicit in `Rec` applications.
- `Fix` is only used at function types (safe lowering).

## 5. Safety and Codegen Boundary

**Input:** MIR bodies.

**Output:** borrow-checked MIR and generated Rust.

**Invariants:**
- Borrow and ownership checks are applied before codegen.
- `Prop` terms are erased before codegen (no runtime dependence on proofs).

## 6. Failure Policy

Any phase may reject input that violates these invariants. The kernel remains the ultimate authority for soundness.
