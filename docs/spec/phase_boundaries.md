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
- Attributes (e.g. `opaque`, `transparent`) are preserved or explicitly re-attached by macro output.
- Expansion is compile-time only; any runtime evaluation must be an explicit surface form (e.g. `eval`).
- Classical logic imports/axioms must appear explicitly in expanded syntax (no silent injection).

## 2. Elaboration Boundary

**Input:** expanded surface syntax.

**Output:** kernel core terms (`kernel::ast::Term`) plus core definitions.

**Invariants:**
- No `Term::Meta` remains (all metas solved).
- All implicit arguments are inserted; the term is fully explicit.
- `match` is fully desugared to `Rec` with an explicit motive.
- Every `Rec` term carries explicit universe levels (no empty level list), with the level list
  ordered as `[inductive universe params..., motive level]`.
- `Fix` is only used at function types (enforced by the kernel).
- Lambda/function kinds are inferred and attached to `Lam`/`Pi`. Explicit kind
  annotations (if present) must be at least the inferred kind.
- Core-term invariants are validated after elaboration (e.g. `kernel::checker::validate_core_term`).

The elaborator is responsible for computing the recursor universe level from the motive type and
attaching it to `Rec` together with the inductive's universe parameters.

## 3. Kernel Boundary

**Input:** fully explicit core terms from elaboration.

**Output:** accepted definitions in the kernel environment (or a rejection).

**Invariants enforced by the kernel:**
- Type checking for all terms.
- Definitional equality (NbE).
- Large elimination restrictions for `Prop`.
- Termination / totality boundaries.
- Explicit recursor levels are required.
- Function kind validation for `Lam`/`Pi` (e.g., `FnOnce` values are not treated
  as `Fn` without an explicit coercion).
- Effect boundaries are enforced via totality markers (total cannot call partial/unsafe;
  partial cannot call unsafe). Effect typing (requiring `Comp` returns) is enforced.
- Capture-mode annotations are checked for **structural validity only**
  (closure id exists, indices reference actual free variables). The kernel does not
  enforce capture-mode *strength*.

## 4. MIR Lowering Boundary

**Input:** kernel-accepted core terms.

**Output:** MIR bodies.

**Invariants expected by MIR lowering:**
- Core terms are explicit and contain no surface constructs.
- `Rec` is the canonical elimination form (pattern matching already desugared).
- Inductive parameters and indices are explicit in `Rec` applications.
- `Fix` is only used at function types (safe lowering).
- MIR recomputes **required capture modes** from closure usage and rejects any
  annotation that is weaker than required. Capture modes determine whether a
  captured value is moved or borrowed (and with what mutability), and MIR
  instantiates the corresponding regions/borrows during lowering.

## 5. Safety and Codegen Boundary

**Input:** MIR bodies.

**Output:** borrow-checked MIR and generated Rust.

**Invariants:**
- Borrow and ownership checks are applied before codegen.
- The production pipeline must run MIR typing + NLL for top-level user-defined
  bodies and derived closure bodies (this is a release-bar invariant).
- Canonical constructor aliases are excluded: constructors are resolved from
  inductive metadata as constructor values, not admitted as ordinary definitions.
- `Prop` terms are erased before codegen (no runtime dependence on proofs).

## 6. Failure Policy

Any phase may reject input that violates these invariants. The kernel remains the ultimate authority for soundness.
