# LeanRustLisp Language Analysis

## Executive Summary

LeanRustLisp (LRL) is an experimental programming language that synthesizes three paradigms into a cohesive system:

1. **Lean-grade formal verification** – Dependent types, theorem proving, proof erasure
2. **Rust-grade memory safety** – Ownership, borrowing, affine types, lifetime tracking
3. **Lisp-grade metaprogramming** – S-expression syntax, hygienic macros

The language achieves this through a **minimal trusted kernel design**, providing "soundness you can bet a civilization on."

---

## Core Language Features

### 1. Type System: Calculus of Inductive Constructions (CIC)

LRL's kernel implements a full dependent type theory based on CIC, closely aligned with Lean's kernel:

**Universe Hierarchy:**
- **`Prop` (Sort 0)**: Impredicative universe for proofs
  - Terms are computationally irrelevant and erased at runtime
  - `Π (x : A), B : Prop` if `B : Prop`, regardless of `A`'s universe
- **`Type u` (Sort u+1)**: Predicative hierarchy for computational types
  - Universe polymorphism supported

**Dependent Types:**
```lisp
;; Pi types (dependent functions)
(pi n Nat (pi m Nat Nat))           ;; Nat → Nat → Nat

;; Dependent product example
(pi A (sort 1) (pi a A (Eq A a a))) ;; ∀ A, ∀ a : A, a = a
```

**Inductive Types:**
Full CIC-style inductive definitions with automatic recursor generation:
```lisp
(inductive Nat (sort 1)
  (ctor zero Nat)
  (ctor succ (pi n Nat Nat)))

(inductive Eq (pi A (sort 1) (pi a A (pi b A (sort 0))))
  (ctor refl (pi A (sort 1) (pi a A (Eq A a a)))))
```

### 2. Ownership & Resource Management

LRL implements Rust-style ownership without garbage collection:

**Affine Types (Default):**
- Values can be used 0 or 1 times
- Destructors run on drop
- Prevents use-after-move, double-free, data races

**Copy Types (Opt-in):**
```lisp
(inductive copy Nat ...)    ;; Mark type as freely copyable
(inductive copy Bool ...)
```

**Borrowing & References:**
```
&'ρ A       ;; Shared reference (copyable, read-only)
&'ρ mut A   ;; Unique reference (linear, read-write)
```

**Lifetime Tracking:**
- First-class lifetimes at the type level (erased at runtime)
- Outlives relation constraint solving
- Non-lexical lifetimes (NLL) analysis

### 3. Hygienic Macro System

**Syntax Objects:**
Macros operate on syntax objects bundling datum, source span, and scope sets:
```rust
struct Syntax {
    kind: SyntaxKind,  // List, Symbol, Int, etc.
    span: Span,        // Source location
    scopes: Vec<ScopeId>, // Hygiene scopes
}
```

**Hygiene Model:**
- Each macro invocation generates a fresh scope ID
- Macro-introduced identifiers don't capture call-site variables
- Arguments retain original scopes

**Quasiquoting:**
```lisp
(defmacro id (x) x)
`(list ,x ,@xs)    ;; Template with unquote and splice
```

### 4. Safety Fragments

LRL stratifies code into three regions:

| Fragment | Characteristics | Type Participation |
|----------|----------------|-------------------|
| `def` | Total, terminating | Yes (appears in types) |
| `partial def` | General recursion | No (under `Comp` effect) |
| `unsafe def` | FFI, raw pointers | No (manual safety) |

---

## Architecture & Design

### Trusted Kernel (TCB)

The Trusted Computing Base is intentionally minimal (~200KB of Rust):

```
kernel/
├── ast.rs       → Term, Level, InductiveDecl
├── checker.rs   → Type checking, inference, WHNF reduction
├── nbe.rs       → Normalization-by-Evaluation for definitional equality
└── ownership.rs → Affine type checking hooks
```

**Kernel Invariants:**
- De Bruijn indices for binding (0 = most recent)
- Explicit universe levels on recursors
- No unresolved metavariables
- Closed terms only

### Untrusted but Checkable Components

Everything outside the kernel produces artifacts the kernel can verify:

```
frontend/        → Parser, macro expander, elaborator
mir/             → Mid-level IR, ownership/borrow analysis
codegen/         → Rust code emission
cli/             → REPL and compilation driver
```

### Compilation Pipeline

```
LRL Source (.lrl)
     │
     ▼ Parser
Syntax Objects (with spans, scopes)
     │
     ▼ Macro Expander
Expanded Surface Syntax
     │
     ▼ Elaborator (implicit resolution, motive synthesis)
kernel::Term (fully explicit)
     │
     ▼ Kernel Type Checker
Verified Terms + Environment
     │
     ▼ MIR Lowering
Control-flow IR (basic blocks, locals)
     │
     ├── Ownership Analysis (use-after-move, linear consumption)
     └── Borrow Analysis (conflicting borrows, escaping refs)
     │
     ▼ Codegen
Rust Code (with proof erasure)
```

---

## Key Traits & Capabilities

### 1. Proof Erasure
Propositions (`Prop`, Sort 0) are erased at runtime:
- Proofs don't affect performance
- Types carry semantic meaning but not runtime cost
- Equality proofs (`Eq A a b`) vanish in generated code

### 2. Large Elimination Restrictions
To maintain proof irrelevance:
- Cannot eliminate from `Prop` to `Type u` (u > 0) in general
- Exceptions: empty types (`False`), singleton propositions, equality (`Eq`)

### 3. Axiom Tracking
```lisp
(axiom classical LEM (pi P (sort 0) (or P (not P))))
```
- Axioms explicitly declared and tagged
- Transitive dependency tracking
- Know if a theorem relies on classical logic

### 4. Termination Checking
- Structural recursion via pattern matching (`match`/`Rec`)
- Well-founded recursion via `Acc` (accessibility predicates)
- Non-terminating code quarantined under `Comp` monad

### 5. Pattern Matching
Desugared to eliminators with computed motives:
```lisp
(match n Nat
  (case (zero) m)
  (case (succ pred ih) (succ ih)))
```

---

## Advantages

### 1. **Correctness Guarantees**
- Minimal TCB reduces attack surface for soundness bugs
- Dependent types catch logic errors at compile time
- Formal proofs can coexist with executable code

### 2. **Memory Safety Without GC**
- Rust-level performance characteristics
- No runtime garbage collection pauses
- Data-race freedom in safe code

### 3. **Expressiveness**
- Full dependent types for precise specifications
- Pattern matching with dependent motives
- Universe polymorphism for generic libraries

### 4. **Extensibility**
- Hygienic macros don't break soundness
- S-expression syntax enables DSLs
- Macros produce checkable surface syntax

### 5. **Interoperability**
- Compiles to Rust for ecosystem access
- FFI through `unsafe def` boundary
- Type erasure enables efficient code

### 6. **Theorem Proving**
- Equality type for propositional equality
- Proof terms can be written and checked
- Mechanization in Lean for meta-theory

---

## Comparison with Related Languages

| Feature | LRL | Lean 4 | Rust | Idris 2 |
|---------|-----|--------|------|---------|
| Dependent Types | ✓ Full CIC | ✓ Full CIC | ✗ | ✓ Full |
| Ownership/Borrowing | ✓ Affine | ✗ | ✓ | ✓ (QTT) |
| Proof Erasure | ✓ | ✓ | N/A | ✓ |
| Hygienic Macros | ✓ | ✓ | ✓ (proc) | ✗ |
| S-Expression Syntax | ✓ | ✗ | ✗ | ✗ |
| Minimal TCB | ✓ | ✓ | ✗ | ✓ |
| Compiles to Native | ✓ (via Rust) | ✓ (C) | ✓ | ✓ (Scheme) |

---

## Standard Library

The prelude (`stdlib/prelude.lrl`) provides foundational types:

```lisp
;; Core types (marked Copy)
(inductive copy Nat ...)   ;; Natural numbers
(inductive copy Bool ...)  ;; Booleans

;; Polymorphic containers
(inductive List ...)       ;; Linked lists

;; Computational effects
(inductive Comp ...)       ;; Partiality monad

;; Propositional equality
(inductive Eq ...)         ;; a = b proofs
```

Core functions: `add`, `not`, `and`, `or`, `if_nat`, `append`

---

## Use Cases

1. **Verified Systems Software**: Write low-level code with formal proofs
2. **Smart Contracts**: Prove correctness of financial logic
3. **Cryptographic Libraries**: Verify security properties
4. **Embedded Systems**: No GC, predictable memory
5. **Theorem Proving**: Interactive proof development in REPL

---

## Current Status

LRL is experimental with working implementations of:
- ✓ Full CIC kernel with type checking
- ✓ Hygienic macro expansion
- ✓ Elaboration with implicit arguments
- ✓ MIR-based ownership/borrow analysis
- ✓ Rust code generation
- ✓ Interactive REPL

Active development areas:
- Universe polymorphism ergonomics
- Tactic framework
- IDE integration
- Standard library expansion

---

## Conclusion

LeanRustLisp represents a novel point in the programming language design space: combining the **correctness guarantees** of proof assistants like Lean, the **resource safety** of Rust, and the **syntactic extensibility** of Lisp. The minimal trusted kernel design ensures that soundness bugs are localized to a small, auditable core, while the untrusted periphery provides ergonomic features without compromising trust.

The language is suitable for applications where both **correctness** and **performance** are critical—verified systems programming, cryptography, smart contracts, and formally verified software.
