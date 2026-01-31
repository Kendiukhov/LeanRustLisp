# Core Calculus Specification

## 1. Kernel Calculus Base

The kernel is based on the **Calculus of Inductive Constructions (CIC)** dependent type theory.

## 2. Universes

*   **`Prop`**: The universe of computationally irrelevant propositions. Terms in `Prop` are erased at runtime.
*   **`Type u`**: A cumulative hierarchy of computational types, indexed by universe levels `u`.

## 3. Inductive Types

The kernel supports inductive definitions similar to Lean, including:
*   Built-in primitives where needed (`Nat` for efficiency, though conceptually inductive).
*   User-defined inductives: `List`, `Vec`, etc.
*   Indexed families (W-types or direct support for indices).

## 4. Equality

*   **Definitional Equality**: `â/é/ä/æ` reductions plus unfolding rules. This is decided by the kernel's normalization engine.
*   **Propositional Equality (`Eq`)**: The standard homogeneous equality type, inhabited by `refl`.

## 5. Completeness & Totality

*   **Total Fragment**: Definitions involved in types must be terminating.
    *   Structural recursion or well-founded recursion is enforced.
*   **Partial Fragment**: General recursion is allowed but quarantined under an effect (e.g., `Comp`) and cannot participate in definitional equality during type checking.
