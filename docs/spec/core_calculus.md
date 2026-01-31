# Core Calculus Specification

## 1. Kernel Calculus Base

The kernel is based on the **Calculus of Inductive Constructions (CIC)** dependent type theory, closely aligned with Lean's kernel.

## 2. Universes

*   **`Prop` (Sort 0)**: The universe of computationally irrelevant propositions.
    *   **Impredicative**: `Prop` is impredicative. The universe level of a Pi-type `Π (x : A), B` is `Prop` if `B : Prop`, regardless of the universe of `A`.
    *   **Erasure**: Terms in `Prop` are proofs and are erased at runtime.
*   **`Type u` (Sort u+1)**: A cumulative hierarchy of computational types, indexed by universe levels `u`.
    *   **Predicative**: The universe level of `Π (x : A), B` where `B : Type v` is `max(level(A), v)`.

## 3. Inductive Types and Elimination

The kernel supports inductive definitions.

*   **Large Elimination Restriction**: To maintain proof irrelevance, elimination from an inductive type in `Prop` to a type in `Type u` (where `u > 0`) is restricted.
    *   Allowed only if the inductive type has **zero constructors** (e.g., `False`) or **one constructor** where all non-parameter fields are in `Prop` (e.g., `Eq`, `True`, `Acc`).
    *   Elimination from `Prop` to `Prop` is always allowed.

## 4. Definitional Equality and Unfolding

Definitional equality (`a ≡ b`) is decided by a Normalization-by-Evaluation (NbE) engine.

*   **Transparency**: Definitions carry a transparency hint.
    *   **Transparent (Reducible)**: The default. Unfolded during standard type checking.
    *   **Opaque (Irreducible)**: Unfolded only when explicitly requested (e.g., by tactics or specialized reduction modes), effectively abstracting the implementation details.
*   **Reduction**: Includes Beta (λ), Iota (recursion), Zeta (let), and Delta (definition unfolding based on transparency).

## 5. Axioms and Classical Logic

The kernel supports classical logic via axioms (e.g., Excluded Middle, Choice).

*   **Explicit Tracking**: Axioms must be declared explicitly.
*   **Dependency Tracking**: Every definition tracks the set of axioms it depends on (transitively). This allows users to know if a theorem relies on classical logic or specific axioms.

## 6. Completeness & Totality

*   **Total Fragment**: Definitions involved in types must be terminating.
    *   Structural recursion (via `Rec`) or well-founded recursion (via `Acc`) is enforced.
*   **Partial Fragment**: General recursion is allowed but quarantined under an effect (e.g., `Comp`) and cannot participate in definitional equality during type checking.