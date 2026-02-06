# Core Calculus Specification

## 1. Kernel Calculus Base

The kernel is based on the **Calculus of Inductive Constructions (CIC)** dependent type theory, closely aligned with Lean's kernel.

## 2. Universes

*   **`Prop` (Sort 0)**: The universe of computationally irrelevant propositions.
    *   **Impredicative**: `Prop` is impredicative. The universe level of a Pi-type `Π (x : A), B` is `Prop` if `B : Prop`, regardless of the universe of `A`.
    *   **Erasure**: Terms in `Prop` are proofs and are erased at runtime.
*   **`Type u` (Sort u+1)**: A cumulative hierarchy of computational types, indexed by universe levels `u`.
    *   **Predicative**: The universe level of `Π (x : A), B` where `B : Type v` is `max(level(A), v)`.

## 3. Function Kinds (Ownership)

`Pi` and `Lam` carry a function-kind annotation (`Fn`, `FnMut`, `FnOnce`) that
controls ownership and call semantics for runtime values. The kind is part of
type identity (no definitional equality across kinds). Beta reduction is
unchanged. See `docs/spec/function_kinds.md` for the full specification.

Core grammar excerpt:

```
FnKind ::= Fn | FnMut | FnOnce
Pi(ty, body, binder_info, fn_kind)
Lam(ty, body, binder_info, fn_kind)
```

## 4. Inductive Types and Elimination

The kernel supports inductive definitions.

*   **Large Elimination Restriction**: To maintain proof irrelevance, elimination from an inductive type in `Prop` to a type in `Type u` (where `u > 0`) is restricted.
    *   Allowed only if the inductive type has **zero constructors** (e.g., `False`) or **one constructor** where all constructor fields are in `Prop` (e.g., `True`).
    *   Exception: inductives matching the **equality shape** `(A : Type u) -> (a : A) -> (b : A) -> Prop` with `refl : (A : Type u) -> (a : A) -> Eq A a a` may eliminate into `Type` (transport/J), even though their parameters are in `Type`.
    *   Elimination from `Prop` to `Prop` is always allowed.
*   **Explicit Recursor Universes**: Recursor terms must carry explicit universe levels (e.g., `Rec Nat [u]`). The kernel rejects `Rec` with missing levels. The elaborator computes the level from the motive type and supplies it.

## 5. Definitional Equality and Unfolding

Definitional equality (`a ≡ b`) is decided by a Normalization-by-Evaluation (NbE) engine.

*   **Transparency**: Definitions carry a transparency hint.
    *   **Transparent (Reducible)**: The default. Unfolded during standard type checking.
    *   **Opaque (Irreducible)**: Unfolded only when explicitly requested (e.g., by tactics or specialized reduction modes), effectively abstracting the implementation details.
*   **Reduction**: Includes Beta (λ), Iota (recursion), Zeta (let), and Delta (definition unfolding based on transparency).
*   **Default policy**: Type checking uses transparency mode `Reducible` (respecting `opaque`).
*   **Fuel / budget**: Definitional equality is fuel-bounded to keep normalization predictable. The default fuel is `100_000`, configurable via `LRL_DEFEQ_FUEL` or the CLI flag `--defeq-fuel <N>` (the CLI flag overrides the env var). When fuel is exhausted, the kernel reports an error with context; marking large definitions as `opaque` reduces unfolding pressure.
*   **Fix unfolding**: `fix` (general recursion) is never unfolded during definitional equality. Use `partial` for general recursion and `opaque` to keep it out of reductions in type checking.
*   **Safety classification**: Prop classification respects `opaque` by default; explicit contexts can opt in to unfolding for checks like large elimination and Prop-in-data. MIR lowering may still peek through opaque aliases to detect `Ref`/interior mutability. These classification checks do not make `opaque` transparent for definitional equality.

## 6. Axioms and Classical Logic

The kernel supports classical logic via axioms (e.g., Excluded Middle, Choice).

*   **Explicit Tracking**: Axioms must be declared explicitly.
*   **Explicit Classification**: Axioms may carry tags (e.g., `classical`) that the kernel uses to classify dependencies; no name-based heuristics are used.
    *   Surface syntax attaches tags via `(axiom classical name ty)` or `(axiom (classical) name ty)`. Untagged axioms are treated as non-classical.
*   **Dependency Tracking**: Every definition tracks the set of axioms it depends on (transitively). This allows users to know if a theorem relies on classical logic or specific axioms.
*   **`import classical`** introduces the axiom `classical_choice` with type `Π (P : Prop), ((P → False) → False) → P` (double-negation elimination), tagged as classical.

## 7. Completeness & Totality

*   **Total Fragment**: Definitions involved in types must be terminating.
    *   Structural recursion (via `Rec`) or well-founded recursion (via `Acc`) is enforced.
    *   General recursion (`fix`) is **rejected** in total definitions.
*   **Partial Fragment**: General recursion is allowed and cannot participate in definitional equality during type checking. Partial definitions must return an effect type (e.g., `Comp A`), and the kernel enforces this requirement.
    *   `fix` is the only general-recursion form; it is permitted only in `partial` defs.
