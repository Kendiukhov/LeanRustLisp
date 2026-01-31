# Design Note: Impredicative Prop in LRL Kernel

This document outlines the design and implementation of an impredicative `Prop` type in the LeanRustLisp (LRL) kernel, following the guidance in `agents/tasks/impredicative_loop.md`.

## 1. `Prop` and Universe Level Conventions

In this kernel, we establish the following universe level conventions to distinguish between propositions (proofs) and types (data):

*   **`Prop`**: The sort of propositions. It is represented at the lowest universe level, `Sort(Level::Zero)`. Terms of type `Prop` are proofs, which are intended to be erasable during code generation.

*   **`Type u`**: The sort of types at a specific universe level `u`. It is represented as `Sort(Level::Succ(u))`.
    *   `Type 0` corresponds to `Sort(Succ(Zero))`, which is the first universe level above `Prop`. It contains "small" types like `Nat` and `Bool`.
    *   `Type 1` corresponds to `Sort(Succ(Succ(Zero)))`, and so on.

This hierarchy is essential for maintaining consistency and preventing paradoxes while allowing `Prop` to be impredicative.

## 2. The Impredicative Π-Type Universe Rule

To make `Prop` impredicative, we introduce a special universe-level computation rule for Π-types (dependent functions). The universe level of a Π-type `Π (x : A), B` is determined by the universe levels of its domain `A` and codomain `B`.

Let `A : Sort u` and `B : Sort v`. The resulting sort of `Π (x : A), B` is `Sort(level_imax(u, v))`, where `level_imax` is defined as:

```
level_imax(u, v) := if v is Level::Zero then Level::Zero else Level::max(u, v)
```

**Rule Explanation:**

1.  **Impredicativity**: If the codomain `B` is in `Prop` (i.e., `v` is `Level::Zero`), then the entire Π-type is also in `Prop`. This allows for quantification over types of any universe level while remaining within `Prop`. For example, `Π (A : Type 0), (Π (p : Prop), p)` is itself a `Prop`. This is the core of Lean-style impredicativity.

2.  **Predicativity**: If the codomain `B` is in `Type` (i.e., `v` is not `Level::Zero`), then the resulting universe level is the standard maximum of the domain and codomain levels. For example, `Π (A : Type 0), A` resides in `Type 1` because its codomain can be a large type. Similarly, `Π (A : Type 0), Prop` resides in `Type 1` because `Prop` itself is a type (inhabiting `Type 0`), not a proposition.

This `level_imax` function will be the single source of truth for calculating the universe level of Π-types in the kernel's type checker.

## 3. Elimination from `Prop` into `Type`

**A critical restriction is required to maintain logical consistency and enable proof erasure:** a term of type `Prop` (a proof) cannot be used to compute a term of type `Type` (data).

**Planned Restriction:**

The kernel will forbid pattern matching on a term whose type is in `Prop` to produce a result that is in `Type`. For example, if `p : MyProp`, where `MyProp : Prop`, one cannot write a `match p with ...` expression that returns a `Nat`.

This restriction, often called "non-informative proofs," is fundamental. Without it, one could "prove" `False` and then use that proof to produce any data value, leading to a trivial and inconsistent system. While the full implementation of a `match` expression and this check may be deferred, the design acknowledges this restriction as a foundational principle. The checker will eventually be equipped to reject such invalid eliminations.

## 4. Difference from Predicative `Prop`

A **predicative** system would treat `Prop` like any other universe level. In a predicative system, the universe rule for Π-types would always be `Level::max(u, v)`.

This would mean that `Π (A : Type 0), (∀ p:Prop, p)` would have the sort `Type 0`, not `Prop`. While simpler, a predicative `Prop` significantly reduces the expressiveness of the logic, making it cumbersome to state certain higher-order properties.

By choosing an **impredicative** `Prop`, we gain expressive power, allowing us to quantify over all types to form a proposition, a hallmark of the Calculus of Inductive Constructions (CIC) upon which Lean is based. The trade-off is the added complexity of the `level_imax` rule and the strict requirement for restricting eliminations from `Prop` to `Type`.
