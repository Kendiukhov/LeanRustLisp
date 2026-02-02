# Macro System Specification

## Overview

LeanRustLisp (LRL) provides a hygienic, procedural macro system based on syntax objects. The goal is to allow users to extend the language syntax without accidentally capturing variables (hygiene) and without compromising the trusted kernel.

## Syntax Objects

Macros operate on *Syntax Objects*, not raw S-expressions. A Syntax Object bundles:
*   **Datum**: The structural content (List, Symbol, Int, String).
*   **Span**: Source location information for error reporting.
*   **Scopes**: A set of scope identifiers (marks) used for hygiene.

```rust
struct Syntax {
    kind: SyntaxKind,
    span: Span,
    scopes: Vec<ScopeId>,
}
```

## Hygiene Model

LRL uses a **Scope Sets** model (simplified for this stage).

### Principles
1.  **Lexical Scoping**: Identifiers are resolved based on their name *and* their active scopes.
2.  **Fresh Scopes**: Every macro invocation generates a fresh `ScopeId`.
3.  **Scope Propagation**:
    *   Syntax explicitly introduced by the macro body acquires the fresh `ScopeId`.
    *   Syntax passed as arguments to the macro *retains* its original scopes (it does not get the fresh scope).
4.  **Binder Logic**:
    *   A binder (like `lam x`) binds a name `x` with a specific set of scopes.
    *   A usage `x` refers to that binder only if its scopes are a superset of the binder's scopes (or in our simplified strict equality model, if they match relevantly).

### Example
```lisp
(defmacro m () x) ;; x here has scopes {Module}

(let x 1 (m))
```
*   The `let` binder `x` has scopes `{Module}`.
*   The `(m)` expands to `x` with scopes `{Module, MacroScope}`.
*   The usage `x` `{Module, MacroScope}` does *not* accidentally bind to `let x` `{Module}` if we enforce strict matching or if the macro scope makes it distinct.
*   *Note*: In standard scope sets, it's about "subset/superset" relations. For our MVP, we ensure that macro-introduced variables are distinct from call-site variables by checking that their scope sets distinguish them.

## Staging

Macros are expanded at **compile time** (or pre-evaluation time in the REPL).
*   Expansion happens top-down, processing macros until a fixed point (or fully expanded).
*   Macros cannot execute runtime effects (IO) but can perform logic to rearrange syntax.

## Quasiquoting

To facilitate macro writing, LRL supports:
*   `(quote x)`: Returns the syntax object for `x` literally.
*   `(quasiquote x)` or `` `x ``: template construction.
*   `(unquote x)` or `,x`: Insert the result of evaluating `x` (at expansion time) into the template.
*   `(unquote-splicing x)` or `,@x`: Splice a list into the template.

## Determinism

Macro expansion is deterministic.
*   Scope IDs are generated deterministically based on expansion order.
*   `gensym`s use deterministic counters.
*   No access to system time or random numbers in macros.

## Error Handling

*   Errors during expansion report the span of the macro usage.
*   If an inner term fails elaboration, the span points to the original source location if preserved, allowing users to debug macros effectively.
