# Macro System Specification

## Overview

LeanRustLisp (LRL) provides a hygienic, procedural macro system based on syntax objects. The goal is to allow users to extend the language syntax without accidentally capturing variables (hygiene) and without compromising the trusted kernel.

## Decision Note (2026-02-02)

**Macro expansion target:** Macros expand **Syntax -> Syntax** only. Any lowering to `SurfaceTerm` (or directly to `CoreTerm`) is a separate pass (desugaring/elaboration). This enforces a clean phase boundary: macro expansion is purely syntactic and untrusted; elaboration is semantic and type-aware.

**Rationale:** This matches the small-kernel philosophy, improves tooling (`:expand` shows post-macro syntax), keeps hygiene tied to syntax objects, and simplifies determinism (structural rewriting with predictable caching).

**Current Syntax -> SurfaceTerm behavior:** treat as *desugaring* (rename/module split), not macro expansion.

**Quasiquote semantics:** quasiquote builds **syntax objects** (macro-time) rather than runtime lists. Runtime list construction should be expressed explicitly in surface code.

**Semantic identity:** Macros do **not** mint DefId/AdtId/CtorId/FieldId. Semantic IDs are
assigned during elaboration by a deterministic registry. Macro output is plain syntax; any
marker traits/attributes are resolved *after* expansion, not by string matching.

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
    *   A usage `x` refers to that binder when the binder's normalized scope set is a **subset** of the usage scope set.
    *   Unscoped binders are only resolved by unscoped usages (scoped references do not fall back to unscoped names).

### Example
```lisp
(defmacro m () x) ;; x here has scopes {Module}

(let x 1 (m))
```
*   The `let` binder `x` has scopes `{Module}`.
*   The `(m)` expands to `x` with scopes `{Module, MacroScope}`.
*   Macro-introduced references do *not* accidentally bind to unrelated unscoped/local binders; the extra macro scope prevents fallback to unscoped names.
*   *Note*: Hygiene resolution is subset-based with deterministic tie-breaking, not strict equality. Nested macro invocations do not implicitly capture binders from outer macro expansions unless scope propagation makes that binder visible.

### Nested Macro Example (Current Behavior)
```lisp
(defmacro inner () x)
(defmacro outer (e) `(let x Nat 0 ,e))
(outer (inner))
```
**Defined behavior:** `inner` resolves to the global `x` (or remains unbound), **not** the `x`
introduced by `outer`. This follows current subset-based scope resolution and macro-scope
propagation; cross-macro capture does not occur unless the binding is passed explicitly.

## Attributes and Hygienic Metadata

Attributes (e.g. `opaque`, `transparent`) are part of surface syntax and must be preserved through macro expansion.

*   **Propagation**: If a macro rewrites a node that carries attributes, it is responsible for explicitly re-attaching them to the replacement node. Attributes are not dropped implicitly.
*   **Introduction**: Macros may introduce attributes explicitly in their output syntax. There is no hidden injection of attributes by the expander.
*   **Hygienic attribute names**: Attribute identifiers are scoped like other identifiers, so user-defined attributes cannot accidentally capture or be captured by macro-introduced names.
*   **Built-in attributes**: Core attributes such as `opaque` and `transparent` are reserved and are resolved by name after expansion; they are not shadowable. Macros must emit them explicitly when intended.

## Reserved Core Forms

Macro names that collide with core surface forms are reserved and cannot be defined or shadowed by macros. This preserves explicitness at safety and classical boundaries.

Reserved core forms (non-exhaustive but enforced):
*   `def`, `partial`, `unsafe`
*   `axiom`
*   `instance`
*   `inductive`, `structure`
*   `opaque`, `transparent`
*   `import`, `import-macros`
*   `eval`
*   `defmacro`

## Staging

Macros are expanded at **compile time** (or pre-evaluation time in the REPL).
*   Expansion happens top-down, processing macros until a fixed point (or fully expanded).
*   Macros cannot execute runtime effects (IO) but can perform logic to rearrange syntax.

## Macro Environment and Imports

Macros are **file-scoped**. A file can explicitly import macros from other files using:

```lisp
(import-macros "path/to/macros.lrl")
```

*   Imports are **file-scoped** and processed before expansion; their position in the file does not affect visibility.
*   Local macros (defined in the file) shadow imported macros of the same name.
*   Imported modules are searched deterministically (lexicographic by module id).
*   Imports are **not transitive**; if a macro depends on other macro modules, import them explicitly.

## Phase Separation and Eval

Macro expansion is **compile-time only** and operates purely on syntax objects. Runtime evaluation is a separate phase and must be explicit in surface syntax.

*   Any dynamic evaluation must appear as an explicit form (e.g. `(eval <dyn-code> <EvalCap>)`) in the expanded syntax.
*   The expander does not insert `eval` forms or capabilities implicitly.
*   Compile-time macros cannot perform runtime I/O or depend on runtime values; they may only compute and transform syntax.

## Expansion Order and Trace Semantics

*   **Order**: Expansion is deterministic, top-down, and left-to-right within a form. Expansion repeats until a fixed point (no remaining macro calls) or a configured expansion limit.
*   **Scope generation**: Each macro invocation introduces a fresh scope deterministically.
*   **Error/trace**: Errors report the span of the macro call site. Diagnostics include a macro-expansion stack (macro name + call-site span) when available, not only on fatal errors.

## Quasiquoting

To facilitate macro writing, LRL supports:
*   `(quote x)`: Returns the syntax object for `x` literally.
*   `(quasiquote x)` or `` `x ``: Template construction **at macro time** (produces syntax objects).
*   `(unquote x)` or `,x`: Insert the **syntax object** produced by macro-time expansion of `x` into the template.
*   `(unquote-splicing x)` or `,@x`: Splice a **list of syntax objects** produced by macro-time expansion of `x` into the template.

## Determinism

Macro expansion is deterministic.
*   Scope IDs are generated deterministically based on expansion order.
*   `gensym`s use deterministic counters.
*   No access to system time or random numbers in macros.

### Caching Keys

Expansion results may be cached. A cache key must include:
*   Macro identity + definition hash/version.
*   Expanded input syntax structure, including identifier names and scopes (spans may be excluded from the key but must be preserved in output).
*   Macro environment version (imports, definitions, and any feature flags affecting expansion).
*   Expansion mode (e.g. single-step vs full expansion).

## Classical Logic and Non-Silent Injection

Any classical-logic forms (e.g. `import classical` or explicit `axiom`/classical tags) must be present explicitly in expanded syntax.
*   The expander does **not** silently inject classical axioms or attributes.
*   Macros may emit classical forms, but the output must make the classical dependency explicit to downstream phases and tooling.
*   The expander emits a warning diagnostic when a macro expansion produces `unsafe` forms or classical/unsafe axioms/imports, pointing at the macro call site.

## Error Handling

*   Errors during expansion report the span of the macro usage.
*   If an inner term fails elaboration, the span points to the original source location if preserved, allowing users to debug macros effectively.
