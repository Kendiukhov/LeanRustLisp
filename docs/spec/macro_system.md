# Macro System Specification

## Overview

LeanRustLisp (LRL) provides a template-based macro system on syntax objects: a macro
`(defmacro name (p1 ... pn) template)` is instantiated by substituting its arguments for its
parameters in the template (no code runs at macro time; macros are not procedural). Expansion is
hygienic for local binders. The goal is to allow users to extend the language syntax without
accidentally capturing variables and without compromising the trusted kernel: macro output is
ordinary surface syntax that goes through the whole pipeline (desugaring, elaboration, kernel,
MIR).

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
(defmacro m () x)   ;; the template's x carries no scope until an expansion adds one

(let x Nat 1 (m))
```
*   The `let` binder `x`, written by the user, has no scopes.
*   `(m)` expands to `x` with scopes `{MacroScope}` (the fresh scope of this call).
*   Macro-introduced references do *not* bind to unrelated unscoped/local binders; the macro scope prevents fallback to unscoped names, so `x` refers to a global `x` (or is unbound).
*   *Note*: Hygiene resolution is subset-based with deterministic tie-breaking, not strict equality. Nested macro invocations do not implicitly capture binders from outer macro expansions unless scope propagation makes that binder visible.

### Limits of hygiene

Hygiene covers local binders only (see `docs/spec/macros/hygiene.md`):
*   Macro names are resolved by bare name in the module where the call is expanded, so a local
    binder named like a macro is taken over by the macro in head position, and a template that calls
    another macro uses the call site's macro of that name.
*   Global names in a template (definitions, constructors, inductives) are resolved at the call
    site by the elaborator, like any free identifier.

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

Reserved core forms (`RESERVED_MACRO_NAMES` in `frontend/src/macro_expander.rs`):
*   `def`, `partial`, `unsafe`, `noncomputable`
*   `axiom`
*   `instance`
*   `inductive`, `structure`
*   `opaque`, `transparent`
*   `import`, `import-macros`, `module`, `open`
*   `eval`
*   `defmacro`

## Staging

Macros are expanded at **compile time** (or pre-evaluation time in the REPL), before desugaring.
*   Expansion is one recursive pass in normal order: a macro call is replaced by its instantiated
    template, which is expanded again; other lists are expanded element by element.
*   Macros cannot execute runtime effects (IO) and cannot compute: there are no conditionals, no
    pattern matching on arguments and no syntax primitives. The only operation is substitution of
    the arguments into the template (plus `quasiquote`/`unquote`, which build syntax).

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
*   Compile-time macros cannot perform runtime I/O or depend on runtime values; they only substitute syntax into templates.

## Expansion Order and Trace Semantics

*   **Order**: Expansion is deterministic, top-down, and left-to-right within a form. The result of each macro call is expanded again until no macro call remains, subject to limits: at most 10,000 macro invocations per top-level form (`F0106`), a nesting depth of at most 128 (`F0106`), and a repeated identical call (same macro, same arguments with scopes) inside its own expansion is reported as a cycle (`F0107`).
*   **Scope generation**: Each macro invocation introduces a fresh scope deterministically.
*   **Error/trace**: Errors report the span of the macro call site. Diagnostics raised during expansion (boundary violations, limits, cycles) carry the macro-expansion stack (macro name + call-site span) as labels. Diagnostics raised later (elaboration, kernel, MIR) are related to the macro calls of the same file afterwards (`attach_macro_call_sites` in `cli/src/driver.rs`): a diagnostic whose span lies inside a macro call site gets the label "in code produced by macro 'm'" (template code carries the call site's span), and a macro call inside the reported span gets "macro 'm' expanded here" (e.g. a kernel ownership error, which is reported on the whole definition body). A MIR borrow error located at a compiler-inserted statement without source position is reported at the span of the offending loan.

## Quasiquoting

To facilitate macro writing, LRL supports:
*   `(quote x)`: Returns the syntax object for `x` literally.
*   `(quasiquote x)` or `` `x ``: Template construction **at macro time** (produces syntax objects).
*   `(unquote x)` or `,x`: Insert the **syntax object** produced by macro-time expansion of `x` into the template.
*   `(unquote-splicing x)` or `,@x`: Splice a **list of syntax objects** produced by macro-time expansion of `x` into the template.

**Parameter substitution and quasiquote.** In a template that is not quasiquoted, every occurrence of a
parameter is replaced by the argument. Inside a quasiquote, a parameter is replaced only inside an
`unquote`/`unquote-splicing` of the outermost quasiquote; other symbols under the quasiquote are literal
text, even if they have the name of a parameter (`substitute_rec_with_scope` in
`frontend/src/macro_expander.rs`). So in
`(defmacro defchan (name ctor) `(inductive ,name (sort 1) (ctor ,ctor (pi id Nat ,name))))` the keyword `ctor`
stays and only `,ctor` is replaced (before, every `ctor` was replaced and the expansion was malformed).

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
*   **Macro boundary.** When a macro expansion produces an `(unsafe name type value)` definition, an `eval` form, any `axiom` (tagged or not) or `(import classical)`, the expander reports `F0104` at the macro call site, with the expansion stack as labels. By default this is an **error** (for prelude and user macros alike; the prelude allowlist `PRELUDE_MACRO_BOUNDARY_ALLOWLIST` is empty); `--macro-boundary-warn` downgrades it to a warning.

## Error Handling

*   Errors during expansion report the span of the macro usage.
*   If an inner term fails elaboration, the span points to the original source location if preserved, allowing users to debug macros effectively.
