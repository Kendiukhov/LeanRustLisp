# Macro System Documentation

LRL macros are **syntactic transformations** that operate on the `Syntax` tree (S-expressions) before elaboration.

## Characteristics

*   **Compile-time only**: Macros run during the expansion phase. They cannot perform runtime I/O or side effects (other than defining other macros).
*   **Deterministic**: Expansion order and name generation (`gensym`) are deterministic.
*   **Hygienic**: The system uses the **Scope Sets** model to prevent accidental variable capture. Identifiers introduced by macros are distinct from those at the call site.
*   **No semantic IDs**: Macros do **not** mint DefId/AdtId/CtorId/FieldId. Semantic IDs are assigned during elaboration by a deterministic registry.
*   **Attribute-aware**: Definition attributes like `opaque` and `transparent` are part of surface syntax and must be explicitly preserved or emitted by macros. Attribute names obey hygiene, except reserved core attributes.
*   **Template-based**: Macros are defined using `defmacro` which substitutes arguments into a body template.
*   **Quasiquoting**: `quasiquote`, `unquote`, and `unquote-splicing` construct **syntax objects at macro time**. Runtime list construction should be explicit in surface code.
*   **Phase-separated**: Macro expansion is compile-time only; any runtime evaluation must appear as an explicit `(eval <dyn-code> <EvalCap>)` form in expanded syntax.
*   **Explicit classical forms**: Classical logic imports or axioms must be explicit in expanded syntax; the expander does not silently inject them.
*   **Module-scoped**: Macros are scoped to a file/module. Use `(import-macros "...")` to bring macros from other files into scope.
*   **Reserved core forms**: Macro names that collide with core forms (e.g. `def`, `axiom`, `unsafe`, `partial`, `instance`, `inductive`, `structure`, `opaque`, `transparent`, `import`, `import-macros`, `eval`, `defmacro`) are reserved and cannot be defined or shadowed.
*   **Macro boundary warnings**: If a macro expansion produces `unsafe` forms or classical/unsafe axioms/imports, the expander emits a warning diagnostic at the macro call site.

## Tooling

*   **REPL**: Use `:expand-1 <expr>` (single step), `:expand-full <expr>` or `:expand <expr>` (full), and `:trace-expand <expr>` (full + trace). Toggle trace during normal processing with `:trace-macros on|off`.
*   **CLI**: Use `--expand-1`, `--expand-full`, or `--trace-expand` to print expansion output for a file (prelude macros loaded). `--show-expanded` remains as a legacy verbose mode during processing. Use `--trace-macros` to print macro traces during normal runs/compiles.
