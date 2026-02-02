# Macro System Documentation

LRL macros are **syntactic transformations** that operate on the `Syntax` tree (S-expressions) before elaboration.

## Characteristics

*   **Compile-time only**: Macros run during the expansion phase. They cannot perform runtime I/O or side effects (other than defining other macros).
*   **Deterministic**: Expansion order and name generation (`gensym`) are deterministic.
*   **Hygienic**: The system uses the **Scope Sets** model to prevent accidental variable capture. Identifiers introduced by macros are distinct from those at the call site.
*   **Template-based**: Macros are defined using `defmacro` which substitutes arguments into a body template.
*   **Quasiquoting**: `quasiquote`, `unquote`, and `unquote-splicing` are supported for constructing syntax lists. Note that `quasiquote` generates runtime code to build lists, so it is primarily for runtime list construction, though it can be used in macros if the macro expands to code that builds lists.

## Tooling

*   **REPL**: Use `:expand <expr>` to see the fully expanded syntax of an expression.
*   **CLI**: Use `--show-expanded` flag to print expanded syntax for all expressions in a file.
