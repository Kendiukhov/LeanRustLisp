# Staging

Macros run in a separate stage before type checking.

## Invocation

Macros are expanded by the `Frontend`. The expander runs a VM/interpreter that evaluates the macro function.
Dependencies for macros must be compiled and available in the "macro stage" (or host).
