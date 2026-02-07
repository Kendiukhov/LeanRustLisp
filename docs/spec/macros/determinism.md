# Determinism

Macro expansion must be pure and deterministic.
- No IO allowed in macros.
- No access to global mutable state (unless thread-local to expansion session).
- `gensym`s must be deterministic based on seed/position.
