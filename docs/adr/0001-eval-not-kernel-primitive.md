# ADR 0001: Eval Is Not a Kernel Primitive

Date: 2026-02-04
Status: Accepted

## Context
LRL includes a surface form for runtime `eval`, intended to evaluate dynamic code and return `Dyn`.
This is inherently effectful and must not influence definitional equality or kernel computation.
The kernel remains the trusted core and must stay free of runtime evaluation semantics.

## Decision
`eval` is **not** a kernel primitive. It is treated as a **capability-gated, computational-only**
feature:
- `eval` returns `Dyn` and requires `EvalCap`.
- `eval` is forbidden in type positions and must not be reduced by definitional equality (NbE).
- Macro expansion is compile-time only; prelude macros cannot inject `eval` unless explicitly
  allowlisted.

## Consequences
- The elaborator and kernel enforce a hard boundary (reject in types; opaque in defeq).
- Prelude can declare nominal placeholders (`Dyn`, `EvalCap`, and `eval`) without runtime semantics.
- The interpreter/runtime remains a future extension; no refactors are required in the kernel when
  adding an actual evaluator.
