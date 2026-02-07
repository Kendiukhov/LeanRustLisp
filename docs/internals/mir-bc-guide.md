# MIR and Bytecode Guide

## MIR
Mid-level IR used for optimization and borrow checking.
- Constructed from elaborated terms.
- Explicit control flow (CFG).

## Bytecode (BC)
Interpreter bytecode used for:
- REPL execution.
- Macro expansion.
- `const` evaluation.

The BC virtual machine is distinct from the compiled output.
