# 2. MIR Introduction

Date: 2025-01-15

## Status

Accepted

## Context

Directly lowering to Rust AST from surface terms is difficult for analysis (borrow checking).

## Decision

Introduce a Mid-level IR (MIR).
- Control Flow Graph structure.
- Explicit drops and borrows.

## Consequences

- Easier to implement NLL.
- Better optimization potential.
