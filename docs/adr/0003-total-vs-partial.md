# 3. Total vs Partial Split

Date: 2025-01-20

## Status

Accepted

## Context

Dependent types require normalization, which requires termination.

## Decision

Split the language into Total and Partial fragments.
- Only Total terms can be used in types.
- Partial terms live in `Comp` or `IO`.

## Consequences

- No "Type in Type" paradoxes.
- Logical consistency.
