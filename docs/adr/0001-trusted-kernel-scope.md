# 1. Trusted Kernel Scope

Date: 2025-01-01

## Status

Accepted

## Context

We need to ensure logical soundness of the proof system.

## Decision

We will isolate the core logic into a `kernel` crate.
- Only `kernel` is trusted.
- `frontend` and `codegen` are untrusted.
- The kernel validates all terms produced by the frontend.

## Consequences

- Slower compilation (re-checking).
- Higher assurance.
