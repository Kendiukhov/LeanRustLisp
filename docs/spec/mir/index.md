# MIR Specification (Structure + Places)

This document defines the structural shape of MIR (Mid-level IR) in LRL, with
emphasis on places/projections and where region information lives.

## Overview

MIR is a typed, CFG-based IR used for ownership, borrow checking (NLL), and
typed backend readiness. It is the single pipeline IR for both batch compile
and REPL evaluation.

## Core Structure

A MIR body contains:
- **Locals**: typed slots (`MirType`) for arguments, temporaries, and return.
- **Basic blocks**: a sequence of statements plus a terminator.
- **CFG**: explicit control-flow edges through terminators.

Key nodes:
- `Statement::Assign(Place, Rvalue)`
- `Statement::StorageLive/StorageDead(Local)`
- `Terminator::{Return, Goto, SwitchInt, Call, Unreachable}`

## Places and Projections

A **Place** represents a memory location:
```
Place = LocalId + Projection*
```

Projections include:
- `Deref` (indirection through references or raw pointers)
- `Field(i)` (field projection for struct/ctor fields)
- `Downcast(variant_index)` (enum/ADT variant projection)
- `Index(local)` (optional; for indexed containers)

Place typing must be **projection-aware**, using ADT layout metadata so that
borrow checking and codegen can reason about field-level aliasing.

## Regions in MIR

Regions are not standalone MIR nodes; they are carried by `MirType::Ref`.
Borrow creation is explicit (`Rvalue::Ref`) and **assigns a fresh inference
region** to the new reference at the borrow site (origin location).

- `Region::Static` is reserved for globals / truly static references.
- NLL solves region constraints over CFG points.

## Semantic Identity Rule

All semantic identity in MIR is keyed by nominal IDs (DefId/AdtId/CtorId/FieldId),
not by raw strings. Borrow checking and codegen must not depend on names.
