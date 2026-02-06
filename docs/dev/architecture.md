# Compiler Architecture (Deterministic IDs + Pipeline Spine)

This document captures architectural invariants needed for typed backends and
stable builds.

## Deterministic ID Registry

A single registry mints nominal IDs during declaration loading/elaboration.
IDs are derived from:
- PackageId (name + version + source + hash)
- ModulePath
- ItemName
- Disambiguator (only when required)

Definitions:
- **DefId**: top-level definition (functions, constants, axioms)
- **AdtId**: inductive type definition
- **CtorId**: (AdtId, ctor_index)
- **FieldId**: (CtorId, field_index)

Rules:
- IDs are **deterministic** and **build-stable**.
- IDs are **not** minted in MIR passes.
- No semantic pass (borrowck/codegen/typing) depends on raw strings.

## Phase Spine (Single Pipeline)

Source → parse → macro-expand → elaborate → kernel check → lower to MIR →
NLL borrow check → codegen

Notes:
- Macros are syntax-only and **do not mint semantic IDs**.
- Elaboration resolves identifiers and assigns DefId/AdtId/CtorId/FieldId.
- MIR and downstream passes consume IDs and metadata only.

## Runtime Layout Policy

Dependent indices do **not** affect runtime layout. Runtime-dependent indices
must be explicit fields in the runtime representation.

## Interior Mutability Policy

Interior mutability is expressed by **marker traits/attributes** resolved to
DefId-based flags during elaboration. The panic-free profile rejects any
interior mutability (RefCell/Mutex/Atomic).

## Sanity Rule

Borrow checking, MIR typing, and codegen must never depend on raw strings for
semantic identity. All semantics are keyed by IDs (including PackageId).
