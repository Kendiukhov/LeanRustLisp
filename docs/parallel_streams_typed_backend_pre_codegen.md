# Parallel Streams: Typed Backend Readiness (Pre-Codegen)

This file splits the remaining **pre-codegen** typed-backend readiness work into parallel, non-overlapping streams. Each stream can be done by an independent agent with minimal contention. Any cross-stream dependency is called out explicitly.

## Stream 0: Contract Clarifications + Spec Deltas (docs only)
- Decide and document (locked):
  - **Nominal ID scheme**: deterministic, build-stable IDs derived from
    `PackageId + ModulePath + ItemName + Disambiguator`, hashed or interned.
    `DefId` = top-level def; `AdtId` = inductive type; `CtorId` = (AdtId, ctor_index);
    `FieldId` = (CtorId, field_index). IDs are minted by a single registry during
    declaration loading/elaboration (never inside MIR passes; never from HashMap order).
  - **ADT layout/index policy**: dependent indices do **not** affect runtime layout.
    `MirType::Adt(AdtId, type_args)` is the runtime identity; indices are erased or
    carried only as compile-time metadata. Runtime-dependent indices must be explicit
    fields in the runtime representation.
  - **Static region + borrow assignment (NLL)**: distinguished `Region::Static` for
    globals; each borrow creates a fresh inference region with an origin location.
    NLL solves region constraints (outlives + liveness + reborrow) over CFG points.
  - **Interior mutability mapping**: use kernel-level marker traits/attributes resolved
    to DefId-based flags (no string matching, no special syntax). The panic-free
    linter rejects any interior mutability (RefCell/Mutex/Atomic).
  - **Sanity rule**: borrowck/codegen/MIR typing must never depend on raw strings for
    semantic identity.
- Update docs:
  - `docs/spec/mir/borrows-regions.md`
  - `docs/spec/mir/nll-constraints.md`
- **Dependency:** None. Unblocks Streams 1–5.

## Stream 1: Nominal IDs + No Name-Based Semantics
- Replace name-based semantics in MIR types and literals with IDs.
- Introduce stable ID types and thread them through MIR:
  - `mir/src/types.rs` (AdtId -> numeric or DefId-based)
  - `mir/src/lib.rs` (Literal::InductiveCtor uses CtorId, not String)
  - `mir/src/lower.rs` (lower to IDs, remove string matching on "Ref"/"Mut"/"Shared", builtins)
- Update pretty-printing and tests to use IDs or stable name lookup tables.
- **Dependency:** Stream 0 decisions.

## Stream 2: ADT Layout Metadata + Place Typing
- Add layout metadata so `PlaceElem::Field`/`Downcast` can be typed precisely.
- Implement projection-aware typing in `place_type` and related helpers:
  - `mir/src/analysis/nll.rs`
  - `mir/src/analysis/borrow.rs` (if retained for tests)
- Add `PlaceElem::Index` if indexing is part of the language surface.
- Update MIR pretty/printers and snapshots.
- **Dependency:** Stream 1 (IDs + layout metadata).

## Stream 3: Region/Lifetime Plumbing Fixes
- Fix region assignment for `Rvalue::Ref` and borrow creation:
  - Remove hardcoded `Region(0)` for new refs.
  - Avoid renumbering that erases static vs local regions.
  - Ensure constraints are generated from actual borrow regions.
- Adjust NLL tests for new region assignment rules.
- **Dependency:** Stream 0 decisions (static region policy).

## Stream 4: Drop/Escape Checks + Structured Diagnostics
- Insert explicit `StorageDead` at end-of-scope/function exit so dangling borrows are detected.
- Implement escaping-reference checks (returning ref to local, etc.).
- Wire `BorrowError` + `MirSpan` diagnostics instead of strings.
- Update CLI/driver reporting to preserve structured spans.
- **Dependency:** Stream 3 (region correctness).

## Stream 5: Interior Mutability Mapping + Panic-Free Profile Gating
- Map source-level constructs to `MirType::InteriorMutable` (RefCell/Mutex/Atomic).
- Add a profile flag in `PipelineOptions` and gate `PanicFreeLinter` on it.
- Ensure runtime checks are only injected for actual interior-mutable uses.
- **Dependency:** Stream 0 decisions (mapping policy).

## Stream 6: Borrow-Check Artifacts for Codegen
- Persist `BorrowCheckResult` (regions, loan ranges, runtime checks) as artifacts.
- Attach artifacts to MIR bodies or to driver outputs for codegen consumption.
- Add golden tests for serialized borrow-check evidence.
- **Dependency:** Streams 2–4 (place typing + region correctness + diagnostics).

## Stream 7: Surface Borrow Syntax + Integration Tests
- Implement surface syntax for borrows/ref creation.
- Enable and expand pending borrow surface tests:
  - `cli/tests/pending_borrow_surface.rs`
  - `tests/pending/borrow_surface.lrl`
- Add integration tests that round-trip through parse/elab/lower/NLL.
- **Dependency:** None, but benefits from Streams 1–4 for correctness.

---

### Notes on Non-Overlap
- Stream 1 touches core MIR types and lowering; avoid concurrent edits in `mir/src/types.rs`, `mir/src/lib.rs`, `mir/src/lower.rs`.
- Stream 2 depends on layout metadata from Stream 1 and should not overlap in those files.
- Stream 3 is mostly in NLL and lowering; keep separate from Stream 4 diagnostics.
- Stream 5 is isolated to lints/pipeline + lowering mapping.
- Stream 6 is plumbing/serialization; low overlap once APIs are stable.
- Stream 7 is front-end heavy and can proceed in parallel with MIR changes.
