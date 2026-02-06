# Parallel Streams Plan — Red Team Fix Tasks (2026-02-04)

This plan splits the fresh audit fix items into independent parallel streams. Streams are non‑overlapping; if a dependency exists, it is explicitly called out.

## Stream A — Borrow-Shape & Alias Hardening (MIR/NLL)
**Scope:** Prevent opaque aliases from bypassing borrow checking and interior‑mutability runtime checks.

Tasks:
- Implement a “shape reducer” in MIR lowering that can see through `opaque` aliases only for `Ref` and interior‑mutability detection. (`mir/src/lower.rs`)
- Create loans based on `Rvalue::Ref` regardless of destination type. (`mir/src/analysis/nll.rs`)
- Insert interior‑mutability runtime checks at borrow sites (not only by local type). (`mir/src/analysis/nll.rs`)
- Add regression tests: opaque alias to `Ref Mut` must still create a loan and fail on conflicting access; opaque alias to `RefCell` must still insert checks. (`mir/tests/*`, `cli/tests/*`)

Dependencies:
- None, but if Stream D changes `MirType::Opaque` compatibility, tests here should be updated accordingly.

## Stream B — Prop-Shape & Erasure Enforcement (Kernel/MIR)
**Scope:** Ensure Prop semantics are enforced even through opaque aliases.

Tasks:
- Define `is_prop_like` (or equivalent) that unfolds opaque aliases for Prop classification only. (`kernel/src/checker.rs`, `mir/src/lower.rs`)
- Use Prop‑like detection in:
  - Prop‑elimination restriction. (`kernel/src/checker.rs`)
  - Prop‑field prohibition in data inductives. (`kernel/src/checker.rs`)
  - MIR `is_prop` tagging for erasure. (`mir/src/lower.rs`)
- Add regression tests for opaque Prop alias:
  - Large elimination must be rejected.
  - Proof data must be erased and not influence runtime branches. (`kernel/tests/*`, `mir/tests/*`, `cli/tests/*`)

Dependencies:
- None. This stream is independent of Stream A, but both may touch alias handling; keep definitions separate (Prop‑shape vs borrow‑shape).

## Stream C — Effect Typing Enforcement
**Scope:** Enforce `partial def` return‑type discipline (`Comp A`) to match README claims.

Tasks:
- Enforce `partial def` return type is `Comp A` (or explicit effect type). (`kernel/src/checker.rs`)
- Add elaborator‑level diagnostics for missing effect wrapper. (`frontend/src/elaborator.rs` or `cli/src/driver.rs`)
- Add tests: partial def returning `Nat` fails; `Comp Nat` passes. (`kernel/tests/*`, `cli/tests/*`)
- If enforcement is deferred, update docs to retract/clarify the guarantee. (`README.md`, `docs/spec/*`)

Dependencies:
- None. If docs changes are chosen instead of enforcement, capture that explicitly in the PR.

## Stream D — MIR Typing Strictness (Opaque)
**Scope:** Prevent `MirType::Opaque` from acting as a wildcard.

Tasks:
- Require reason‑equality (or tagged equivalence) for `MirType::Opaque` compatibility even outside refs. (`mir/src/analysis/typing.rs`)
- Add tests for incompatible opaque reasons failing type checks. (`mir/tests/*`)

Dependencies:
- None. Coordinate with Stream A to avoid conflicting assumptions in borrow‑shape tests.

## Stream E — Axiom Tag Enforcement Mode
**Scope:** Prevent classical/unsafe axiom laundering when strict tracking is needed.

Tasks:
- Add CLI flag (e.g., `--require-axiom-tags`) that rejects untagged axioms. (`cli/src/driver.rs`, `frontend/src/declaration_parser.rs`)
- Add tests for strict mode rejecting untagged axioms while allowing tagged ones. (`cli/tests/*`)

Dependencies:
- None.

## Stream F — Defeq Fuel Diagnostics
**Scope:** Make defeq fuel exhaustion actionable.

Tasks:
- Improve fuel‑exhaustion diagnostics with top‑level definition names and hints. (`kernel/src/nbe.rs`, `kernel/src/checker.rs`)
- Add tests that assert enriched diagnostics for fuel exhaustion. (`kernel/tests/*`, `cli/tests/*`)

Dependencies:
- None.
