# Production Parallel Streams (Pre-Codegen)

Scope: tasks derived from `report_production_grade_engineer_pre_codegen.md`. Streams are designed to be non-overlapping; dependencies are explicitly stated.

**Safety & Contract Preservation Guidelines**

All streams must preserve the current release-bar contract (P1–P8). Treat this contract as a hard gate: any change that weakens kernel boundary enforcement, totality/Prop restrictions, macro boundary Deny behavior, MIR typing/NLL soundness, or axiom/noncomputable policy is unacceptable unless explicitly approved and accompanied by updated specs + regression tests. Concretely: (1) keep refactors behavior-preserving by default and split “refactor-only” PRs from “semantic change” PRs; (2) require that every PR touching kernel/, frontend/, mir/, or cli/driver passes the full CI suite plus the scope-limited release-bar audit/red-team checks; (3) for every fixed bug or modified invariant, add or update a regression test in the narrowest layer possible (kernel/MIR/frontend) so future refactors cannot silently reintroduce it; (4) avoid accidental nondeterminism by banning iteration over HashMap in any output-relevant path unless keys are sorted; and (5) prohibit unwrap()/expect() in production paths—replace with structured errors carrying spans—so industrialization work reduces risk rather than introducing new failure modes.

## Stream A: Span + Diagnostics Plumbing
Focus: stable, source-level diagnostics across the pipeline.

Tasks:
1. Replace pointer-keyed span tracking with stable term IDs in `frontend/src/elaborator.rs` and downstream mappings.
2. Wire `MirSpanMap` into borrow/ownership errors in `mir/src/analysis/*` and render source spans in `cli/src/compiler.rs`.
3. Add golden tests for macro-expanded spans and borrow/ownership errors.

Dependencies:
- Blocks Stream B (hygiene) only on test harness updates if spans are required in new tests.
- Unblocks Stream D (defeq perf) for consistent profiling output in diagnostics.

## Stream B: Macro Hygiene + Name Resolution
Focus: determinism and scalability of names/macros.

Tasks:
1. Upgrade hygiene resolution in `frontend/src/desugar.rs` to support compatible scope subsets (not exact equality).
2. Add module-qualified name resolution + deterministic import scopes in `frontend/src/elaborator.rs` (and parser surface forms as needed).
3. Add macro expansion memoization and explicit recursion cycle detection in `frontend/src/macro_expander.rs`.

Dependencies:
- Independent from Stream A code changes, but new tests should reuse Stream A’s span work when available.

## Stream C: MIR Boundary Hygiene (Opaque + Literal Term)
Focus: IR boundary clarity and respecting transparency.

Tasks:
1. Remove `borrow_shape_unfold` and require explicit borrow-wrapper markers instead of unfolding `opaque` in `mir/src/lower.rs`.
2. Eliminate or gate `Literal::Term` in `mir/src/lib.rs` with an explicit `OpaqueConst` error path.
3. Add tests that `opaque` aliases do not influence borrow checking unless explicitly marked.

Dependencies:
- Independent of Streams A/B. Some tests may benefit from Stream A span mapping but are not required.

## Stream D: Defeq + Unification Performance Guardrails
Focus: predictable typechecking performance.

Tasks:
1. Add a session-scoped defeq cache shared across elaboration passes (`kernel/src/nbe.rs`, `frontend/src/elaborator.rs`).
2. Add size-based fuel heuristics and include fuel detail metrics in defeq diagnostics.
3. Add a `--defeq-profile` CLI flag that prints top reductions.

Dependencies:
- Independent of Streams B/C. Stream A recommended for high-quality diagnostics, but not required.

## Stream E: Dataflow + Liveness Performance
Focus: MIR analysis scaling.

Tasks:
1. Replace HashSet-based liveness with a bitset implementation in `mir/src/analysis/liveness.rs`.
2. Add micro-bench/regression tests for liveness runtime and stability.

Dependencies:
- Independent of Streams A–D.

## Stream F: Safety + Panic Elimination
Focus: no panics from well-typed programs.

Tasks:
1. Replace marker-registry `expect` in `mir/src/lower.rs` with proper `LoweringError` diagnostics.
2. Enforce `panic_free` profile at pipeline boundary (fail compile if runtime checks inserted).
3. Add tests for marker registry errors and panic-free enforcement.

Dependencies:
- Independent of Streams B/C/D/E; may use Stream A span mapping if available.

## Suggested Cross-Stream Milestones
1. A + F for diagnostics and panic-free correctness.
2. B for macro/name scalability.
3. C for IR boundary clarity.
4. D + E for performance and determinism.
