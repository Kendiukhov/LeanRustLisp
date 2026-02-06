All streams must preserve the current release-bar contract (P1–P8). Treat this contract as a hard gate: any change that weakens kernel boundary enforcement, totality/Prop restrictions, macro boundary Deny behavior, MIR typing/NLL soundness, or axiom/noncomputable policy is unacceptable unless explicitly approved and accompanied by updated specs + regression tests. Concretely: (1) keep refactors behavior-preserving by default and split “refactor-only” PRs from “semantic change” PRs; (2) require that every PR touching kernel/, frontend/, mir/, or cli/driver passes the full CI suite plus the scope-limited release-bar audit/red-team checks; (3) for every fixed bug or modified invariant, add or update a regression test in the narrowest layer possible (kernel/MIR/frontend) so future refactors cannot silently reintroduce it; (4) avoid accidental nondeterminism by banning iteration over HashMap in any output-relevant path unless keys are sorted; and (5) prohibit unwrap()/expect() in production paths—replace with structured errors carrying spans—so industrialization work reduces risk rather than introducing new failure modes. 
All streams must preserve the current release-bar contract (P1–P8). Treat this contract as a hard gate: any change that weakens kernel boundary enforcement, totality/Prop restrictions, macro boundary Deny behavior, MIR typing/NLL soundness, or axiom/noncomputable policy is unacceptable unless explicitly approved and accompanied by updated specs + regression tests. Concretely: (1) keep refactors behavior-preserving by default and split “refactor-only” PRs from “semantic change” PRs; (2) require that every PR touching kernel/, frontend/, mir/, or cli/driver passes the full CI suite plus the scope-limited release-bar audit/red-team checks; (3) for every fixed bug or modified invariant, add or update a regression test in the narrowest layer possible (kernel/MIR/frontend) so future refactors cannot silently reintroduce it; (4) avoid accidental nondeterminism by banning iteration over HashMap in any output-relevant path unless keys are sorted; and (5) prohibit unwrap()/expect() in production paths—replace with structured errors carrying spans—so industrialization work reduces risk rather than introducing new failure modes.

**Stream A: Kernel Recursor Metadata + NbE Integration**
- Define shared `InductiveInfo`/recursor metadata in `kernel/` and export from `Env`.
- Update `kernel/src/nbe.rs` (`try_reduce_rec`) to consume shared metadata, eliminating local arity logic.
- Add kernel tests covering indexed inductive recursor reduction using shared metadata.
Dependencies: none.

**Stream B: MIR Recursor Lowering Integration**
- Update `mir/src/lower.rs` (`lower_rec`) to use shared kernel recursor metadata.
- Remove local `count_indices` logic in MIR lowering.
- Replace any `expect/unwrap` in `lower_rec` with structured `LoweringError` carrying spans.
- Add MIR lowering snapshots for Nat/Vec/Eq recursors using shared metadata.
Dependencies: Stream A must land first (shared metadata API).

**Stream C: Prop Classification + Transparency Context**
- Introduce explicit transparency context for Prop classification in `kernel/src/checker.rs`.
- Replace `Transparency::All` usage in `is_prop_like` and `check_elimination_restriction` with the new context.
- Add kernel regression tests proving `opaque` aliases do not unfold during Prop checks unless explicitly enabled.
Dependencies: none.

**Stream D: Macro Expansion Budget + Cycle Diagnostics**
- Add expansion step budget + max depth in `frontend/src/macro_expander.rs`.
- Emit new diagnostic code when budget is exceeded; include macro trace.
- Add tests for recursive macro exhaustion and stable diagnostic output.
Dependencies: none.

**Stream E: Borrow Checker Precision + Constraint Diagnostics (NLL)**
- Improve place conflict precision in `mir/src/analysis/nll.rs` (disjoint fields, index projections).
- Attach loan + region constraint explanation to `BorrowError` diagnostics.
- Add MIR tests for reborrows, disjoint-field accesses, and constraint explanations.
Dependencies: none.

**Stream F: Remove `unwrap/expect` in Production Paths (Pre-codegen)**
- Audit and replace `unwrap/expect` in `mir/src/types.rs`, `mir/src/analysis/*`, and `frontend/src/elaborator.rs` production paths with structured errors carrying spans.
- Ensure any diagnostic uses stable sorting (no HashMap iteration in outputs without key ordering).
- Add targeted negative tests for each replaced panic site.
Dependencies: none. Avoid touching files owned by Streams A/B/C/D/E during their PR windows.

**Stream G: Defeq Fuel + Performance Guardrails**
- Move defeq fuel configuration to CLI (explicit flags) and record in build metadata.
- Add defeq microbench tests and fuel regression thresholds in `kernel/tests/`.
- Ensure defeq diagnostics report fuel source (override/env/default) deterministically.
Dependencies: none.

**Stream H: Elaborator Diagnostics Pretty-Printing**
- Implement user-facing pretty-printer for core terms and wire into `frontend/src/elaborator.rs` errors.
- Preserve spans and avoid Debug output in end-user diagnostics.
- Add frontend tests asserting stable, readable error messages.
Dependencies: none.

**Stream I: Termination Checker Upgrade**
- Replace heuristic decreasing-arg selection with a size-change or recursor-only policy in `kernel/src/checker.rs`.
- Strengthen mutual recursion checks with explicit measure requirements.
- Add kernel regression tests for accepted and rejected mutual recursion patterns.
Dependencies: none.
