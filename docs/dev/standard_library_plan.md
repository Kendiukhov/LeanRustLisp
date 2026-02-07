# Standard Library Development Plan (LRL 0.1 -> 0.2)

## Purpose

Define a concrete, testable roadmap to move from a prelude-centric alpha setup to a real standard library with:

- one public API contract (`prelude_api`)
- tiny backend platform shims (`prelude_impl_dynamic`, `prelude_impl_typed`)
- shared backend-neutral stdlib modules for user-facing logic
- compact, readable syntax conventions suitable for day-to-day programming

This plan assumes current backend architecture and ownership/type/NLL rules remain authoritative.

## Current Baseline (as of this plan)

- Prelude architecture already exists:
  - `stdlib/prelude_api.lrl` (public contract)
  - `stdlib/prelude_impl_dynamic.lrl` (dynamic platform layer)
  - `stdlib/prelude_impl_typed.lrl` (typed platform layer)
- Shared API contains core types/functions (`Nat`, `Bool`, `List`, `add`, `append`, etc.).
- Platform layers are small and mostly runtime-boundary definitions (`Dyn`, `EvalCap`, `eval`).
- Function application already accepts multiple arguments in one form:
  - `(f a b c)` parses/desugars as chained application.
- Function definition type/binder syntax is still mostly unary/curried at core level:
  - explicit nested `lam`/`pi` style remains canonical.

## Design Principles

1. Single public contract
- User code targets API names/types, not backend-specific files.
- No user program should import or depend on `prelude_impl_*`.

2. One stdlib, two tiny platforms
- Shared algorithms live once under `stdlib/std/*`.
- `prelude_impl_dynamic.lrl` and `prelude_impl_typed.lrl` stay platform-only.

3. Backend-neutral semantics first
- Any function in shared stdlib must compile under both backends.
- Differences are allowed only for explicitly documented platform boundaries.

4. Strictly test-driven migration
- Every moved/added stdlib function gets compile + behavior checks.
- Conformance tests gate dynamic/typed parity for overlap subset.

5. Syntax compactness without semantic shortcuts
- Keep core calculus unchanged (curried semantics).
- Add/desugar ergonomic sugar to reduce boilerplate where safe.

## Target Stdlib Layout

```text
stdlib/
  prelude_api.lrl
  prelude_impl_dynamic.lrl
  prelude_impl_typed.lrl
  std/
    core/
      bool.lrl
      nat.lrl
      logic.lrl
    data/
      list.lrl
      option.lrl
      result.lrl
      pair.lrl
    control/
      comp.lrl
      maybe.lrl
    text/
      show_nat.lrl
      show_bool.lrl
    laws/
      eq.lrl
      order.lrl
```

Notes:
- `prelude_api.lrl` should expose minimal bootstrap names and import/open stable std modules as needed.
- Keep `print_*` and runtime-boundary hooks near prelude/API layer until IO surface is stabilized.

## Scope Definition

### In scope (0.1 -> 0.2)

- Core data + algorithms that are backend-neutral:
  - `Bool`, `Nat`, `List`, `Option`, `Result`, `Pair`
  - list operations (`length`, `map`, `foldl`, `foldr`, `reverse`, `filter`)
  - Nat utilities (`pred`, `sub` bounded, comparisons)
  - boolean combinators and conditionals
- Effect-safe helpers around existing `Comp` API.
- Documentation of stable API signatures and behavior laws.
- Syntax ergonomics for multi-argument definitions (sugar/desugar level).

### Explicitly out of scope for this phase

- New kernel features.
- Ownership rule relaxation.
- Runtime redesign of interior mutability.
- Full trait/typeclass ecosystem.
- Full numeric hierarchy beyond `Nat`.

## Multi-Argument Functions and Syntax Compactness

### Status today

- Call side already compact:
  - `(f a b c)` works as chained application.
- Definition side is verbose:
  - nested `(lam x T (lam y U ...))`
  - nested `(pi x T (pi y U ...))`

### Plan

1. Add accepted sugar (desugars to current core forms):
- `(lam (x T) (y U) body)` -> nested unary `lam`
- `(pi (x T) (y U) R)` -> nested unary `pi`

2. Optional sugar for compact stdlib authoring:
- Arrow shorthand for non-dependent function spaces (if parser/desugar already prepared):
  - `(-> A B C)` -> `(pi _ A (pi _ B C))`

3. Keep canonical lowering unchanged:
- Core term representation remains curried/unary.
- No MIR/codegen special-cases for multi-arg functions.

4. Formatting guidance for compactness:
- Prefer one-screen definitions.
- Prefer shared helpers over deeply nested matches.
- Keep binder lists short and explicit.

## Phase Plan

### Phase S0: Bootstrap and invariants

Deliverables:
- `docs/spec/prelude_api.md` updated with stdlib migration boundary.
- `docs/dev/prelude_api_parity_report.md` includes "stdlib ownership" section.
- New guard: `prelude_impl_*` must not define shared algorithms.

Acceptance:
- CI fails if platform preludes add non-platform algorithms.

### Phase S1: Module scaffolding

Deliverables:
- Create `stdlib/std/core`, `stdlib/std/data`, `stdlib/std/control`.
- Move current pure definitions from `prelude_api.lrl` into modules where possible.
- Keep compatibility exports in `prelude_api.lrl`.

Acceptance:
- Existing programs compile unchanged.
- No API symbol disappearance.

### Phase S2: Core data APIs

Deliverables:
- `std/core/bool.lrl`: `not`, `and`, `or`, `if_nat` variants.
- `std/core/nat.lrl`: `add`, `pred`, bounded `sub`, comparisons.
- `std/data/list.lrl`: `append`, `length`, `map`, `foldr`, `foldl`.

Acceptance:
- Unit-style compile tests for each module.
- Dynamic/typed parity tests for pure overlap subset.

### Phase S3: Option/Result/Pair and ergonomics

Deliverables:
- `std/data/option.lrl`, `std/data/result.lrl`, `std/data/pair.lrl`.
- Basic combinators: `map`, `and_then`/`bind`, `unwrap_or` equivalents.
- Multi-binder `lam`/`pi` sugar shipped for stdlib authoring.

Acceptance:
- Syntax contract updated.
- Parser/desugar tests for new sugar.
- No backend divergence introduced.

### Phase S4: Control and effect adapters

Deliverables:
- `std/control/comp.lrl` utilities around `Comp`.
- Explicit boundary docs for `Dyn`/`EvalCap`/`eval` platform differences.

Acceptance:
- Shared modules compile under both backends.
- Any backend-specific behavior documented and test-gated.

### Phase S5: Law docs and quality bar

Deliverables:
- Behavioral docs for core functions (identity/associativity-like laws where relevant).
- Complexity notes (e.g., `append` linear in left list).
- Examples curated for both interpreter and compile modes.

Acceptance:
- Documentation coverage checklist passes.
- Conformance suite includes representative stdlib functions.

## Testing Strategy

1. API conformance
- Verify required symbols/types after loading API + backend impl.

2. Stdlib module compile tests
- Compile each module and representative import/usage programs.

3. Backend conformance
- For overlap subset, run same programs under dynamic + typed and compare observable output.

4. Corpus checks
- All `tests/**/*.lrl` classified as expected pass/fail.
- Ensure stdlib migration does not increase unexpected failures.

5. Syntax sugar tests
- Snapshot tests for desugaring `(lam (x T) (y U) ...)` and `(pi ...)` multi-binder forms.

## Migration Rules (important)

1. Do not break existing names in `prelude_api` during 0.1.
2. If moving a function from prelude to module, keep a stable exported alias.
3. Any semantic change requires:
- changelog note
- conformance evidence
- regression test

## Risks and Mitigations

1. Risk: accidental dual-stdlib drift
- Mitigation: enforce platform-layer guard + parity report in CI.

2. Risk: syntax sugar introduces ambiguity
- Mitigation: desugar-only implementation with strict grammar tests.

3. Risk: backend divergence in recursive/container functions
- Mitigation: conformance tests per function family (`append`, `map`, `fold*`).

4. Risk: oversized prelude_api
- Mitigation: prelude_api remains contract/export surface, logic moves to `stdlib/std/*`.

## Concrete 0.2 Success Criteria

- Shared stdlib modules exist and hold most pure algorithms.
- Platform impl preludes remain tiny and backend-specific only.
- Multi-arg definition sugar is available and documented.
- At least 20 stdlib-focused conformance tests pass under both backends.
- User guidance clearly states a single prelude API contract and stable stdlib entrypoints.

## Immediate Next Steps

1. Create `stdlib/std/core` and `stdlib/std/data` module files with current pure functions.
2. Add parser/desugar support tests for multi-binder `lam`/`pi` sugar.
3. Wire compatibility exports from `prelude_api.lrl` to new stdlib modules.
4. Extend conformance suite with stdlib function programs (`append`, `length`, `map`, `pred`).
