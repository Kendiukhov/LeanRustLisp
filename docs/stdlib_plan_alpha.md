# Stdlib Plan for Alpha

This staged plan targets a minimal but usable standard library aligned with current compiler/backend constraints.

## Milestone 0: Compiles Cleanly (Both Backends, No New Axioms)

Status: completed

### Modules to add/complete

- Keep split prelude model (`prelude_api` + backend impl layer).
- Ensure stable shared std modules are loaded from backend prelude stacks (`std/core`, `std/data`).

### Functions/types in scope

- No new effect/runtime primitives.
- Keep platform impl files small and platform-only (`eval`/boundary shims only).

### Tests

- `cli/tests/prelude_api_conformance.rs` stack assertions and API surface checks.
- `cli/src/compiler.rs` backend prelude stack unit assertions.

### Explicit deferrals

- No new runtime/interpreter features.
- No package registry/runtime fetch features.

## Milestone 1: Useful Core

Status: completed (with documented backend caveats)

### Modules to add/complete

- `std/data/option.lrl`
- `std/data/result.lrl`
- `std/data/pair.lrl`
- `std/control/comp.lrl` (minimal)
- Keep `std/data/list.lrl` complete for alpha list workflows.

### Functions/types implemented

- Option:
  - `option_map`
  - `option_and_then`
  - `option_flat_map`
  - `option_unwrap_or`
  - `option_is_some`
- Result:
  - `result_map`
  - `result_map_err`
  - `result_and_then`
  - `result_unwrap_or`
- Pair:
  - `pair_fst`
  - `pair_snd`
  - `pair_map_fst`
  - `pair_map_snd`
  - `pair_map`
- Comp:
  - `comp_pure`
  - `comp_bind`
- List (already present and kept):
  - `length`, `map`, `foldl`, `foldr`, `append`, `reverse`, `filter`

### Tests added

- Backend overlap conformance additions:
  - `tests/backend_conformance/cases/overlap/stdlib_bool_eq_truth_table.lrl`
- Typed backend stdlib smoke programs:
  - `tests/stdlib_alpha_typed/option_unwrap_some.lrl`
  - `tests/stdlib_alpha_typed/result_unwrap_ok.lrl`
  - `tests/stdlib_alpha_typed/pair_match_sum.lrl`
- Typed smoke harness:
  - `cli/tests/stdlib_alpha_typed.rs`

### Explicit deferrals

- String-first user I/O ergonomics (beyond existing prelude placeholders).
- Dynamic overlap parity for Option/Result/Pair helper-heavy programs.
- Comp helper runtime ergonomics beyond minimal constructor-level flow (module currently opt-in, not default-prelude loaded).
- Full stabilization of Option/Result helper behavior on `None`/`Err` and closure-heavy map/bind compositions in typed backend.

## Milestone 2: Ergonomics Polish

Status: planned

### Modules to add/complete

- Fill scaffold modules:
  - `std/core/logic.lrl`
  - `std/control/maybe.lrl`
- Expand helper reliability for:
  - Option/Result higher-order flows across both backends.
  - Pair helper call codegen behavior in typed backend.
  - Comp helper availability/ergonomics in CLI compile workflows.

### Functions/types to implement or harden

- Optional Eq-style convenience helpers for list/compound data once ownership/codegen constraints are resolved.
- Additional small utility combinators (without introducing advanced IO/effects).

### Tests to add

- Promote currently typed-only Option/Result/Pair helper tests into backend-overlap parity once dynamic behavior matches expected MIR semantics.
- Add explicit regression cases for helper-heavy closure/capture paths that previously triggered moved-local/inference failures.

### Explicit deferrals

- Full text/string runtime ergonomics and rich IO API.
- Concurrency/runtime effect layers beyond current placeholder surface.
