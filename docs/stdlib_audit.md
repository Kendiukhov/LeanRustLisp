# Stdlib Audit (Alpha)

This audit reflects the current `stdlib/` tree and current CLI/backend behavior.

## Module Inventory

| Path | Status | Depends On | Notes |
| --- | --- | --- | --- |
| `stdlib/prelude_api.lrl` | working | none | Shared API contract (types, primitives, print/file surface, core constructors). |
| `stdlib/prelude_impl_dynamic.lrl` | working | `prelude_api` | Dynamic-only platform shim (`Dyn`, `EvalCap`, `eval`). |
| `stdlib/prelude_impl_typed.lrl` | working | `prelude_api` | Typed-only platform shim (`Dyn`, `EvalCap`, `eval`). |
| `stdlib/std/core/nat.lrl` | working | `prelude_api` (`Nat`, `Bool`, `add`) | `nat_pred`, `nat_sub`, `nat_{eq,lt,le,gt,ge}` implemented and covered in overlap tests. |
| `stdlib/std/core/nat_literals.lrl` | working | `prelude_api` (`Nat`) | Generated Nat literal cache for text-literal desugaring. |
| `stdlib/std/core/bool.lrl` | working | `prelude_api` (`Bool`, `not`) | `if_bool`, `xor`, `implies`, `bool_eq`. |
| `stdlib/std/core/logic.lrl` | scaffold | `prelude_api` | Placeholder module only. |
| `stdlib/std/data/list.lrl` | working | `prelude_api` + `std/core/nat` | `length`, `map`, `foldl`, `foldr`, `filter`, `reverse`; `append` comes from prelude API. |
| `stdlib/std/data/option.lrl` | partial | `prelude_api` + `std/core/bool` | `Option`, `option_{map,and_then,flat_map,unwrap_or,or,is_some,is_none}` defined. Only smoke-tested `Some`/positive flows are currently guaranteed in typed backend. |
| `stdlib/std/data/result.lrl` | partial | `prelude_api` + `std/core/bool` | `Result`, `result_{map,map_err,and_then,unwrap_or,or,is_ok,is_err}` defined. Only smoke-tested `Ok`/positive flows are currently guaranteed in typed backend. |
| `stdlib/std/data/pair.lrl` | partial | `prelude_api` | `Pair`, `pair_{fst,snd,map,map_fst,map_snd}` present. Pattern-match usage is stable; direct helper calls still expose typed codegen generic inference limitations. |
| `stdlib/std/control/comp.lrl` | partial | `prelude_api` (`Comp`, `ret`, `bind`) | Minimal `comp_pure`, `comp_bind` surface implemented. Module is currently opt-in (not auto-loaded in default backend prelude stacks). |
| `stdlib/std/control/maybe.lrl` | scaffold | none | Placeholder module only. |

## API Gaps

1. Dynamic overlap subset still does not provide reliable runtime semantics for Option/Result/Pair helper usage; overlap remains primarily Nat/Bool/List oriented.
2. `std/core/logic.lrl` and `std/control/maybe.lrl` are scaffolds with no usable APIs yet.
3. No string-first alpha I/O workflow yet beyond prelude placeholders (`print_text`, `print`, `read_file`, `write_file`) and the existing nat/bool print helpers.
4. `Comp` helper ergonomics are incomplete in CLI compile flows; `std/control/comp.lrl` remains opt-in until codegen/elaboration behavior is stabilized.
5. Pair helper runtime ergonomics need typed codegen polish for projection helper-heavy programs.
6. Option/Result helper paths outside current smoke coverage (notably `None`/`Err` and higher-order helper-heavy combinations) still hit typed backend move/capture instability.

## Compatibility Notes

### Typed backend (Stage 1)

- Stable in current tests for core Nat/Bool/List overlap and typed smoke for Option/Result positive unwrap paths plus Pair pattern matching.
- Compiles with the default split prelude stack (`prelude_api + std/core + std/data + prelude_impl_typed`).
- Pair helper-heavy direct calls still trigger generic inference/codegen issues in some programs.
- Option/Result negative/error and helper-heavy paths are not yet in the guaranteed typed subset.

### Dynamic backend

- Stable overlap subset remains Nat/Bool/List-centric.
- Option/Result/Pair helper runtime behavior is not yet reliable enough for overlap-case parity expectations.
- Uses `prelude_api + std/core + std/data + prelude_impl_dynamic`; platform shim remains intentionally minimal.

## Accidental Backend-Specific Assumptions Found

1. Assuming Option/Result helper runtime parity on dynamic currently causes false confidence; overlap tests must stay conservative.
2. Assuming Pair projection helpers are always codegen-safe on typed currently fails for some generic helper call shapes.
3. Assuming Comp helper defs are uniformly consumable by all CLI compile paths is currently unsafe.
