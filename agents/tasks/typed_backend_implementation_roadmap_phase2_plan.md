# Typed Backend Implementation Roadmap — Phase 2 Execution Plan

**Source roadmap:** `agents/tasks/typed_backend_implementation_roadmap.md`  
**Phase:** 2 — Typed locals, typed calls, and closure conversion in typed subset  
**Owner:** Codegen Engineer

## 1. Phase 2 goals (from roadmap)

1. Compile MIR function values into typed Rust callables (no dynamic `Value` call path in typed subset).
2. Ensure closure conversion path is explicit and deterministic.
3. Ensure no `"Expected Func"`-style backend panics in typed subset.
4. Validate with higher-order typed backend acceptance tests.

## 2. Current baseline (before Phase 2 execution)

1. Typed backend exists in `mir/src/typed_codegen.rs` with internal AST (`Item`, `Stmt`, `Expr`) and deterministic pretty-printer.
2. Functions/closures are currently represented as `Rc<dyn Fn(..) -> ..>` in typed backend output.
3. Stage 1 tests exist (`cli/tests/typed_backend.rs`) and cover Nat/Bool/user ADT/match/fallback/determinism.
4. Dedicated Phase 2 acceptance tests for higher-order behavior are not yet comprehensive in `cli/tests/typed_backend.rs`.

## 3. Work plan

### Workstream A: Typed function-value lowering audit

1. Audit `MirType::Fn`/`FnItem`/`Closure` lowering in typed codegen:
   - `rust_type` conversion
   - call operand emission
   - constant/function reference lowering
2. Confirm all typed call sites emit direct typed calls (no dynamic tag checks).
3. If gaps are found, patch typed codegen to keep function values in typed callable form only.

### Workstream B: Closure conversion path hardening (subset)

1. Keep current closure-lifting strategy (derived closure bodies + captured values passed explicitly), because it is already integrated with MIR lowering.
2. Normalize emitted closure construction and capture passing where needed for determinism/readability.
3. Keep `FnMut` rejected in Phase 2 subset with explicit diagnostic (not silently accepted).

### Workstream C: No-tag-check policy enforcement (Phase 2)

1. Add/extend tests to assert typed backend output does not include dynamic function-tag panic artifacts.
2. Ensure higher-order typed examples run through typed backend without dynamic `Value` call machinery.

### Workstream D: Acceptance tests (Phase 2)

Add tests in `cli/tests/typed_backend.rs` for higher-order typed programs:

1. Function argument application:
   - `(apply_once f x) = f x`
2. Returning functions / closure capture:
   - e.g. const-function maker and/or adder-like closure capture
3. Function selection:
   - match/branch that returns one of two functions and applies it
4. Optional parity test:
   - typed output equals dynamic output for one higher-order program (result-level parity)

Each test should validate:
1. typed backend codegen succeeds,
2. compiled Rust runs,
3. output result is expected,
4. typed code does not include `Value::` or `"Expected Func"` markers for the typed path.

### Workstream E: Documentation update

1. Update `docs/spec/codegen/typed-backend.md` to reflect implemented Phase 2 subset:
   - higher-order support boundaries,
   - closure representation approach,
   - still-unsupported constructs (`FnMut`, refs, parametric ADTs, etc.).

## 4. Execution order

1. Implement any required typed codegen fixes found in Workstream A/B.
2. Add Phase 2 acceptance tests (Workstream D).
3. Update spec doc (Workstream E).
4. Run targeted tests:
   - `cargo test -p cli --test typed_backend`
   - fallback: run specific test names if workspace-wide compile blockers exist.

## 5. Done criteria for this execution

Phase 2 execution is complete when:

1. Typed backend handles representative higher-order programs in tests.
2. No dynamic function-tag-check paths are emitted for typed subset tests.
3. Unsupported function-kind cases remain explicit errors.
4. Phase 2 scope/status is documented in `docs/spec/codegen/typed-backend.md`.
5. Test status is reported with exact pass/fail details and blockers.

## 6. Known risk / blocker handling

1. If unrelated workspace compile failures block test execution, do not broaden scope to unrelated subsystems.
2. Still complete code + tests for Phase 2, then report verification blocker with exact file/line and failing compiler error.
