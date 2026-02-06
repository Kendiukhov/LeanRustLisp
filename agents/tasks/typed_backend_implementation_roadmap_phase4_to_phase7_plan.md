# Typed Backend Implementation Roadmap - Phases 4-7 Execution Plan

**Source roadmap:** `agents/tasks/typed_backend_implementation_roadmap.md`  
**Owner:** Codegen Engineer  
**Scope:** Complete remaining roadmap phases with tests and docs, while preserving existing phase 1-3 behavior.

## 0. Baseline (at start of this plan)

1. Phase 1-3 typed backend functionality is present and covered by `cli/tests/typed_backend.rs`.
2. Typed backend supports generics, refs/raw pointers/interior mutability/index/runtime-check lowering for the implemented subset.
3. Typed backend currently rejects `MirType::Opaque` / `Literal::OpaqueConst`, which blocks some proof/effect/capability scenarios.
4. Full `cargo test -p cli` has an unrelated frontend golden failure outside typed-backend scope; typed-backend integration tests are green.

## 1. Phase 4 - Proof Erasure Hardening

### Goals

1. Ensure proof artifacts are erased before typed codegen in practical proof-carrying programs.
2. Ensure typed backend does not reject proof-carrying programs solely due erased proof remnants.
3. Ensure generated Rust does not include proof-only ADT runtime structures for erased paths.

### Implementation tasks

1. Harden MIR erasure handling to avoid proof remnants leaking into typed backend support checks.
2. Extend typed backend compatibility for erased proof placeholders where needed.
3. Add typed-backend integration test with a Prop-level user inductive argument proving runtime result unchanged.
4. Add assertion that generated typed Rust does not emit proof-only ADT definitions for that test.

### Acceptance

1. Proof-carrying sample compiles under `--backend typed`.
2. Runtime output matches proof-free equivalent.
3. Generated typed Rust excludes proof-only runtime structures for the erased path.

## 2. Phase 5 - Dependent Lowering Hardening

### Goals

1. Keep dependent/indexed lowering executable and deterministic in typed backend.
2. Expand coverage from singleton indexable projection to at least one additional realistic indexable shape.

### Implementation tasks

1. Add tests for additional indexable forms (`Slice`/`Array` style wrappers over `List`).
2. Add parity test (typed vs dynamic output) for an indexed-dependent sample.
3. Add determinism assertion that indexed/runtime-check lowering output is byte-stable for identical MIR.
4. Document exact dependent lowering boundaries in `docs/spec/codegen/typed-backend.md`.

### Acceptance

1. Indexed-dependent sample runs under typed backend.
2. Typed output matches dynamic output on the selected dependent sample.
3. Determinism test passes.

## 3. Phase 6 - Effects and Capabilities Mapping (typed prelude path)

### Goals

1. Provide typed-backend-compatible prelude definitions for reserved effect/proof core names needed by user programs.
2. Ensure effect-style programs compile and run under typed backend without dynamic `Value` backend fallback.

### Implementation tasks

1. Extend `stdlib/prelude_typed.lrl` with reserved core names needed for typed workflow:
   - `List`, `Eq`, `Comp`, `False` (typed-safe minimal definitions)
2. Keep `stdlib/prelude.lrl` unchanged.
3. Keep backend-specific prelude selection explicit (`typed`/`auto` use typed prelude; `dynamic` uses legacy prelude).
4. Add typed-backend tests that compile+run simple `Comp`/capability-style programs using typed prelude definitions.
5. Add at least one test proving these programs stay on typed backend (no fallback message path).

### Acceptance

1. Program using `Comp` in typed prelude compiles+runs with `--backend typed`.
2. Reserved core names are available from typed prelude without user redefinition.
3. No dynamic backend fallback required for those tests.

## 4. Phase 7 - Typed Default Policy in Auto/CLI

### Goals

1. Make typed backend the default path for compile commands while preserving explicit dynamic fallback controls.
2. Keep diagnostics clear when unsupported constructs force fallback.

### Implementation tasks

1. Change compile command default backend from `dynamic` to `auto`.
2. Keep explicit `--backend dynamic` behavior unchanged.
3. Add/update CLI tests for default backend policy and fallback warning behavior.
4. Update docs/spec to reflect default policy.

### Acceptance

1. `compile` and `compile-mir` default to auto mode.
2. Unsupported typed cases still fall back with clear warning in auto mode.
3. Existing explicit backend flags continue to work.

## 5. Validation Plan

1. `cargo test -p mir --lib`
2. `cargo test -p cli --test typed_backend`
3. `cargo test -p cli --test pipeline_negative`
4. `cargo test -p cli`

## 6. Execution Notes

1. Keep edits limited to typed-backend files, typed prelude, relevant CLI backend-selection code, and tests/docs for these phases.
2. Do not modify unrelated stream files.
3. If unrelated failures remain, report them explicitly with file and test name after phase-targeted suites pass.

## 7. Execution Status

1. Phase 4 complete.
   - Implemented proof-runtime erasure hardening in MIR erasure and typed codegen.
   - Added regression coverage requiring a proof argument call path to compile/run under typed backend.
   - Added assertion that proof-only ADTs are absent from generated typed Rust.
2. Phase 5 complete.
   - Indexed lowering coverage includes singleton indexable and list-wrapper index projection.
   - Determinism tests for indexed/runtime-check lowering pass.
3. Phase 6 complete.
   - `prelude_typed.lrl` contains typed-safe core/effect surface (`Comp`, `Eq`, `False`, `Dyn`, `EvalCap`, `eval`).
   - Typed-backend tests execute `Comp`/`EvalCap` scenarios without dynamic runtime fallback.
4. Phase 7 complete.
   - CLI defaults for `compile` and `compile-mir` are `--backend auto`.
   - Added backend-selection tests covering default policy and explicit auto-fallback warning path.
5. Validation complete.
   - `cargo test --all -- --test-threads=1` passes.
