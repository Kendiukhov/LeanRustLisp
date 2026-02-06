# Typed Backend Implementation Roadmap - Phase 3 Execution Plan

**Source roadmap:** `agents/tasks/typed_backend_implementation_roadmap.md`  
**Phase:** 3 - Polymorphism strategy (Rust generics first)  
**Owner:** Codegen Engineer

## 1. Phase 3 goals (from roadmap)

1. Emit parametric ADTs in typed backend using Rust generics.
2. Emit polymorphic functions in typed backend using Rust generics.
3. Make `MirType -> RustType` robust for generic forms, relying on rustc monomorphization.
4. Include typed `Ref(region, T, Mut)` lowering in the Phase 3 supported subset.
5. Include typed `RawPtr`, `InteriorMutable`, indexed-place projections, and MIR runtime-check lowering.
6. Keep typed backend deterministic and free of dynamic tag-check call paths in supported subset.

## 2. Current baseline (before Phase 3 execution)

1. Typed backend currently supports non-parametric ADTs and higher-order closure/call subset.
2. `mir/src/typed_codegen.rs` currently rejects:
   - parametric ADTs,
   - `MirType::Param(_)`,
   - `MirType::Ref(_, _, _)`.
3. Phase 2 closure conversion is in place (`LrlCallable`, closure/fix adapters, typed `.call(...)`).
4. `cargo test -p cli` currently passes after Phase 2 hardening.

## 3. Scope decision and assumptions

### Recommended Phase 3 scope

1. Implement polymorphism for ADTs/functions via Rust generics.
2. Implement `Ref(region, T, Mut)` lowering directly in typed backend in this phase.
3. Implement `RawPtr`, `InteriorMutable`, indexed terms, and runtime-check constructs in typed backend.

### Borrow/pointer lowering strategy (Phase 3)

1. Introduce typed backend reference wrappers:
   - `LrlRefShared<T>` for shared borrows.
   - `LrlRefMut<T>` for mutable borrows.
2. Represent wrappers with raw pointers plus marker fields in generated Rust.
3. Lower `RawPtr<T>` as `*const T` / `*mut T` and `InteriorMutable<T, K>` as backend wrapper types keyed by `IMKind`.
4. Lower `Rvalue::Ref`, `PlaceElem::Deref`, and `PlaceElem::Index` against wrappers/helpers in codegen.
5. Lower `Statement::RuntimeCheck` kinds to explicit typed runtime helper calls.
6. Treat MIR/NLL as the source of borrow soundness; codegen should not silently relax borrow constraints.
7. If an operation cannot be represented safely in current typed subset, fail typed backend support check and use fallback/diagnostic path.

### Why

1. This matches your requested Phase 3 scope expansion and removes a major typed-backend blocker early.
2. Combining generics + refs in one phase prevents rework in `MirType -> RustType` and call/closure signatures.
3. Bundling refs/pointers/interior mutability/index/runtime checks avoids a second invasive rewrite of place/rvalue handling.

## 4. Work plan

### Workstream A: Generic type model in typed codegen

1. Add deterministic generic parameter naming strategy (`T0`, `T1`, ...).
2. Track generic parameters per emitted item (ADT, constructor helpers, defs/closures as needed).
3. Extend mini-AST type emission paths to support generic type parameters on items.

### Workstream B: `MirType -> RustType` polymorphic translation

1. Support `MirType::Param(idx)` -> generic symbol mapping in context.
2. Support `MirType::Adt(adt_id, args)` with recursive generic args.
3. Support `MirType::Ref(region, T, Mutability)` -> typed ref wrapper forms in emitted Rust.
4. Support `MirType::RawPtr(T, Mutability)` and `MirType::InteriorMutable(T, IMKind)`.
5. Support `MirType::IndexTerm(_)` in a deterministic lowered representation when required by indexed ADT identity.
6. Preserve existing function-value lowering (`Rc<dyn LrlCallable<Arg, Ret>>`) with generic/ref/pointer/interior arguments.
7. Keep unsupported-type rejection only for explicitly unimplemented opaque forms.

### Workstream C: Parametric ADT emission

1. Emit Rust generic ADTs:
   - `enum List<T0> { ... }`
2. Ensure recursive field boxing logic works for instantiated recursive fields with type args.
3. Emit constructor helpers for parametric ADTs in typed backend output.
4. Ensure deterministic item ordering and deterministic generic parameter ordering.

### Workstream D: Polymorphic function emission

1. Emit generic function signatures for typed defs where `MirType::Param` appears.
2. Ensure closure adapter generation is compatible with generic captured/argument/return types.
3. Verify curried function codegen remains type-correct under generics.

### Workstream E: Typed ref/pointer/index/runtime-check lowering in emitted Rust

1. Add typed backend runtime items for `LrlRefShared<T>` / `LrlRefMut<T>` wrappers.
2. Add typed backend runtime items/helpers for:
   - `LrlRawPtrConst<T>` / `LrlRawPtrMut<T>` shape handling (or direct raw pointers),
   - interior mutability wrappers keyed by `IMKind`,
   - index/runtime-check helpers (`runtime_bounds_check`, `runtime_index`, borrow checks).
2. Implement statement/expression lowering for:
   - `Rvalue::Ref(BorrowKind::Shared, place)`,
   - `Rvalue::Ref(BorrowKind::Mut, place)`,
   - place projection paths involving `PlaceElem::Deref`.
3. Implement lowering for place projection paths involving `PlaceElem::Index`.
4. Implement `Statement::RuntimeCheck(RuntimeCheckKind::{RefCellBorrow, MutexLock, BoundsCheck})`.
5. Ensure assignment/call/match paths that consume these operands stay typed and deterministic.
6. Keep unsupported combinations explicit (diagnostic/fallback) when they exceed current subset guarantees.

### Workstream F: Fallback and diagnostics behavior

1. Update typed support checks so parametric ADTs/functions no longer trigger unsupported errors.
2. Update typed support checks so supported `Ref` constructs no longer trigger unsupported errors.
3. Update typed support checks so `RawPtr`, `InteriorMutable`, `IndexTerm`, and runtime checks no longer trigger unsupported errors in implemented forms.
4. Keep diagnostics explicit for still-unsupported constructs.
5. Preserve `--backend auto` fallback behavior and message quality for unsupported constructs.

### Workstream G: Test expansion (Phase 3 acceptance)

Add/adjust tests primarily in `cli/tests/typed_backend.rs`:

1. Generic ADT compile/run:
   - `List<Nat>` and `List<Bool>` examples.
2. Polymorphic function compile/run:
   - `id`, `map`, `length`-style examples instantiated at concrete types.
3. Ref lowering compile/run:
   - shared and mutable borrow examples that stay in typed subset.
4. Raw pointer + interior mutability + runtime-check/index compile/run:
   - representative `borrow_shared`/`borrow_mut`,
   - representative index path with bounds runtime check.
4. Typed vs dynamic parity for one polymorphic+ref program.
5. Typed vs dynamic parity for one polymorphic+ref+index/runtime-check program.
6. Determinism test including generic item emission.
7. Unsupported-construct guard tests still fail/fallback clearly for genuinely out-of-scope combinations.

Add/adjust targeted MIR typing tests if needed:

1. Keep generic call specialization coverage.
2. Ensure no regression on labeled lifetime negative diagnostics.
3. Add/refine tests for ref-specialization boundaries (accepted vs rejected cases).

### Workstream H: Documentation update

1. Update `docs/spec/codegen/typed-backend.md`:
   - move parametric ADTs/functions and supported `Ref` forms from unsupported to supported,
   - document remaining unsupported constructs and fallback behavior.

## 5. Execution order

1. Implement generic type translation scaffolding (A + B).
2. Enable parametric ADT emission (C).
3. Enable polymorphic function emission (D).
4. Implement typed ref/pointer/index/runtime-check lowering (E).
5. Update support checks and fallback diagnostics (F).
6. Add/update tests (G).
7. Update spec doc (H).
8. Run validation suite.

## 6. Validation plan

1. `cargo test -p mir`
2. `cargo test -p cli --test typed_backend`
3. `cargo test -p cli --test pipeline_negative`
4. `cargo test -p cli`

Optional extra check:

1. Compile a standalone polymorphic sample with:
   - `cargo run -p cli -- compile <file>.lrl --backend typed`

## 7. Done criteria for Phase 3 execution

Phase 3 is complete when all are true:

1. Typed backend compiles and runs representative parametric ADT programs.
2. Typed backend compiles and runs representative polymorphic function programs.
3. Typed backend compiles and runs representative `Ref` programs in the supported subset.
4. Typed backend compiles and runs representative `RawPtr`/`InteriorMutable`/index/runtime-check programs.
5. Typed-vs-dynamic parity holds for at least one polymorphic+ref+index/runtime-check integration test.
6. Deterministic output remains stable for generic/ref/pointer/index programs.
6. `cargo test -p cli` is green.
7. Typed backend spec doc reflects Phase 3 support accurately.

## 8. Risks and mitigations

1. **Risk:** generic parameter ordering nondeterminism.
   - **Mitigation:** derive parameter order from stable index order and item-local deterministic traversal.
2. **Risk:** generic recursion emission mismatches (`Box<List<T>>` shape issues).
   - **Mitigation:** add focused recursive generic ADT tests early.
3. **Risk:** unsafe/raw-pointer ref wrapper misuse in generated Rust.
   - **Mitigation:** isolate wrapper operations behind minimal helper API and keep generation patterns narrow and tested.
4. **Risk:** over-broad type unification affecting lifetime diagnostics.
   - **Mitigation:** preserve and extend targeted negative typing tests.
5. **Risk:** runtime-helper design for interior mutability/index checks diverges from dynamic backend behavior.
   - **Mitigation:** mirror dynamic backend helper semantics and validate typed-vs-dynamic parity on focused programs.
