# Pre-Codegen Production-Grade Audit (From Scratch)

Date: 2026-02-06
Scope: `kernel`, `frontend`, `mir`, pre-codegen `cli` driver/pipeline
Out of scope for this pass: backend/runtime codegen details

## Verification baseline

- Ran `cargo test -p kernel --lib`: PASS (64/64)
- Ran `cargo test -p frontend --lib`: PASS (13/13)
- Ran `cargo test -p mir --lib`: PASS (106/106)
- Ran `cargo test -p cli --lib`: FAIL (1 failing test)
  - `compiler::tests::test_append_fnonce_compiles`
  - Failure shows MIR typing mismatch with generic params vs concrete args in closure call path.

---

## A) Prototype Smells (specific)

### 1) Generic call typing rejects valid monomorphic applications (blocker)
- Files:
  - `mir/src/analysis/typing.rs:165`
  - `mir/src/analysis/typing.rs:665`
  - `cli/src/compiler.rs:1065`
- Symbols:
  - `TypingChecker::check_call`
  - `TypingChecker::types_compatible_inner`
  - `test_append_fnonce_compiles`
- Smell:
  - `MirType::Param(_)` is only compatible with `MirType::Param(_)`, not with instantiated concrete types (`Nat`, `Adt(...,[Nat])`). This breaks legitimate generic calls in lowered MIR.
- Industrial alternative:
  - Introduce local type substitution / unification for call checking (`Param(i)` binds to actual once per call), then validate return type under that substitution.

### 2) Macro expansion cache invalidation is collision-prone and incomplete
- Files:
  - `frontend/src/macro_expander.rs:365`
  - `frontend/src/macro_expander.rs:368`
  - `frontend/src/macro_expander.rs:371`
- Symbols:
  - `Expander::macro_env_version`
- Smell:
  - Cache version is a `wrapping_add` of current module + direct imports only. This can collide and ignores transitive import dependency changes. `env_version` is incremented but not used in this key.
- Industrial alternative:
  - Use a deterministic structural fingerprint over transitive module dependency graph (module id + module version tuple hash), then key cache invalidation off that fingerprint.

### 3) Panic paths still exist in production pre-codegen flows
- Files:
  - `frontend/src/parser.rs:350`
  - `mir/src/lower.rs:2018`
  - `cli/src/repl.rs:19`
  - `cli/src/repl.rs:86`
  - `cli/src/repl.rs:324`
  - `cli/src/compiler.rs:262`
- Symbols:
  - integer parsing in `Parser::parse_primary`
  - borrow lowering in `LoweringContext::lower_term`
  - REPL setup/history path
  - diagnostic printer path
- Smell:
  - Overflow integer parse can panic (`parse().unwrap()`), and multiple `expect/unwrap` paths can abort process.
- Industrial alternative:
  - Replace with structured errors carrying spans/source context and emit diagnostics; never panic for user input/tooling failures.

### 4) Driver has O(N^2)-style scaling behavior per declaration
- Files:
  - `cli/src/driver.rs:962`
  - `cli/src/driver.rs:1009`
- Symbols:
  - `process_code`
  - `env.clone()` checkpoint per def
  - `IdRegistry::from_env(&env)` per admitted def
- Smell:
  - Full env clone + full id registry rebuild for each declaration scales poorly as stdlib/project size grows.
- Industrial alternative:
  - Batch validation with incremental snapshots and incremental `IdRegistry` updates (or single rebuild per compilation unit).

### 5) Macro/declaration parser leaks debug noise to stdout
- Files:
  - `frontend/src/declaration_parser.rs:120`
  - `frontend/src/declaration_parser.rs:123`
- Symbols:
  - `DeclarationParser::parse_decl`
- Smell:
  - Parser emits raw debug `println!` on errors, polluting CLI/tool output and making diagnostics non-composable.
- Industrial alternative:
  - Route all parse/expansion failures through `DiagnosticCollector` only.

### 6) Defeq cache has no budget/eviction and no perf benchmark guardrail
- Files:
  - `kernel/src/nbe.rs:1290`
  - `kernel/src/nbe.rs:1872`
  - `kernel/src/nbe.rs:1889`
- Symbols:
  - `DefEqConfig.cache`
  - `eval_with_cache`
- Smell:
  - Unbounded per-check cache without metrics/limits can produce memory and latency cliffs on large terms.
- Industrial alternative:
  - Add configurable cap/eviction and expose cache hit/miss/fuel counters; gate regressions with microbench tests.

### 7) Transparency policy for Prop checks unfolds opaque aliases in core checks
- Files:
  - `kernel/src/checker.rs:5010`
  - `kernel/src/checker.rs:5019`
  - `kernel/src/checker.rs:6133`
- Symbols:
  - `check_elimination_restriction`
  - `PropTransparencyContext::UnfoldOpaque`
- Smell:
  - Core restriction checks default to unfolding opaque aliases, weakening opacity boundaries and making behavior sensitive to reduction policy.
- Industrial alternative:
  - Keep `Opaque` default for kernel-level judgments; use explicit, narrowly-scoped override contexts where required by spec.

### 8) Equality eliminator exception is kernel-special-cased
- Files:
  - `kernel/src/checker.rs:5063`
  - `kernel/src/checker.rs:5605`
- Symbols:
  - `is_equality_inductive`
- Smell:
  - Kernel contains explicit shape recognition for Eq-style exception. This is extra trusted logic and expands TCB complexity.
- Industrial alternative:
  - Move exception criteria into principled kernel rule abstraction with machine-checkable predicate module and dedicated tests/spec references.

### 9) Lowering uses unsafe raw pointer guard for span restoration
- Files:
  - `mir/src/lower.rs:266`
  - `mir/src/lower.rs:274`
  - `mir/src/lower.rs:1629`
- Symbols:
  - `SpanRestore`
  - `LoweringContext::enter_term_span`
- Smell:
  - Uses `unsafe` for mutable span restoration in a path that should be representable safely.
- Industrial alternative:
  - Replace with safe scoped API (explicit `with_term_span` closure) to avoid raw pointer lifetime assumptions.

### 10) Borrow diagnostics context is incomplete in some conflict paths
- Files:
  - `mir/src/analysis/nll.rs:1177`
  - `mir/src/analysis/nll.rs:1185`
  - `mir/src/analysis/nll.rs:1197`
- Symbols:
  - `check_call_borrow_access_conflict`
- Smell:
  - Several borrow errors emit `BorrowErrorContext::default()` instead of full loan/region chain context.
- Industrial alternative:
  - Always attach loan issuance + region chain evidence for user-actionable conflict diagnostics.

### 11) Runtime-check collection is quadratic on body size
- Files:
  - `mir/src/analysis/nll.rs:1881`
  - `mir/src/analysis/nll.rs:1908`
- Symbols:
  - `collect_runtime_checks`
  - `collect_runtime_checks_for_type`
- Smell:
  - Scans all statements for each local/type recursively; this can blow up on large MIR bodies.
- Industrial alternative:
  - Precompute local use-sites once and reuse, or collect checks in a single traversal.

### 12) Panic-free profile policy is coarser than selected interior mutability compromise
- Files:
  - `mir/src/lints.rs:21`
  - `mir/src/lints.rs:84`
  - `cli/src/driver.rs:1144`
- Symbols:
  - `PanicFreeLinter::check`
  - panic-free runtime-check gate
- Smell:
  - Panic-free mode currently rejects all interior mutability and all runtime checks; this also blocks `Mutex/Atomic` cases that are not borrow-panics by nature.
- Industrial alternative:
  - Keep RefCell borrow-panic bans strict; separate policy buckets for Mutex/Atomic in panic-free profile.

### 13) NBE reduction still contains unchecked unwrap in const unfolding path
- Files:
  - `kernel/src/nbe.rs:1378`
  - `kernel/src/nbe.rs:1381`
- Symbols:
  - const branch in `eval_with_config`
- Smell:
  - Uses `def.value.as_ref().unwrap()` after guard checks; invariant break would panic inside kernel execution path.
- Industrial alternative:
  - Pattern-match `Option` directly and convert invariant failures to internal typed errors.

### 14) Tooling diagnostics model is too thin for industrial integrations
- Files:
  - `frontend/src/diagnostics.rs:22`
  - `frontend/src/diagnostics.rs:77`
- Symbols:
  - `Diagnostic`
  - `DiagnosticCollector`
- Smell:
  - Flat structure lacks richer machine-readable categories, related spans, and remediation metadata.
- Industrial alternative:
  - Introduce structured diagnostic schema contract (category, primary span, related spans, notes/help ids).

### 15) Fuzzing surface is narrow
- Files:
  - `fuzz/fuzz_targets/nll_checker.rs:1`
- Symbols:
  - only NLL fuzz target exists
- Smell:
  - No fuzz harnesses for parser/macro/elaboration/kernel reduction paths where malformed input and reduction edge cases live.
- Industrial alternative:
  - Add fuzz targets for parser + macro expander + elaborator + defeq/NBE normalization.

### 16) Key pre-codegen modules are monolithic and multi-responsibility
- Files:
  - `kernel/src/checker.rs` (~6986 LOC)
  - `frontend/src/elaborator.rs` (~3848 LOC)
  - `mir/src/lower.rs` (~3493 LOC)
  - `cli/src/driver.rs` (~2462 LOC)
- Symbols:
  - central modules owning many concerns
- Smell:
  - Large files raise change risk, reduce reviewability, and enlarge effective TCB surface.
- Industrial alternative:
  - Split by bounded responsibilities with small interfaces (kernel judgments, elaboration constraints, lowering sub-passes, pipeline orchestration).

### 17) REPL module initialization and history handling can hard-fail session
- Files:
  - `cli/src/repl.rs:19`
  - `cli/src/repl.rs:324`
- Symbols:
  - `start`
- Smell:
  - Editor/history IO errors can panic/terminate rather than degrade gracefully.
- Industrial alternative:
  - Fall back to stateless REPL mode with warnings.

### 18) Compiler diagnostic rendering can panic on output failures
- Files:
  - `cli/src/compiler.rs:262`
  - `cli/src/repl.rs:436`
- Symbols:
  - diagnostic print pipeline
- Smell:
  - `print(...).unwrap()` aborts on sink failures (pipe closed, terminal IO issues).
- Industrial alternative:
  - Best-effort print with non-fatal fallback (`eprintln!` + continue).

---

## B) Industrialization Roadmap

### Phase 1: Must-do refactors before stdlib expansion

Tasks:
1. Fix generic call typing (`MirType::Param` substitution) and close `test_append_fnonce_compiles`.
2. Remove production `unwrap/expect` panic paths in parser/lowering/cli diagnostics/repl.
3. Replace macro cache version scheme with transitive dependency fingerprint.
4. Stabilize declaration parsing output by removing debug `println!` side channel.
5. Clarify kernel transparency policy boundaries for Prop checks and codify Eq exception rule.

Dependencies:
- Typing fix depends on agreement of MIR generic semantics (`Param` binding strategy).
- Transparency policy work depends on kernel boundary spec updates.

Estimated risk:
- Medium to high (typing and transparency are semantics-adjacent).

Acceptance tests:
- `cargo test -p cli --lib` all green (including `test_append_fnonce_compiles`).
- New regression tests for parser integer overflow and lower-term borrow app malformed path.
- Macro cache tests proving transitive import changes invalidate cache deterministically.

### Phase 2: Performance and determinism upgrades

Tasks:
1. Remove per-definition full `IdRegistry::from_env` rebuild and reduce env snapshot cloning.
2. Optimize NLL runtime-check collection to near-linear pass.
3. Add defeq cache telemetry (hits/misses/size/fuel events) and bounded cache config.
4. Add microbench harness for defeq hotspots and macro expansion.

Dependencies:
- Phase 1 typing stabilization first (to avoid optimizing unstable semantics).

Estimated risk:
- Medium.

Acceptance tests:
- Benchmark baselines committed; CI gate on relative regression thresholds.
- Determinism regression suite includes cache invalidation and artifact ordering checks.

### Phase 3: Tooling and ecosystem readiness

Tasks:
1. Expand diagnostic schema for LSP/CI consumption (stable codes + related spans + notes).
2. Add parser/macro/elaborator/kernel fuzz targets.
3. Split monolithic files into scoped modules with explicit interfaces.
4. Produce pre-codegen architecture docs aligned with implementation boundaries.

Dependencies:
- Phase 1 and 2 stabilized APIs.

Estimated risk:
- Medium.

Acceptance tests:
- Fuzz targets run in CI for budgeted time and remain crash-free.
- LSP-style JSON diagnostic contract snapshots are stable.
- Architectural module boundaries documented and enforced by crate/module ownership tests.

---

## C) Hard Requirements Checklist for v0.1 Core

- Deterministic compilation (same input -> same output): PARTIAL
  - Strong sorting discipline exists in many places, but macro cache versioning is not robust (collision + transitive dependency blind spots).

- Stable error categories and spans: PARTIAL
  - Diagnostic codes/spans are present broadly, but some paths still emit raw debug output or incomplete context.

- No panics from well-typed programs in default backend: PARTIAL/FAIL-RISK
  - Multiple production `unwrap/expect` sites remain in pre-codegen pipeline/REPL tooling.

- Clear kernel boundary (minimal TCB): PARTIAL
  - Kernel has principled core machinery, but special-case Eq elimination and broad transparency exceptions increase trusted complexity.

- Definitional equality is principled (NbE or equivalent): PASS with caveats
  - NbE-based defeq is implemented with fuel and cache, but lacks benchmark guardrails and bounded cache policy.

- Inductives/eliminators generality (no Nat/Bool/List semantic special casing): PARTIAL
  - Significant progress via shared recursor metadata; equality exception remains special-cased in kernel logic.

- Performance guardrails (transparency/fuel/cache): PARTIAL
  - Fuel policy exists and is surfaced, but no benchmark CI and no cache budget controls.

- Treat `panic!` in compiler/generated code as failure by default: PARTIAL
  - Good direction, but pre-codegen still has panic-capable paths (`unwrap/expect`) requiring cleanup.

### Additional decisions audit

- NLL-ready MIR requirements:
  - CFG/basic blocks: PASS (`mir` body + basic block model present)
  - Region constraints: PASS (`RegionInferenceContext` with outlives + liveness)
  - Constraint-conflict diagnostics: PARTIAL (some paths still drop rich context)

- Panic-free profile definition/enforcement:
  - Present as profile/linter: PASS
  - Current enforcement granularity vs selected compromise: PARTIAL (currently too coarse for Mutex/Atomic scenarios)

- Transparent-by-default unfolding with guardrails:
  - Opaque/transparent controls: PASS
  - Bounded defeq unfolding/fuel: PASS
  - Defeq performance benchmark guardrails: FAIL (missing)

---

## D) Top 5 Concrete Proposed Changes (PR-ready)

### Top 1: Fix generic call typing substitution in MIR checker

Files/modules:
- `mir/src/analysis/typing.rs`

Exact change:
1. Introduce per-call substitution map: `HashMap<usize, MirType>`.
2. In `check_call`, when expected param is `MirType::Param(i)`, bind `i -> arg_ty` if unbound; else require compatibility with existing binding.
3. Apply substitution to remaining param/return type before subsequent argument and destination checks.
4. Keep function-kind checks unchanged.

Pseudo-code:
```rust
let mut subst = HashMap::<usize, MirType>::new();
for arg in args {
    let expected = apply_subst(param_ty, &subst);
    let actual = operand_type(arg);
    if !unify_param_aware(&expected, &actual, &mut subst) { error(...) }
}
let expected_ret = apply_subst(&current_ty, &subst);
```

Tests to add/update:
- Promote `test_append_fnonce_compiles` to mandatory regression.
- Add MIR typing unit test with `Param`-to-concrete argument and concrete return destination.

### Top 2: Remove panic paths from pre-codegen production flows

Files/modules:
- `frontend/src/parser.rs`
- `mir/src/lower.rs`
- `cli/src/repl.rs`
- `cli/src/compiler.rs`

Exact change:
1. Replace `s.parse().unwrap()` with parse error variant (e.g. invalid/overflow integer literal + span).
2. Replace `args.last().expect(...)` with guarded error return in lowering.
3. Replace REPL/compiler `print(...).unwrap()` and history `unwrap()` with best-effort logging and non-fatal continuation.

Tests:
- Parser regression for oversized integer literal.
- Lowering regression for malformed borrow app shape returns diagnostic, not panic.
- REPL/diagnostic printer resilience tests (inject failing writer mock where feasible).

### Top 3: Rebuild macro cache invalidation around dependency fingerprints

Files/modules:
- `frontend/src/macro_expander.rs`

Exact change:
1. Replace `macro_env_version` sum with deterministic fingerprint of transitive dependency graph rooted at `current_module`.
2. Include `(module_id, module_version, imported_module_ids...)` in hash input with sorted traversal.
3. Remove dead/unused `env_version` or integrate it into fingerprint contract explicitly.

Tests:
- Transitive import invalidation test: A imports B imports C; mutate C macro; ensure A cache invalidates.
- Collision resistance sanity test across synthetic module/version combinations.

### Top 4: Remove O(N^2) driver behavior in declaration processing

Files/modules:
- `cli/src/driver.rs`
- `mir/src/types.rs` (if incremental API is added)

Exact change:
1. Build `IdRegistry` once per compilation batch, then update incrementally on accepted declarations.
2. Replace full `env.clone()` checkpoint per def with scoped rollback artifacts (new definition id + span-map delta + artifact index rollback), not full environment clone.

Tests:
- Large synthetic module benchmark test for declaration count scaling.
- Functional equivalence tests: rollback behavior identical under error paths.

### Top 5: Align panic-free profile with interior mutability compromise + improve borrow context

Files/modules:
- `mir/src/lints.rs`
- `cli/src/driver.rs`
- `mir/src/analysis/nll.rs`

Exact change:
1. Split runtime-check categories into panic-prone vs non-panic-prone.
2. In panic-free mode, reject RefCell borrow-violation checks; allow Mutex/Atomic paths (policy decision, if approved).
3. Replace `BorrowErrorContext::default()` in call-conflict paths with full context from active loan source.

Tests:
- Panic-free policy matrix tests for RefCell/Mutex/Atomic.
- Borrow diagnostic snapshots include region chain and loan origin for call-conflict errors.

---

## E) Non-goals / Deliberate Tradeoffs

1. Do not over-engineer full global inference or higher-order unification before stabilizing current first-order meta + constraint model.
2. Do not move macro system complexity into kernel. Keep kernel small; enforce macro safety in frontend/driver boundary checks.
3. Do not build full incremental compilation database before removing obvious O(N^2) local costs.
4. Do not over-abstract MIR passes yet; first split by correctness-critical boundaries, then tune abstractions after profiling.
5. Keep Eq exception work scoped: formalize current behavior before broadening elimination expressivity.

Complexity placement guidance:
- Kernel: only proof-critical typing/reduction invariants.
- Frontend: parsing, macro hygiene/staging, elaboration heuristics, user diagnostics.
- MIR: ownership/NLL constraints and checkable evidence.
- Tooling/CLI: orchestration, diagnostics formatting, artifact/reporting contracts.

---

## Issue list (proposed GitHub issues)

1. `[blocker][mir] Fix generic call typing substitution for MirType::Param`
   - Acceptance: `test_append_fnonce_compiles` passes; new MIR typing regression covers param-to-concrete call.

2. `[high][frontend] Replace integer parse unwrap with spanful parse error`
   - Acceptance: oversized integer literal no longer panics; diagnostic code + span emitted.

3. `[high][mir] Remove lowering panic on borrow_* argument extraction`
   - Acceptance: malformed borrow app returns `LoweringError` with span; no `expect` path remains.

4. `[high][frontend] Eliminate stdout debug prints from DeclarationParser`
   - Acceptance: parse failures only appear via diagnostics collector; no raw `println!` in parse path.

5. `[high][frontend] Rework macro cache invalidation to transitive dependency fingerprint`
   - Acceptance: transitive import mutation invalidates cache deterministically.

6. `[high][cli] Remove unwrap-based hard failures in diagnostic rendering`
   - Acceptance: closed output sink does not panic compiler/repl.

7. `[high][cli] Make REPL startup/history failures non-fatal`
   - Acceptance: REPL runs in degraded mode when history/editor setup fails.

8. `[high][cli] Remove per-definition IdRegistry rebuild in process_code`
   - Acceptance: one-batch or incremental registry path; benchmark shows improved scaling.

9. `[high][cli] Replace full env clone rollback with scoped rollback metadata`
   - Acceptance: rollback semantics preserved; reduced per-definition overhead.

10. `[med][kernel] Replace NBE const unfolding unwrap with checked branch`
    - Acceptance: no unwrap in `eval_with_config` const unfolding path.

11. `[med][kernel] Revisit Prop transparency default in elimination checks`
    - Acceptance: policy documented and tests verify intended opaque behavior.

12. `[med][kernel] Isolate/justify Eq elimination exception with explicit spec link`
    - Acceptance: dedicated module/tests/spec section for Eq exception invariant.

13. `[med][mir] Always attach loan/region context in call-conflict borrow errors`
    - Acceptance: diagnostics include loan origin + region chain in those paths.

14. `[med][mir] Optimize runtime-check collection to avoid O(locals*statements)`
    - Acceptance: single-pass or indexed collection with equivalent output.

15. `[med][mir] Align panic-free profile with interior mutability class policy`
    - Acceptance: policy matrix tests for RefCell vs Mutex/Atomic pass per approved rules.

16. `[med][kernel] Add defeq cache metrics and optional cache budget`
    - Acceptance: expose cache counters; bounded mode available and tested.

17. `[med][tooling] Add defeq and macro expansion microbench harness`
    - Acceptance: CI benchmark task with regression thresholds/checkpoints.

18. `[med][tooling] Add fuzz targets for parser/macro/elaborator/kernel-NbE`
    - Acceptance: fuzz targets compile and run in CI budget without crashes.

19. `[low][mir] Remove unsafe raw-pointer span guard in lowering`
    - Acceptance: safe scoped span API replaces `SpanRestore` unsafe block.

20. `[low][frontend/tooling] Extend diagnostic schema for machine-readable tooling`
    - Acceptance: diagnostics carry category/related spans/help metadata and remain backwards compatible.
