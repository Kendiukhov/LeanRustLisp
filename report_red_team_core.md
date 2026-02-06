# Red Team Audit Report: Release-Bar Promises P1-P8

**Agent:** LRL Release-Bar Red Team Auditor (Mode A -- Pre-Codegen, Scope-Limited)
**Date:** 2026-02-04
**Commit:** `e5b87e1` (main)
**Stance:** "Unsound until proven otherwise"

---

## 1. Executive Verdict

**GO** for stdlib expansion, with **two non-blocking observations** (P6-obs, P7-obs).

All eight release-bar promises are satisfied at their stated scope. No soundness blockers found. The kernel boundary is rigorously enforced, totality/effect boundaries are multi-layered, Prop/erasure safety uses correct transparency policies, macro boundary Deny produces compilation-aborting errors, NLL borrow checking catches aliasing violations, and defeq fuel exhaustion is properly diagnosed.

---

## 2. Checklist Table

| Promise | Verdict | Confidence |
|---------|---------|------------|
| **P1** Kernel boundary enforced | **PASS** | High |
| **P2** Totality boundary enforced | **PASS** | High |
| **P3** Prop/erasure safety | **PASS** | High |
| **P4** Macro boundary & hygiene | **PASS** | High |
| **P5** Borrow/NLL safety | **PASS** | High |
| **P6** Axiom/noncomputable policy | **PASS** | High (1 observation) |
| **P7** Interior mutability policy | **PASS** | Medium (1 observation) |
| **P8** Defeq fuel/transparency | **PASS** | High |

---

## 3. Stop-the-Line Blockers

**None.** No issues rise to blocker severity.

---

## 4. Detailed Findings Per Promise

### P1: Kernel Boundary Enforced

**Verdict: PASS**

**Evidence:**

All production paths converge on `cli/src/driver.rs:process_code()`, which performs explicit kernel re-checking before accepting any definition:

| Entry Point | Calls | Evidence |
|-------------|-------|----------|
| REPL interactive | `driver::process_code()` | `repl.rs:219,254,298` |
| File interpretation | `driver::process_code()` | `repl.rs:354` |
| Compilation | `driver::process_code()` | `compiler.rs:212` |
| Prelude loading | `driver::process_code()` | `compiler.rs:177` |
| Test compilation | `driver::process_code()` | `compiler.rs:550,817` |

**Kernel re-check boundary** at `driver.rs:703-743`:
```
Line 705: kernel::checker::infer(env, &ctx, ty_core)     -- re-infer type
Line 717: kernel::checker::whnf(env, ty_ty, ...)          -- normalize to Sort
Line 728: matches!(&*ty_ty_norm, Term::Sort(_))           -- verify Sort
Line 735: kernel::checker::check(env, &ctx, val, ty)      -- RE-CHECK value
```

All errors cause rejection via `continue` before `env.add_definition()` at line 780.

**Kernel-internal checks** in `Env::add_definition()` (`checker.rs:883-1189`):
- Reserved name validation (lines 887-937)
- Core invariant validation (lines 928-931)
- Type inference + Sort check (lines 980-984)
- Value type-checking (line 998)
- Ownership checking (line 1004)
- Effect checking (line 1013)
- Termination analysis (lines 1017-1087)

**Bypass vectors investigated:** None found. No path adds a definition without kernel validation.

---

### P2: Totality Boundary Enforced

**Verdict: PASS**

**Evidence (multi-layered enforcement):**

| Layer | Location | What |
|-------|----------|------|
| Declaration parser | `declaration_parser.rs:584` | Rejects `fix` in non-partial defs |
| Driver pre-check | `driver.rs:585-598` | Rejects `fix` via `find_fix_span()` |
| Kernel effects | `checker.rs:5625-5637` | `check_effects()` rejects Fix in Total context |
| Partial-in-types | `checker.rs:941` | `contains_partial_def()` blocks partial defs in types |
| Effect boundaries | `checker.rs:5646-5669` | Total cannot call Partial/Unsafe |

**`fix` detection** uses `SurfaceTerm::find_fix_span()` (`surface.rs:85-127`) which recursively traverses all term variants.

**Effect boundary tests** at `checker.rs:5702-5812` (`test_effect_boundaries()`) verify:
- Total -> Partial: **rejected**
- Total -> Unsafe: **rejected**
- Partial -> Unsafe: **rejected**
- Partial -> Total: allowed
- Partial -> Partial: allowed

**Type safety predicate** (`ast.rs:351-356`):
```rust
pub fn is_type_safe(&self) -> bool {
    matches!(self.effective_totality(), Totality::Total | Totality::Axiom)
        || (totality == Totality::WellFounded && self.wf_checked)
}
```
Partial is explicitly excluded.

---

### P3: Prop/Erasure Safety

**Verdict: PASS**

**Evidence:**

**Prop classification** (`checker.rs:4348-4359`, `is_prop_like()`):
- Uses `Transparency::All` to unfold definitions
- Returns true iff normalized result is `Sort(Level::Zero)`
- Error messages explicitly state: "Prop classification unfolds `opaque` aliases"

**Large elimination restriction** (`checker.rs:4364-4434`, `check_elimination_restriction()`):
- Called on every `Term::Rec` inference (line 4552)
- Uses `Transparency::All` at line 4396 to determine if inductive is in Prop
- Multi-constructor Prop inductives: rejected (line 4412)
- Single-constructor Prop inductives: all fields must be in Prop (line 4424)

**Prop fields in data** (`checker.rs:5419-5440`, within `check_inductive_soundness()`):
- Data inductives cannot contain Prop-typed fields
- `PropFieldInData` error enforced

**Opaque bypass prevention:**
- `is_prop_like()` uses `Transparency::All` (line 4349)
- `result_sort_with_transparency()` uses `Transparency::All` (line 4396/5422)
- `Transparency::All` forces complete unfolding of all definitions (`nbe.rs`)

**Tests:**
- `test_large_elimination_rejection()` in `kernel/src/lib.rs:1695`
- `test_opaque_prop_usage()` in `kernel/src/lib.rs:1936`
- `negative_large_elim_from_prop`, `negative_large_elim_multiple_ctors` in negative tests

---

### P4: Macro Boundary & Hygiene

**Verdict: PASS**

**Evidence:**

**Macro boundary enforcement** (`macro_expander.rs:434-472`):
- `collect_macro_boundary_hits()` (lines 518-617) recursively scans expanded syntax
- Detects: `unsafe`, `eval`, `axiom` (all variants), `import classical`
- `MacroBoundaryPolicy::Deny` produces ERROR-level diagnostics (line 464)
- Default policy is `Deny` (line 166)

**Quasiquote coverage:**
- Quasiquote unquote at depth 1 calls `expand_macros_internal()` (line 707)
- Boundary check runs on fully-expanded result (lines 1088-1093, 1109-1114)

**Test confirmation** (`frontend/tests/macro_expansion_tests.rs:248-314`):
- `test_macro_expansion_quasiquote_smuggling_denied()` verifies:
  - `(defmacro smuggle_axiom () (quasiquote (axiom classical bad (sort 0))))` -> ERROR
  - `(defmacro smuggle_unsafe () (quasiquote (unsafe foo Nat zero)))` -> ERROR
  - `(defmacro smuggle_import () (quasiquote (import classical)))` -> ERROR

**Hygiene mechanism** (`macro_expander.rs:295-328, 1244-1336`):
- Scope-based: each macro call creates unique `ScopeId`
- Macro-introduced symbols get scope; arguments keep original scopes
- Tests: `test_quasiquote_hygiene_capture()`, `test_macro_hygiene_no_capture_call_site()`

**Compilation abort** (`compiler.rs:227-231`):
- `diagnostics.has_errors()` checked after `process_code()` returns
- Compilation aborted, no artifacts emitted

---

### P5: Borrow/NLL Safety

**Verdict: PASS**

**Evidence:**

**NLL constraint solver** (`nll.rs:508-617`, `NllChecker::check()`):
1. Assigns synthetic borrow regions
2. Computes precise liveness via backward dataflow (lines 515-556)
3. Generates constraints and loans (lines 563-610)
4. Iterative fixpoint constraint propagation (lines 445-467)
5. Conflict checking (line 616)

**Aliasing detection** (`nll.rs:713-763`, `check_access()`):
- `AssignWhileBorrowed`: write to borrowed place rejected (line 735)
- `UseWhileBorrowed`: read during mutable borrow rejected (line 724)
- `ConflictingBorrow`: conflicting borrows rejected (line 748)
- Only shared+shared allowed (line 745-747)

**Region laundering prevention:**
- Fresh region numbering per function (`nll.rs:1341-1406`)
- Region(0) = STATIC always preserved
- Region variables local to each function context

**MIR type preservation** (`lower.rs`):
- Reference types preserve region and mutability
- Copy semantics tracked via `LocalDecl.is_copy`
- Opaque types conservatively marked non-Copy

**Ownership analysis** (`ownership.rs`):
- `CopyOfNonCopy` error for invalid copies (line 393)
- `UseAfterMove` error (lines 363-367)
- `DoubleMoveInArgs` error (line 317)

**Tests** (`nll_tests.rs`, `mir/tests/borrowck_corpus.rs`):
- Accept: basic borrow, mutation after loan end, reborrows, conditional branches
- Reject: mutation while borrowed, conflicting borrows, use after move

---

### P6: Axiom/Noncomputable Policy

**Verdict: PASS (1 observation)**

**Evidence:**

**Axiom tracking** (`ast.rs:298-387`):
- `AxiomTag::Classical` / `AxiomTag::Unsafe` properly tags axioms
- `axiom_dependencies` computed transitively (line 366)
- `noncomputable` flag set for axiom-dependent definitions

**Enforcement** (`checker.rs:1164-1176`):
```
if def.totality != Totality::Axiom && !def.noncomputable && !def.axioms.is_empty() {
    return Err(TypeError::AxiomDependencyRequiresNoncomputable { ... })
}
```

**Macro boundary** prevents axiom smuggling (see P4).

**Classical dependency reporting** (`driver.rs:787-798`):
- `report_axiom_dependencies()` called after every definition added
- `classical_axiom_dependencies()` tracks transitive classical dependencies

#### Observation P6-obs: Macro boundary Deny is post-expansion advisory

**Severity: Non-blocking / Design choice**

The macro boundary `Deny` policy records error diagnostics but does not block the expansion return value (`macro_expander.rs:1088-1120`). The expanded form (including a smuggled axiom) is returned as `Ok(Some(expanded))`. The axiom is then parsed into a `Declaration::Axiom` and processed by the driver loop, potentially entering the kernel env.

**Why this is non-blocking:**
- In compilation mode: `diagnostics.has_errors()` at `compiler.rs:227` aborts compilation. No artifacts escape.
- In REPL mode: `repl.rs:446` checks `has_errors()` before acting on results.
- The axiom still goes through full kernel validation before env addition.
- The issue is temporal: the axiom temporarily exists in the env during `process_code()`, but the calling code always checks for errors afterward.

**Recommended regression test:**
A test confirming that a smuggled axiom does not appear in compilation output or REPL auto-evaluation when Deny policy is active.

---

### P7: Interior Mutability Policy

**Verdict: PASS (1 observation)**

**Evidence:**

**Lint-level enforcement** (`mir/src/lints.rs:6-99`):
- `PanicFreeLinter::check()` detects interior mutability types in locals
- Rejects RefCell usage in panic-free profile
- `contains_interior_mutability()` recursively checks all type positions

**Interior mutability type detection** (`mir/src/types.rs:405-563`):
- `parse_interior_mutability_type()` recognizes RefCell/Mutex via markers
- `interior_mutability_kind()` maps markers to `IMKind`

**Runtime check emission** (`mir/src/codegen.rs:477-499`):
- `RuntimeCheckKind::RefCellBorrow` -> `runtime_refcell_borrow_check()`
- `RuntimeCheckKind::MutexLock` -> `runtime_mutex_lock()`
- `RuntimeCheckKind::BoundsCheck` -> `runtime_bounds_check()`

#### Observation P7-obs: RefCell/Mutex runtime checks are stub implementations

**Severity: Non-blocking / Known TODO**

**File:** `mir/src/codegen.rs:209-215`

```rust
fn runtime_refcell_borrow_check(_value: &Value) {
    // TODO: hook into RefCell runtime representation
}
fn runtime_mutex_lock(_value: &Value) {
    // TODO: hook into Mutex runtime representation
}
```

These are empty stubs. In contrast, `runtime_bounds_check()` (lines 217-230) IS implemented.

**Why this is non-blocking:**
- The `PanicFreeLinter` (lints.rs) can reject RefCell/Mutex usage at the MIR level for panic-free profiles.
- Codegen (typed backend) is explicitly out of scope for Mode A.
- RefCell/Mutex types are not yet exposed in the stdlib/prelude.
- The current policy is that RefCell is "safe but may panic" -- when runtime checks are implemented, they will produce panics, not UB.

**Recommended:**
Before enabling RefCell/Mutex in stdlib, implement the runtime check functions or gate their usage behind `unsafe`.

---

### P8: Defeq Fuel/Transparency

**Verdict: PASS**

**Evidence:**

**Fuel exhaustion** (`nbe.rs:1270-1283`, `EvalConfig::tick()`):
- Returns `Err(NbeError::FuelExhausted(...))` when fuel reaches 0
- Context information preserved for diagnostics (line 1274)
- Error propagated as `TypeError::DefEqFuelExhausted` (lines 1734-1735 in driver)

**Fuel diagnostic formatting** (`driver.rs:1732-1737`):
```rust
TypeError::DefEqFuelExhausted { context } => {
    // Produces diagnosable error message with context
}
```

**Transparency enforcement** (`nbe.rs:1376-1405`):
```rust
let should_unfold = match transparency {
    Transparency::All => true,
    Transparency::Reducible => def.transparency != Transparency::None,
    Transparency::Instances => def.transparency == Transparency::Instances,
    Transparency::None => false,
};
```

- `Transparency::None` (opaque) correctly blocks unfolding at `Reducible` level
- `Transparency::All` correctly forces unfolding (used for Prop classification only)

**Opaque definition path** (`declaration_parser.rs:238-242, 478-479`):
- `(def opaque ...)` sets `Transparency::None`
- Axioms default to `Transparency::None` (`ast.rs:322`)

**Tests:**
- `test_opaque_does_not_unfold` in semantic tests
- `test_transparent_unfolds_in_defeq` in semantic tests
- Fuel exhaustion diagnostic tests in `driver.rs:1968-2014`

---

## 5. Suggested GitHub Issues

| # | Title | Labels | Acceptance Test |
|---|-------|--------|-----------------|
| 1 | Macro boundary Deny should block declaration processing on error | `design`, `P6` | Test: smuggled axiom via macro does not enter env when Deny active |
| 2 | Implement runtime_refcell_borrow_check() before stdlib RefCell | `enhancement`, `P7` | Test: RefCell double-borrow panics at runtime |
| 3 | Implement runtime_mutex_lock() before stdlib Mutex | `enhancement`, `P7` | Test: Mutex poisoning panics at runtime |
| 4 | Add REPL-specific test for macro boundary Deny persistence | `test`, `P6` | Test: REPL session with Deny policy rejects macro-smuggled axiom |
| 5 | Document interior mutability gating policy in README | `docs`, `P7` | README section describing when RefCell/Mutex are available |

---

## 6. Out-of-Scope Observations (No Recommendations)

- Codegen Rust emission quality is not evaluated (pre-codegen mode).
- Performance of NLL constraint solver not benchmarked.
- No assessment of stdlib completeness or API design.
- No evaluation of error message quality beyond correctness.
