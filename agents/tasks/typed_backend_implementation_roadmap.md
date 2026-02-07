# Document B — Typed Backend Implementation Roadmap (Codegen Engineer)

**Owner:** Codegen Engineer (typed backend)  
**Purpose:** Implement a typed backend path incrementally, using MIR as the canonical input, while retaining a dynamic backend fallback.  
**Non-goal:** Redesign MIR or borrow checking. This document assumes the MIR/NLL contract defined in Document A exists.

---

## 0. Current situation and why typed backend is incremental

You currently have a dynamic backend that compiles LRL terms to Rust using a universal `Value` enum and runtime tag checks. This is good for bootstrapping but causes:
- runtime overhead,
- panics for “wrong-tag” operations,
- hard-to-validate correctness,
- difficulty integrating NLL + typed layouts.

**Typed backend path** means:
- generate Rust enums/structs for inductives,
- generate typed functions/closures,
- eliminate backend tag-check panics for well-typed programs in the supported subset,
- keep a safe fallback to dynamic backend for unsupported features.

---

## Phase -1 (blocking): Unified pipeline and MIR contract

Before implementing typed codegen, ensure:
- The compiler pipeline is unified: source → … → MIR → borrowck → codegen.
- MIR has typed locals (`MirType`), nominal IDs, Places, CFG, and NLL artifacts (Document A).
- Macro expansion is deterministic and spans are stable.
- Golden tests exist.

**Acceptance:** `--backend dynamic` still works, but both backends consume MIR.

---

## Phase 0: Define typed backend “supported subset” + fallback behavior

### Deliverables
1) A document `docs/spec/codegen/typed-backend.md` specifying:
- Which MIR constructs are supported initially in typed backend.
- What triggers fallback to dynamic backend.
- Guarantees:
  - “No backend tag-check panics in typed subset.”
  - Explicit runtime checks are allowed only for designated constructs (bounds checks, RefCell runtime borrow violations, etc.), and must be documented.

2) CLI switch:
- `--backend typed` (error if unsupported)
- `--backend dynamic` (always works)
- `--backend auto` (typed where possible, else dynamic)

**Acceptance tests**
- A program with unsupported features falls back under auto mode, with a clear diagnostic.

---

## Phase 1: Typed representations for non-parameterized inductives (high ROI)

### Goal
Emit typed Rust for ADTs with no parameters first:
- `Nat`, `Bool`, and user-defined inductives with finite constructors and fields.

### Implementation tasks
1) Emit Rust type definitions:
- For each `AdtId` in MIR (non-param), generate:
  - `enum <Name> { ... }` with appropriate field types.

2) Emit typed expressions:
- Constructors compile to typed enum constructors.
- Matches compile to Rust `match` over enum variants.
- Let/assign compile to Rust `let` and assignments.

3) Remove backend tag checks for this subset:
- No `Value` should appear in typed backend output for these programs.

**Acceptance tests**
- Compile+run a Nat/Bool program under typed backend; output matches dynamic backend.
- Compile+run a user inductive example (e.g., Tree) under typed backend.

---

## Phase 2: Typed locals, typed calls, and closure conversion in the typed subset

### Goal
Move away from dynamic closure representation:
- compile functions to typed Rust functions or closures
- compile calls as direct calls

### Implementation tasks
1) Translate MIR function types into Rust `fn`/`impl Fn` types:
- For first pass, prefer “named functions” to avoid complex captured environments.

2) Implement closure conversion (if necessary):
- Represent closures as structs with captured fields + `impl FnOnce/FnMut/Fn`.

3) Ensure no “Expected Func” panics remain in typed subset.

**Acceptance tests**
- Programs with higher-order functions compile in typed backend subset.

---

## Phase 3: Polymorphism strategy — rely on Rust generics first

### Recommendation
If your target backend is Rust, avoid implementing full LRL monomorphization initially.
Instead:
- emit Rust generics for parametric inductives and functions,
- let rustc monomorphize.

### Implementation tasks
1) Emit parametric ADTs:
- `List<A>` → `enum List<A> { Nil, Cons(A, Box<List<A>>) }`

2) Emit polymorphic functions:
- `map : (A->B) -> List<A> -> List<B>` → `fn map<A,B>(...) -> List<B>`

3) Implement a robust `MirType -> RustType` translation:
- `Adt(AdtId, [params])` → `<Name><Rust(params)>`
- `Ref(region, T, Mut)` → references or pointer wrappers consistent with borrowck contract.

**Acceptance tests**
- `List<Nat>` and `List<Bool>` compile and run typed backend.
- `map/fold/length` examples work.

---

## Phase 4: Proof erasure becomes real (Prop elimination)

### Goal
Proof terms and Prop artifacts do not appear in runtime code.

### Implementation tasks
1) Implement erasure pass on MIR (or earlier):
- Remove all values typed as `Prop` or proof-only args.
- Ensure no runtime branching depends on proofs (kernel should already restrict this).

2) Ensure typed backend ignores erased content.

**Acceptance tests**
- Program containing proofs compiles and runs with identical runtime behavior; generated Rust contains no proof structures.

---

## Phase 5: Dependent types lowering patterns (not “Rust dependent types”)

### Goal
Support selected dependent patterns by lowering:

1) Compile-time-known indices:
- `Vec A 3` may lower to `[A; 3]` or a dedicated `Vec3<A>` wrapper.

2) Runtime indices:
- `VecDyn<A> { len: usize, data: Box<[A]> }` with invariants checked at constructors/boundaries.

### Implementation tasks
- Add lowering rules for specific indexed types.
- Avoid pretending Rust expresses `Vec<A, n>` in general.
- Integrate with borrowck Places/projections.

**Acceptance tests**
- At least one dependent-index example works in typed backend using lowering.

---

## Phase 6: Effects + capabilities mapping to typed Rust

### Goal
Translate effectful computations into explicit Rust constructs.

Implementation sketch (choose based on your effect design):
- `Comp ε A` → function taking capability tokens + returning `Result<A, E>` or similar.

**Acceptance tests**
- IO sample works under typed backend without dynamic `Value`.

---

## Phase 7: Make typed backend default (optional endgame)

Once typed backend supports the majority of programs:
- `--backend auto` defaults to typed; dynamic remains as fallback or scripting mode.
- Keep dynamic backend for debugging / REPL flexibility.

---

## Cross-cutting requirements (must be enforced throughout)

1) **No backend tag-check panics in typed subset**
- If MIR typechecks and borrowck passes, typed backend must not panic because of “wrong tag.”
- Explicit runtime checks are permitted only for documented constructs (bounds checks, RefCell runtime borrow errors, etc.).

2) **Deterministic output**
- Same MIR + same backend config => identical Rust output (modulo stable name-mangling).

3) **Structured codegen (avoid string concatenation)**
- Prefer a Rust AST builder:
  - `syn`/`quote`, or a minimal custom AST.
- This improves correctness, formatting, and safety.

4) **Stable naming and IDs**
- Use `DefId`/`AdtId`/`CtorId` for mangling, not raw strings.

---

## Deliverables checklist for the Codegen Engineer

- `docs/spec/codegen/typed-backend.md` (supported subset + fallback policy)
- `--backend typed|dynamic|auto`
- Typed ADT generation for non-param inductives
- Typed match compilation
- No tag-check panics for typed subset
- Tests: compile+run parity against dynamic backend for selected programs
- Structured codegen (AST) replacing string concatenation (as early as feasible)

---

## Definition of “done” for v0 typed backend MVP

Typed backend MVP is achieved when:
- A nontrivial subset (Nat, Bool, one user inductive, basic functions) compiles and runs via typed backend,
- typed backend produces no tag-check panics for those programs,
- auto mode falls back cleanly with good diagnostics for unsupported constructs.

---

## Implementation status audit (2026-02-06)

Phase status:
- [x] Phase -1 complete.
  - Unified MIR pipeline for both backends in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/src/compiler.rs`.
- [x] Phase 0 complete.
  - `--backend typed|dynamic|auto` implemented with typed-first fallback warnings in auto mode.
  - Backend default policy tests in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/src/compiler.rs` and `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/src/main.rs`.
- [x] Phase 1 complete.
  - Typed ADT/match/codegen parity coverage in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/tests/typed_backend.rs`.
- [x] Phase 2 complete.
  - Higher-order typed calls and closure/fix adapters covered in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/tests/typed_backend.rs`.
- [x] Phase 3 complete.
  - Parametric ADTs/functions, refs/raw pointers/interior mutability/index/runtime-check lowering in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/mir/src/typed_codegen.rs`.
  - Phase-3 scope tests in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/tests/typed_backend.rs`.
- [x] Phase 4 complete.
  - Proof erasure pass wired before codegen in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/src/compiler.rs`.
  - Erasure logic in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/mir/src/transform/erasure.rs`.
- [x] Phase 5 complete.
  - Indexed/dependent lowering paths covered by typed backend index/runtime-check tests.
- [x] Phase 6 complete.
  - Typed prelude effect/capability surface in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/stdlib/prelude_typed.lrl`.
  - Effect/capability execution tests in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/tests/typed_backend.rs`.
- [x] Phase 7 (optional) complete.
  - `compile` and `compile-mir` default to `auto` in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/src/main.rs`.

Cross-cutting status:
- [x] No dynamic `Value` tag-check path in typed subset tests (`typed_backend.rs` asserts this repeatedly).
- [x] Deterministic typed output tests are present (single-case and corpus-level determinism checks).
- [x] Structured typed codegen is in place (internal `Item`/`Stmt`/`Expr` AST plus renderer in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/mir/src/typed_codegen.rs`).
- [x] Stable unsupported reason codes (`TB001`..`TB900`) and guard tests exist.

Documentation status:
- [x] Typed backend specification: `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/docs/spec/codegen/typed-backend.md`.
- [x] Conformance subset spec: `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/docs/dev/backend_conformance_subset.md`.
- [x] Conformance report: `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/docs/dev/backend_conformance_report.md`.

Verification status:
- [x] `cargo test --all` passes on current workspace snapshot.
