# Document A — Typed Backend Readiness Contract (Borrow Architect)
 
**Owner:** Borrow Checker Architect (MIR + NLL)  
**Purpose:** Define the **compiler spine contract** that makes a typed backend feasible and non-fragile.  
**Non-goal:** Implement typed codegen. This document specifies what the MIR + NLL pipeline must provide so that a Codegen Engineer can build typed backends reliably.

---

## 0. Context and decisions this contract must reflect

1. **Borrow checking is NLL/constraint-based (Rust modern style), not lexical.**
2. **Interior mutability policy (selected compromise):**
   - `RefCell`-like abstractions are **safe**, but may **panic** at runtime on borrow rule violations.
   - `Mutex`/atomics are safe concurrency primitives (no borrow panics; may block/relax semantics).
   - A **panic-free safe subset** exists as a **lint/profile**, not a language rule.
3. **Unfolding policy:** **transparent by default**, but must support an **opaque escape hatch** for compile-time performance/abstraction (even if “transparent” is default).
4. **Definitional equality:** NbE-based and deterministic (kernel-side), with transparency contexts.
5. **Pipeline spine:** One pipeline only:
   - **Source → parse → macro-expand → elaborate → kernel check → lower to MIR → NLL borrow check → codegen**

---

## 1. Phase -1: Unify the pipeline around MIR (DONE)

### Requirement
There must be **exactly one** compiler pipeline used by both:
- `cli compile_file` (batch compile)
- REPL `run_file` / interactive evaluation

### Acceptance criteria
- [x] There is no separate “legacy compile path” that bypasses MIR.
- [x] Any fallback backend still consumes MIR (or is explicitly labeled legacy and only used in `--backend dynamic` mode, not as the default pipeline).
- [x] `cli` driver and compiler both run the MIR validation pipeline (Lower -> Ownership -> Borrow -> Lint).

---

## 2. MIR data model: typed and codegen-ready (DONE)

### 2.1 MIR must have its own type language (`MirType`) (DONE)
**Hard rule:** MIR must not use `kernel::ast::Term` as “types”.

**`MirType` must cover at minimum:**
- Primitive runtime types: `Nat`, `Bool`, `Unit`, `I64`/`U64` (depending), `Ptr` if needed.
- Function types for MIR-level calls (or a call ABI abstraction).
- ADTs (inductives) by **nominal ID**, not by string name: `Adt(AdtId, Vec<MirType>)`.
- Reference types with regions and mutability:
  - `Ref(RegionVar, Box<MirType>, Mutability)`
- Optional: trait objects / Dyn boundary types:
  - `Dyn` (runtime-tagged value) if runtime eval is introduced later.
- Interior Mutability:
  - `InteriorMutable(Box<MirType>, IMKind)` where `IMKind` is RefCell, Mutex, or Atomic.

**Acceptance criteria**
- [x] The borrow checker can determine mutability and ownership rules from `MirType`, without string matching on names.
- [x] Codegen can translate `MirType` into target types without consulting kernel typing.

---

### 2.2 Nominal IDs: no name-based semantics (DONE)
Define stable IDs:
- `DefId` for definitions
- `AdtId` for inductives
- `CtorId` for constructors
- optionally `FieldId` if field access uses nominal projection

**Acceptance criteria**
- [x] Borrow checking, MIR validation, and codegen never infer semantics based on `Const("Ref")` or the string `"Mut"`.
- [x] Renaming/shadowing of user identifiers cannot break borrow checking or codegen.

---

### 2.3 Places and projections (Rust MIR-like) (DONE)
MIR must model memory locations as **Places**, not just locals:
- `Place = LocalId + Projection*`
- Projections: `Deref`, `Field(i)`, `Index(LocalId)` (or similar)

This is required for:
- NLL reasoning about aliasing through deref/field,
- typed codegen emitting field accesses safely.

**Acceptance criteria**
- [x] Borrow checking can express “borrow of field” vs “borrow of whole struct”.
- [x] Codegen can emit typed field accesses from MIR Places.

---

### 2.4 CFG-first MIR (required for NLL) (DONE)
MIR must be control-flow aware:
- Basic blocks with terminators (`Goto`, `Switch`, `Return`, `Call`, etc.)
- Explicit predecessors/successors
- Statements in blocks (`Assign`, `Borrow`, `Drop`, etc.)

**Acceptance criteria**
- [x] The borrow checker can compute liveness and region constraints across branches.
- [x] There exists a stable serialized/pretty-printed MIR form for debugging and golden tests.

---

## 3. NLL borrow checker contract (DONE)

### 3.1 Inputs
- Typed MIR (CFG + Places + MirType)
- A mapping from MIR locals/places to types and ownership categories
- Explicit borrow creation operations (see below)

### 3.2 Borrow operations must be explicit in MIR (DONE)
MIR must contain dedicated statements for borrow creation:
- `Borrow { kind: Shared|Mut, region: RegionVar, place: Place } -> LocalId`
and potentially reborrowing operations.

### 3.3 Region variables and constraints (DONE)
The borrow checker must:
- create region variables (`RegionVar`)
- generate constraints (subset/outlives) based on borrow uses and liveness
- solve constraints (NLL)
- produce either:
  - a successful assignment/solution, or
  - a diagnostic explaining conflicting loans/regions.

**Acceptance criteria**
- [x] Tests include at least 3 cases that lexical lifetimes would reject but NLL accepts.
- [x] Error diagnostics include at least:
  - borrow overlap conflict
  - use-after-move (via OwnershipAnalysis)
  - use-after-free/dropped
  - mutation while shared borrowed

---

## 4. Interior mutability classification and “panic-free safe subset” (DONE)

### 4.1 Interior mutability is allowed but explicit
The type system/MIR must be able to distinguish:
- **Static borrows** (checked by NLL)
- **Interior mutability** (runtime-checked or concurrency-checked)

Do not detect this via string matching. Use one of:
- marker traits in elaborated core lowered to MIR metadata, or
- a `MirType` tag `InteriorMutable(Box<MirType>, IMKind)` where `IMKind` distinguishes RefCell-like vs Mutex-like vs Atomic.

### 4.2 Panic-free profile
Define a linter/profile:
- `--profile panic_free_safe` (naming up to you)
- In this profile:
  - Using RefCell-like constructs is rejected or at least warned with “error-level” diagnostics.
  - Mutex/atomics are allowed.

**Acceptance criteria**
- [x] The same program compiles in default profile but is rejected/flagged in panic-free profile when using RefCell-like patterns.
- [x] Diagnostics explicitly explain “RefCell-like may panic; forbidden in panic-free profile.”
- [x] Implemented in `mir/src/lints.rs`.

---

## 5. Codegen contract output (what Borrow Architect must hand to codegen)

The borrow checker must output:
1. **Validated MIR** (no ill-typed operations, consistent Places, etc.)
2. **Borrow-check success evidence** in a stable form:
   - region solution mapping, or
   - derived non-overlap facts sufficient for codegen safety checks,
   - plus a list of loans/borrows with their live ranges (optional but ideal).
3. **An explicit list of runtime-checking constructs** present:
   - RefCell-like runtime borrow checks
   - bounds checks, etc.
   so codegen can maintain the “no backend tag-check panics” guarantee while allowing explicit runtime checks where policy permits.

---

## 6. Required tests and artifacts (owned by Borrow Architect, implemented with Tester later)

### 6.1 MIR golden snapshots
- Print stable MIR for selected inputs and store snapshots.

### 6.2 NLL acceptance/rejection corpus (DONE)
- [x] At least:
  - 10 accepted cases (covered by unit tests + existing tests)
  - 10 rejected cases (covered by unit tests + existing tests)
  including non-lexical acceptance cases.

### 6.3 No-name-dependence tests (DONE)
- Rename a user symbol `Ref` or `Mut` and ensure borrow checker is unaffected.

---

## 7. Definition of “done” for this contract (MET)

This contract is satisfied when:
- The compiler has **one pipeline** that produces **typed CFG MIR**.
- NLL borrow checking runs on MIR and produces stable diagnostics.
- MIR does not use kernel terms for types; no string matching for borrow semantics.
- Interior mutability is explicit and the panic-free profile can flag it.
- Codegen can consume MIR without re-running kernel typing or relying on `Value` tags.

---

## 8. Suggested file/module boundaries (non-binding, but recommended)

- `mir/` crate or `kernel::mir` module:
  - `mir::types` (MirType, IDs)
  - `mir::ir` (blocks, statements, places)
  - `mir::lowering` (core → MIR)
- `borrowck/` crate or module:
  - `borrowck::nll` (constraints, solver)
  - `borrowck::diagnostics`
- `profiles/` or `lints/` module:
  - panic-free profile checks
