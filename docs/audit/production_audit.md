# LRL Production-Grade Audit Report

**Date:** January 31, 2026
**Auditor:** Production-Grade Compiler Engineer

## 1. Executive Summary

LeanRustLisp (LRL) currently exhibits the characteristics of a **research prototype** transitioning into a more serious implementation. The kernel is the strongest component, recently fortified with industrial-grade features (NbE, transparency, proof irrelevance). However, the periphery (Frontend, MIR, Codegen) suffers from significant design debt, notably disjoint compilation paths, string-based code generation, and a borrow checker that operates on core terms rather than a dedicated intermediate representation with regions.

## 2. Prototype Smells

| Component | Location | Symbol/Feature | Smell Description | Industrial Alternative |
|-----------|----------|----------------|-------------------|------------------------|
| **Codegen** | `codegen/src/lib.rs` | `Codegen::emit` | **String-based Codegen:** Generates Rust code by concatenating strings. Fragile, hard to debug, no semantic checks. | Typed IR (MIR) lowering to LLVM IR, Cranelift, or Cranelift-like structured Rust generation (e.g. `syn` + `quote`). |
| **Codegen** | `codegen/src/lib.rs` | `Value` Enum | **Dynamic Runtime:** Well-typed LRL programs compile to a dynamic interpreter (`Value::Nat`, `Value::Func`) in Rust. Loses all performance and safety benefits of compilation. | Monomorphization or vtables. Map `Nat` to `u64`/`BigInt`, `List` to structs. |
| **Codegen** | `codegen/src/lib.rs` | `panic!` usage | **Runtime Panics:** Generated code uses `panic!` for tag mismatches, even for well-typed programs (weak codegen logic). | Statically verified backend where tag checks are eliminated or handled gracefully (unreachable). |
| **MIR** | `mir/src/lib.rs` | `LocalDecl.ty` | **Core Terms in MIR:** MIR locals use `kernel::ast::Term` for types. This conflates the dependent type theory (no lifetimes) with low-level memory layout. | Dedicated `MirType` enum with explicit Regions/Lifetimes and Layout information. |
| **Borrowck** | `mir/src/analysis/borrow.rs` | `parse_ref_type` | **String Matching:** Detects references by matching `Term::Const` names "Ref", "Mut". Extremely brittle. | Use nominal type IDs (`DefId`) or specialized MIR type variants. |
| **CLI** | `cli/src/compiler.rs` | `compile_file` | **Disjoint Pipelines:** The main compiler uses the legacy string codegen. `compile_file_to_mir` is a separate, experimental path. | Unified pipeline: Source -> Kernel -> MIR -> Codegen. |
| **CLI** | `cli/src/compiler.rs` | `println!` error handling | **Ad-hoc Diagnostics:** Errors often printed directly to stdout/stderr rather than collected into structured Diagnostics. | `Diagnostic` struct collection, emitted at the end with spans (using `ariadne` consistently). |

## 3. Industrialization Roadmap

### Phase 1: Unification & Safety (Must-do)
**Goal:** Establish a single, safe compilation pipeline.
1.  **Unify Pipeline:** Make MIR the *only* path. Deprecate `codegen` crate's legacy string generator. Move `compile_file` to use MIR lowering.
2.  **Typed MIR:** Replace `kernel::ast::Term` in MIR `LocalDecl` with a `MirType` enum that supports `Ref<'a, T>`, `RawPtr`, `Int`, `Struct`.
3.  **Region Inference Stub:** Add region variables to `MirType`. Even if inference is simple initially, the data structure must exist.
4.  **Robust Borrow Checker:** Rewrite borrow checker to operate on `MirType` regions, not string matching `Term`.

### Phase 2: Performance & Backends
**Goal:** Generate efficient code.
1.  **Monomorphization:** Implement a pass to specialize polymorphic LRL functions into concrete MIR functions (eliminating `Value` enum).
2.  **LLVM/Cranelift Backend:** Replace Rust source generation with a proper backend to avoid the double-compilation overhead and dynamic dispatch of the current "transpiler".
3.  **Defeq Caching:** Add a cache to `kernel::nbe::is_def_eq` to prevent exponential blowup on repeated checks.

### Phase 3: Ecosystem
**Goal:** Developer experience.
1.  **LSP Server:** Implement a Language Server Protocol crate using the `frontend` structures.
2.  **Incremental Compilation:** Use a query-based architecture (salsa-like) instead of linear passes.

## 4. Hard Requirements Checklist (v0.1)

- [x] **Clear Kernel Boundary:** Kernel is minimal and isolated.
- [x] **Principled Equality:** NbE is implemented and robust.
- [x] **Performance Guardrails:** Transparency/Opaque logic implemented.
- [ ] **Deterministic Compilation:** MIR pipeline needs unification.
- [ ] **No Panics:** Codegen must prove panic-freedom or unsafe blocks.
- [ ] **Unified Pipeline:** Remove legacy codegen.
- [ ] **Constraint-Based Borrow Checking:** MIR must support regions.

## 5. Proposed Changes (Top 5)

### 1. Unified MIR Pipeline
**Action:** Rewrite `cli/src/compiler.rs` `compile_file` to usage `mir::lower` and `mir::codegen`.
**Delete:** `codegen/src/lib.rs` legacy `Codegen`.
**Impact:** Ensures all code goes through the same analysis passes.

### 2. Introduce `MirType`
**Location:** `mir/src/types.rs` (new).
**Action:**
```rust
pub enum MirType {
    Unit,
    Bool,
    Nat, // u64
    Ref(Region, Box<MirType>, Mutability),
    Adt(DefId, Vec<GenericArg>),
    Closure(DefId, Vec<MirType>),
}
pub enum Region {
    Static,
    Var(RegionVid),
}
```
**Impact:** Decouples MIR from Core Terms, enabling NLL and layout optimizations.

### 3. Nominal Type Identification
**Location:** `mir/src/lower.rs`.
**Action:** Instead of string matching "Ref", resolve `Ref` to a known `InductiveDecl` or intrinsic ID during lowering. Store this ID in `MirType`.
**Impact:** Robustness against renaming/shadowing.

### 4. Structured Diagnostics
**Location:** `cli/src/diagnostics.rs` (new).
**Action:** Define a central `Diagnostic` type. Update `Env`, `Elaborator`, `BorrowChecker` to return/accumulate these instead of strings.
**Impact:** Consistent error reporting, enables LSP integration.

### 5. Panic-Free Codegen Profile
**Location:** `mir/src/codegen.rs`.
**Action:** Change the output to generate Rust code that uses `Result` or `Abort` instead of `panic!` for runtime invariants (or prove them statically).
**Impact:** Production safety.

## 6. Issue List

| Severity | Subsystem | Title | Criteria |
|:---------|:----------|:------|:---------|
| **Blocker** | CLI | Unify Compilation Pipeline | `compile_file` uses MIR lowering; legacy codegen deleted. |
| **High** | MIR | Introduce `MirType` | MIR uses explicit types with regions, not `kernel::ast::Term`. |
| **High** | Borrowck | Remove String Matching | Borrow checker uses `MirType` variants/IDs, not string comparisons. |
| **High** | Codegen | Remove Dynamic `Value` | Codegen emits typed Rust (structs/enums) matching LRL types. |
| **Medium** | Kernel | Defeq Caching | `is_def_eq` caches results for `(t1, t2)` pairs. |
| **Medium** | Tooling | Structured Diagnostics | All crates emit `Diagnostic` types; CLI renders them uniformly. |
| **Low** | Kernel | Inductive Generality | Remove `Nat`/`Bool` special cases in `nbe.rs` (use generic implementation). |
