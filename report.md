# Macro System Implementation Report

> **Last Updated**: 2026-02-01

## Current Status Summary

| Issue | Severity | Status | Notes |
|-------|----------|--------|-------|
| Kernel Panic in `unquote-splicing` | HIGH | **RESOLVED** | Fixed by handling `Meta` as neutral in NbE + unification/check fixes |
| `fix`/`letrec` Support | MEDIUM | **RESOLVED** | Implemented `Term::Fix` in Kernel and Frontend. `fix` expression works. |
| Module System | MEDIUM | **NOT STARTED** | Macros are session/file-local only |
| Quasiquote Implicit Handling | MEDIUM | **RESOLVED** | Fixed by improving implicit arg insertion in `check` |
| Snapshot Tests | LOW | **RESOLVED** | Added `insta` snapshot tests in `frontend/tests/macro_expansion_tests.rs` |
| **Hygiene (Scope Sets)** | - | **WORKING** | Fully implemented and passing tests |
| **Free Variable Hygiene** | - | **RESOLVED** | Fixed by always gensymming binders (lam, pi, match) to avoid capturing free vars with same name |
| **Basic Quasiquote/Unquote** | - | **WORKING** | Works for simple cases without splicing |
| **Unquote-Splicing** | - | **WORKING** | Now works with implicit arguments |
| **`:expand` REPL Command** | - | **WORKING** | Implemented for debugging (with trace) |
| **Macro Defining Macro** | - | **RESOLVED** | Fixed handling of macro definitions inside macros (using template style, not quasiquote code-gen) |
| **Match Parameter Instantiation** | HIGH | **RESOLVED** | Fixed `elaborate_case` to instantiate parameters and shift recursive argument types correctly. |
| **Determinism** | - | **HARDENED** | Switched to `BTreeMap` for environment/macros. Added determinism test. |
| **Tooling** | - | **WORKING** | Added `:expand` REPL command, `--show-expanded` CLI flag, and stack traces. |
| **Torture Test** | - | **PASSED** | Added nested macro hygiene test ensuring proper scope propagation. |

---

## Overview
We have successfully implemented a hygienic macro system for LeanRustLisp (LRL) based on the **Scope Sets** model (simplified). This system ensures that macro-introduced identifiers are distinct from user-defined identifiers, preventing accidental variable capture (hygiene). We also implemented quasiquoting (`quasiquote`, `unquote`, `unquote-splicing`) to facilitate macro authoring.

## Hygiene Model: Scope Sets
We chose the **Scope Sets** approach (inspired by Racket/Rust) over simple renaming because it provides a principled way to track identifier provenance and binding relationships.

### Implementation Details
*   **Syntax Objects**: The `Syntax` struct now carries a `scopes: Vec<ScopeId>` field.
*   **ScopeId**: A unique identifier generated for each macro invocation.
*   **Expansion**:
    *   When a macro is invoked, a fresh `ScopeId` is generated.
    *   Syntax introduced by the macro body (identifiers not present in arguments) is "painted" with this fresh scope using `add_scope`.
    *   Arguments passed to the macro retain their original scopes.
*   **Resolution**:
    *   During elaboration (desugaring), variables are resolved by looking up their **Name + Scope Set**.
    *   We implemented a `BTreeMap<(String, Vec<ScopeId>), String>` in `expand_with_env` to map scoped identifiers to fresh unique names (`gensym`).
    *   This ensures that `x` (user) and `x` (macro-introduced) are treated as distinct variables `x_g1` and `x_g2`.

## Changes Made
### Frontend
*   `frontend/src/macro_expander.rs`:
    *   Implemented `get_key` to canonicalize identifier keys (name + sorted scopes).
    *   Refactored `expand_with_env` to use scoped keys for environment lookup.
    *   Added support for `SyntaxKind::Hole` (`_`) in binders (`lam`, `pi`).
    *   Added `fix` and `let` support in expansion (hygienic).
    *   Enhanced `pi` desugaring to support implicit grouping syntax `(pi {n t} b)` used in the prelude.
    *   Implemented `expand_quasiquote` handling `unquote` and `unquote-splicing`.
    *   Improved `ExpansionError` to provide structured errors (ArgumentCountMismatch, InvalidSyntax).
    *   **Determinism**: Switched internal `HashMap`s to `BTreeMap` to ensure deterministic expansion order.
    *   **Tooling**: Added `expand_syntax` API and `expansion_trace` stack.
*   `frontend/src/declaration_parser.rs`: Updated to use structured `ExpansionError` and handle `None` return from expansion (for macro defs).
*   `frontend/src/elaborator.rs`:
    *   **Fixed** `unify_core` to resolve metas BEFORE checking definitional equality
    *   **Fixed** `check` to insert implicit arguments when inferred type has leading implicit Pis
    *   **Fixed** `elaborate_case` to properly handle implicit constructor parameters in pattern matching (instantiation logic)
    *   **Fixed** `elaborate_case` to shift return type for recursive arguments (IH) to handle context extension
    *   Added helper functions `extract_explicit_pi_arg_types`, `count_explicit_pi_args`, `instantiate_params`, `extract_inductive_info`

### Kernel
*   `kernel/src/nbe.rs`:
    *   **Fixed** Added `Neutral::Meta(usize)` to handle metavariables as stuck/neutral terms
    *   **Fixed** `Term::Meta` in `eval` now creates a neutral value instead of panicking
    *   **Fixed** Added `Neutral::Meta` handling in `quote` and `check_neutral_head`
*   `kernel/src/ast.rs`: Added `Term::Fix`, `Term::LetE` (LetE was already there, used it).

### CLI
*   `cli/src/repl.rs`: Added `:expand` command to visualize macro expansion. Added macro stack trace printing on error.
*   `cli/src/driver.rs`: Added meta-variable checks. Added macro stack trace printing on parsing error.
*   `cli/src/main.rs`: Added `--show-expanded` CLI flag.

### Stdlib
*   `stdlib/prelude.lrl`: Added `append` function (required for `unquote-splicing`).

## Test Results
*   **Hygiene Tests** (`tests/macro_hygiene.lrl`): **PASSED**.
*   **Quasiquote Tests** (`tests/macro_quasiquote.lrl`): **PASSED**.
*   **Comprehensive Macro Test** (`tests/macro_comprehensive.lrl`): **PASSED** (with `letrec`, `fix`, macro-generating macros, runtime lists, recursive sum).
*   **Unit Tests** (`frontend/tests/macro_expansion_tests.rs`): **PASSED** (includes determinism test, hygiene tests, quasiquote tests, nested macro torture test).

## Remaining TODOs and Risks

### 1. **Module System** (MEDIUM PRIORITY - NOT STARTED)
Macros stored in simple `BTreeMap<String, MacroDef>` with no namespace support.

---

## GitHub Issues (Updated Status)

### 1. Fix Kernel Panic in `unquote-splicing`
*   **Status**: **RESOLVED**

### 2. Implement `fix` or `letrec` Macro
*   **Status**: **RESOLVED**

### 3. Global Macro Namespace / Module System
*   **Status**: **NOT STARTED**

### 4. Verify Quasiquote Implicit Argument Handling
*   **Status**: **RESOLVED**

### 5. Add Snapshot Tests for Macro Expansion
*   **Status**: **RESOLVED**

### 6. Fix Match Parameter Instantiation
*   **Status**: **RESOLVED**
