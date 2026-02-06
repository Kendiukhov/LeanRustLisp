# Red Team Fix Plan — Parallel Streams (Round 2, 2026-02-02)

This updates the parallelization plan to incorporate the closure/function‑kind direction (Fn/FnOnce). Streams are designed to avoid overlap and minimize merge conflicts.

## Stream A — Language Design: Function/Closure Kinds
- Tasks: Specify function kinds (Fn/FnOnce), capture rules, and any subtyping/coercions; decide surface syntax + core representation; formalize semantics and ownership impact.
- Files/Folders: `docs/spec`, `docs/production.md`, `frontend/src`, `kernel/src`.
- Dependencies: None (source of truth for downstream streams).

## Stream B — Kernel AST + Type System Changes
- Tasks: Extend core AST/types for function kind; update kernel checking/inference; preserve kinds in whnf/defeq; update Copy logic to respect kinds.
- Files/Folders: `kernel/src/ast.rs`, `kernel/src/type_checker.rs`, `kernel/src/normalize.rs`, `kernel/src/env.rs`, `kernel/src/whnf.rs`.
- Dependencies: Stream A (design decisions).

## Stream C — Elaboration & Surface Syntax
- Tasks: Infer closure kind from captures; implement any explicit kind annotations/defaults; preserve kind info through elaboration; add kind-mismatch diagnostics.
- Files/Folders: `frontend/src`, `cli/src` (error plumbing), `tests` (syntax samples).
- Dependencies: Stream A (syntax/semantics), Stream B (kernel representation).

## Stream D — MIR Lowering & Borrow/Ownership Integration
- Tasks: Lower closures with kind semantics (consume/mut/share env); update ownership/NLL checks; adjust any runtime checks/lints.
- Files/Folders: `mir/src`, `mir/src/borrowck`, `codegen/src`, `tests`.
- Dependencies: Stream B (kind representation), Stream C (elaboration of captures).

## Stream E — Copy Instance Hardening
- Tasks: Gate explicit `instance copy`; track Copy as unsafe/axiom deps; add kernel validation for interior‑mutable types.
- Files/Folders: `kernel/src/env.rs`, `kernel/src/ast.rs`, `frontend/src/elab.rs`, `cli/src`, `tests`.
- Dependencies: None (can proceed in parallel).

## Stream F — Axiom & Effect Boundary Tracking
- Tasks: Enforce unsafe axiom blocking in total contexts/types; verify axiom dependency tracking; harden reserved primitive gating.
- Files/Folders: `kernel/src/env.rs`, `kernel/src/ast.rs`, `kernel/src/type_checker.rs`, `frontend/src/elab.rs`, `stdlib/prelude.lrl`.
- Dependencies: None (can proceed in parallel).

## Stream G — Tests & Regression Suite
- Tasks: Add closure‑kind tests (Fn/FnOnce); add negative tests for Copy abuse; add diagnostics snapshots.
- Files/Folders: `tests`, `frontend/tests`, `cli/tests`.
- Dependencies: Streams B/C/D for kind behavior; Stream E for Copy gating.

## Stream H — Documentation & Migration
- Tasks: Update specs/docs and provide migration notes.
- Files/Folders: `docs/spec`, `docs/production.md`, `README.md` (if user‑facing changes).
- Dependencies: Stream A (design), Streams B/C/D (implementation details).
