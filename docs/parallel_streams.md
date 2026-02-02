# Parallel Streams Plan

## Stream A - Kernel Soundness + Definitional Equality
- Implement strict positivity checking and integrate into `check_inductive_soundness`.
- Implement universe level constraint checks for inductives/constructors.
- Add defeq fuel + caching with a typed error on fuel exhaustion.
- Remove panics in NbE apply path; return typed errors instead.
- Enforce well-founded recursion proof checking before unfolding `WellFounded` defs.

## Stream B - Frontend Hygiene + Elaborator Metas
- Fix hygiene resolution using scope compatibility and longest-match rules.
- Preserve user scopes for macro arguments; add macro scopes only to introduced syntax.
- Implement context-aware meta unification and zonking; tie metas to their contexts.
- Add tests for hygiene (capture avoidance) and implicit-arg/meta solving.

## Stream C - MIR Borrowing + Runtime Checks
- Unify borrow checking to NLL for all bodies (including closures) and deprecate `borrow.rs`.
- Add MIR statements for runtime checks and emit them from NLL results.
- Teach codegen to emit runtime checks for `RefCell`/`Mutex`/`Bounds`.
- Remove fallback typing in lowering; surface typed errors instead of silent `Unit`.

## Stream D - Codegen Safety (Panic-Free Path)
- Replace `panic!`-based codegen paths with panic-free `Result` or typed enums.
- Generate typed inductive enums in Rust instead of dynamic `Value::Inductive` where possible.
- Add panic-free runtime tests for well-typed programs.

## Stream E - Tooling + Determinism Tests
- Add determinism test: same input => identical output hash.
- Add defeq microbench and regression budget.
- Add spec-level inductive/eliminator test suite.
- Add fuzz tests for parser + elaborator (crash-free goal).

## Dependency Notes
- Stream C depends on Stream A for a stable kernel contract.
- Stream D depends on Stream C for runtime-check plumbing.
- Stream E can run in parallel with all streams (tests can be added as changes land).
