# LeanRustLisp Development Rules

## 1. Type Identification
**Rule: No string matching on type names.**

Do not check for types by comparing their names to string literals (e.g., `if name == "Nat"`).
Instead:
- Resolve the type name to a canonical definition or ID in the `Env`.
- Compare against the canonical ID or reference.
- For built-in types (Nat, Bool, List), use the `Env` to retrieve their canonical representation if checking matching.
- Ideally, lowering to MIR should resolve these to `InductiveId` or similar.

## 2. Diagnostics
**Rule: No println-based compiler errors.**

Do not use `println!` or `eprintln!` to report errors during compilation logic.
Instead:
- Use the `Diagnostic` system (defined in `frontend/src/diagnostics.rs`).
- Return `Result` types where appropriate for control flow.
- Collect diagnostics in a `DiagnosticCollector` and present them to the user at the top level.

## 3. Pipeline
**Rule: Single Compilation Spine.**

All compilation modes (File, REPL, Test) must go through the same core pipeline:
- Parse -> Elaborate -> Lower to MIR -> Optimize -> Codegen.
- Do not maintain parallel implementations of this logic.
