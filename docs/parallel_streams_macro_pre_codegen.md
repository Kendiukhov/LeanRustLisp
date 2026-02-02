# Parallel Streams: Macro System Pre-Codegen Work

This file splits the remaining **pre-codegen** macro work into parallel, non-overlapping streams. Each stream can be done by an independent agent with minimal contention. Any cross-stream dependency is called out explicitly.

## Stream 0: Decision Lock (short, unblocker)
- Decide macro expansion target and boundaries:
  - Option A: `Syntax -> Syntax` macro expansion, then separate desugarer `Syntax -> SurfaceTerm`.
  - Option B: keep `Syntax -> SurfaceTerm` (current) but formalize/justify.
- Decide quasiquote semantics:
  - Syntax-object construction (macro-time) vs runtime list construction.
- Output a short decision note in `docs/spec/macro_system.md`.
- **Dependency:** All other streams should align to these decisions.

## Stream 1: Spec + Docs (no code changes)
- Update macro system spec to cover:
  - Attribute propagation (opaque/transparent), hygienic attributes.
  - Phase separation (compile-time macros vs runtime eval).
  - Determinism requirements + caching keys.
  - Expansion order and error/trace semantics.
  - Explicit classical logic forms and non-silent injection.
- Files:
  - `docs/spec/macro_system.md`
  - `docs/macro_system.md`
  - (Optional) `docs/spec/phase_boundaries.md` alignment.
- **Dependency:** Stream 0 decisions only.

## Stream 2: Macro Expansion Architecture (core refactor)
- If Stream 0 chooses `Syntax -> Syntax`:
  - Refactor `frontend/src/macro_expander.rs` to *only* expand to `Syntax`.
  - Add a new desugarer pass (`Syntax -> SurfaceTerm`) in a dedicated module.
  - Update `frontend/src/declaration_parser.rs` to: expand macros first, then parse/desugar.
  - Update CLI/REPL `:expand` to show pre-desugar syntax only.
- Files:
  - `frontend/src/macro_expander.rs`
  - `frontend/src/declaration_parser.rs`
  - new `frontend/src/desugar.rs` (or similar)
  - `cli/src/repl.rs`
- **Dependency:** Stream 0 decision.

## Stream 3: Hygiene + Span Remapping + Trace UX
- Implement call-site span remapping for macro-introduced syntax.
- Preserve unquote/unquote-splicing spans from inserted syntax.
- Improve macro trace output:
  - Include call stack + spans in diagnostics, not just on error.
- Add/extend tests for span preservation and macro trace output.
- Files:
  - `frontend/src/macro_expander.rs`
  - `frontend/tests/span_macro_tests.rs`
  - `frontend/tests/macro_expansion_tests.rs`
- **Dependency:** Stream 0 (if desugarer split, apply spans before desugar).

## Stream 4: Quote/Quasiquote Semantics
- Implement consistent quote semantics for symbols/strings (no `Hole`).
- Implement quasiquote/unquote/unquote-splicing per chosen model:
  - Syntax-object construction preferred for hygienic macros.
- Update or remove stale helper code (`frontend/src/quasiquote_helper.rs`).
- Update macro expansion snapshots.
- Files:
  - `frontend/src/macro_expander.rs`
  - `frontend/src/quasiquote_helper.rs`
  - `frontend/tests/*macro*`
- **Dependency:** Stream 0 decision; minimal overlap with Stream 3.

## Stream 5: Macro Environment Scoping + Imports
- Define macro environment scoping rules (module/file-scoped, import-based).
- Add explicit surface forms for macro imports (if needed).
- Ensure deterministic environment versioning (for caching/fixed expansion order).
- Files:
  - `frontend/src/macro_expander.rs`
  - `frontend/src/declaration_parser.rs`
  - `cli/src/driver.rs` (if import affects pipeline)
- **Dependency:** Stream 0 decision (macro target), and may need coordination with Stream 2.

## Stream 6: Surface Syntax for Attributes / Eval / Classical
- Add surface forms that macros can emit safely:
  - `opaque`/`transparent` def attributes (already parsed directly, but ensure macro output can express them).
  - capability-gated `(eval <dyn-code> <EvalCap>) -> Dyn` syntax placeholder.
  - explicit classical forms (`import classical` or tagged `axiom` forms).
- Add macroexpand snapshot tests for these forms.
- Files:
  - `frontend/src/declaration_parser.rs`
  - `frontend/src/macro_expander.rs` (if syntax requires expansion support)
  - `frontend/tests/*macro*` and `cli/tests/*golden*`
- **Dependency:** Stream 0 decision; minor overlap with Stream 5 (import handling).

## Stream 7: Tooling + CLI UX
- Add REPL/CLI commands:
  - `:expand-1`, `:expand-full`, `:trace-expand`.
- Add stable pretty printer for `Syntax` (if needed for tooling output).
- Add snapshot tests for expanded output and traces.
- Files:
  - `cli/src/repl.rs`
  - `frontend/src/surface.rs` (pretty print enhancements)
  - `cli/tests/snapshots/*`
- **Dependency:** Stream 2 decision (macro target), minimal overlap otherwise.

---

### Notes on Non-Overlap
- Stream 2 is the largest refactor; avoid working in `frontend/src/macro_expander.rs` concurrently with Streams 3–6.
- Streams 1 and 7 can run in parallel with any code stream once Stream 0 is decided.
- Streams 3 and 4 both touch expansion logic; run sequentially or split by file ownership.
