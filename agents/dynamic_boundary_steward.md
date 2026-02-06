AGENT: LRL Dynamic Boundary Steward (Eval/Dyn Capability Boundary — Pre-Interpreter Hardening)

Mode: Pre-codegen / pre-interpreter. You are NOT implementing a runtime interpreter. Your mission is to harden and document the *mode boundary* so future interpreter work is small and does not require refactoring core semantics.

Goal
Ensure that capability-gated runtime `eval` (returning `Dyn`) is:
- explicitly defined as a boundary feature,
- forbidden in types/definitional equality (kernel-level),
- represented in the AST/IR in a way that cannot leak into the trusted kernel,
- test-guarded and documented.

Non-goals
- Do NOT implement actual eval execution.
- Do NOT add a full effect system or runtime reflection beyond minimal placeholders.
- Do NOT expand trusted kernel semantics to “evaluate code.”
- Do NOT add major new syntax layers (readtables/frontends) here.

Deliverables
A) Decision note + ADR
1) Add a short decision note in docs/spec/mode_boundaries.md (or similar):
- `eval` is capability-gated.
- `eval` returns `Dyn`.
- `eval` is forbidden in:
  - type position
  - definitional equality / normalization / kernel computation
- macros are compile-time (Syntax→Syntax) and deterministic; runtime eval is separate and effectful.
2) Add an ADR in docs/adr/:
- “Eval is not a kernel primitive; it is a computation-only feature.”

B) Code audit (verify current behavior)
1) Find how `Eval`/`Dyn` are represented today (if at all) in:
- frontend syntax terms
- elaborated core terms
- MIR
2) Identify current checks that forbid `eval` in type position or defeq:
- kernel contains_partial_def / check_effects
- elaborator restrictions
3) Identify gaps:
- any path where `eval` can sneak into types
- any defeq evaluation that can unfold/step `eval`
- any macro expansion that could inject `(axiom ...)` or `(eval ...)` into trusted prelude without being blocked

C) Minimal code changes (small & surgical)
Implement ONLY what’s needed to enforce the boundary.

Required hardening items:
1) Kernel enforcement
- Ensure kernel rejects `eval` (or its core representation) in:
  - declared types
  - terms that are used in types
  - definitional equality reduction (NbE/whnf must not reduce eval)
2) Frontend enforcement
- Ensure elaborator rejects `eval` in type contexts early with good diagnostics.
3) Prelude boundary
- Ensure macro boundary policy prevents macros from injecting `eval` or `axiom` into the prelude unless explicitly allowlisted (prelude is Deny by default).

Optional but recommended:
4) Placeholder capability/type declarations
- Add nominal placeholder types (if not already present):
  - `Dyn` type
  - `EvalCap` capability type
- This can live in prelude/stdlib as declarations without runtime semantics.

D) Tests (must add)
1) Negative tests: forbidden positions
- `eval` in a type must fail.
- `eval` inside something that influences defeq/typechecking must fail or be rejected.
2) Positive tests: allowed positions
- `eval` in a computational position is allowed to typecheck as returning `Dyn` (execution not required).
3) Macro boundary tests (prelude)
- A macro that expands to `(eval ...)` or `(axiom ...)` inside prelude must be rejected under Deny.

E) Report
Write a short Markdown report summarizing:
- what was already enforced
- what you added
- where the boundary is guaranteed (kernel/frontend/prelude)
- what remains for the interpreter stage (explicitly list “not implemented yet”)

Acceptance criteria
- There is a clear, written, normative rule for eval/Dyn mode boundaries.
- Kernel guarantees: no eval enters types/defeq.
- Tests enforce the above and run in CI.
- Prelude macro boundary prevents macro-smuggled eval/axioms under Deny.
- No large refactors: changes should be minimal and localized.

Implementation hints (keep it small)
- If `eval` exists as a surface form, elaborate it to a core `Const` call to a runtime function returning `Dyn` under `Comp {Eval}` (even if Comp isn’t fully enforced yet).
- If `Comp` isn’t implemented yet, still enforce: `eval` cannot appear in type/defeq; treat its typing as “computational only.”
- Prefer “reject early” in elaborator + “reject always” in kernel for defense-in-depth.