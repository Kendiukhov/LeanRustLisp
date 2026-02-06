# Eval/Dyn Boundary Report (2026-02-04)

## What Was Already Enforced
- **Frontend**: `SurfaceTermKind::Eval` exists and the elaborator rejects `eval` in type contexts
  (`EvalInType`).
- **Kernel**: `contains_partial_def` treats `eval` as unsafe, so it is rejected in type positions.
- **Macro system**: macro boundary checks already flagged `unsafe`/`axiom`/`import classical` forms.

## What Was Added
- **Kernel defeq hardening**: NbE now treats reserved effect names (currently `eval`) as opaque and
  will not unfold them even if a definition exists.
- **Macro boundary**: macro expansion now flags `eval` as a boundary form under the deny policy.
- **Prelude placeholders**: added `Dyn`, `EvalCap`, and `eval` (unsafe axiom) as nominal declarations.
- **Tests**:
  - `eval` in unsafe defs is accepted; `eval` in total defs is rejected.
  - prelude macro boundary test now covers `eval` injection.
  - macro expansion warning test now covers `eval`.
- **Docs**: added a mode-boundary decision note and a formal ADR.

## Where The Boundary Is Guaranteed
- **Frontend**: type-context rejection prevents `eval` from entering types.
- **Kernel**: type-safety checks reject `eval` in types; NbE/defeq keeps `eval` opaque.
- **Prelude**: macro boundary policy denies macro-smuggled `eval`/`axiom` without allowlisting.

## Not Implemented Yet (Interpreter Stage)
- Runtime evaluation semantics for `eval`.
- Dynamic value representation for `Dyn`.
- Capability enforcement beyond the placeholder `EvalCap` type.
- Any runtime I/O or reflection facilities.
