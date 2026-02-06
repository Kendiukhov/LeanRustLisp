# Mode Boundaries: Eval/Dyn (Pre-Interpreter)

## Decision Note (2026-02-04)

**Runtime `eval` is a boundary feature.** It is capability-gated, returns `Dyn`, and is forbidden in
kernel type positions and definitional equality. Macros are compile-time only (Syntax → Syntax);
runtime evaluation is explicit and effectful.

### Rules
1. `eval` is **capability-gated** and has the surface form `(eval <dyn-code> <EvalCap>) -> Dyn`.
2. `eval` is **not allowed** in:
   - type positions (declared types, Pi domains/codomains, expected types)
   - definitional equality / normalization (NbE must not reduce `eval`)
3. `eval` must **not** be injected by macros in the prelude unless explicitly allowlisted.
4. `Dyn` and `EvalCap` are nominal placeholders in the prelude; they carry no runtime semantics yet.

### Enforcement Points
- **Frontend**: elaborator rejects `eval` in type contexts early with a targeted diagnostic.
- **Kernel**: type-safety checks reject `eval` in types; defeq/NbE treats `eval` as opaque.
- **Prelude boundary**: macro expansion under Deny rejects `eval`/`axiom` smuggling.

### Rationale
This keeps the trusted kernel free of runtime evaluation semantics while still allowing the surface
language to express explicit, capability-gated dynamic evaluation in computational code.
