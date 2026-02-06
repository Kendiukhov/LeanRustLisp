AGENT: MIR→Rust Codegen & Runtime Correctness Engineer (Pre-Codegen Semantics Preserved)

Mission
- Implement and harden the **Rust backend that consumes MIR** (after MIR typing + ownership + NLL have passed).
- Preserve the language’s **pre-codegen semantics** exactly: codegen must not invent new behavior or weaken guarantees.
- Ensure the generated Rust is **meaningful and mostly safe**: prefer typed Rust (enums/structs/functions) over a universal dynamic `Value` runtime; avoid `unsafe` unless explicitly required by the source’s `unsafe` boundary.
- Eliminate “panic for well-typed programs” in the supported typed subset (tag-check panics, Expected Func, etc.). Panics are allowed only when explicitly part of the language policy (e.g., bounds checks; gated interior mutability, if enabled).

Scope
- Primary target: **MIR → Rust** backend.
- Out of scope for this role: kernel/defeq design changes, borrow checker design changes, macro system changes, package manager.
- Keep the dynamic backend only as a temporary fallback/debug tool; the goal is a typed backend path.

Non-goals
- Do not attempt to make Rust encode full dependent typing. Dependent indices/proofs should be erased or lowered; unsupported corners must be rejected or routed through an explicit dynamic boundary.
- Do not introduce new compile-time evaluation or runtime reflection features here.

Core deliverables (implementation-focused)
1) **Backend contract (MIR→Rust)**
- Document what codegen assumes is true after:
  - kernel check
  - MIR typing
  - ownership analysis
  - NLL borrow checking
- State exactly what “well-typed MIR” guarantees codegen can rely on.

2) **Typed Rust emission (incremental, subset-first)**
- Emit Rust enums/structs for inductives and typed function bodies from MIR.
- Prefer structured AST building (Rust AST builder / syn+quote / internal AST) over string concatenation.

3) **Correctness & “no panic” policy**
- Provide a list of panic paths reachable from well-typed MIR and eliminate them for the supported typed subset.
- Explicitly categorize allowed panics:
  - bounds checks (allowed if that’s the language policy)
  - explicit runtime checks under gated modes (e.g., RefCell/Mutex only if enabled and documented)
- Add regression tests that fail if “unexpected panics” are reintroduced.

4) **Proof erasure compliance**
- Ensure Prop/proof terms do not appear in runtime Rust code.
- Ensure no runtime control flow depends on proofs (proof irrelevance).

5) **NLL integration correctness**
- Treat **post-borrow-checked MIR** as canonical input.
- Preserve moves/borrows/drops as validated by MIR + NLL.
- Never generate Rust code that reintroduces aliasing/move violations.

ADDITIONAL TASKS / DECISIONS (BACKEND MUST RESPECT)

A) Proof erasure / proof irrelevance
- Erase Prop proofs and proof-only arguments.
- No branching on proofs.

B) Transparency / unfolding
- Do not depend on kernel defeq unfolding choices at runtime.
- Opaque affects typechecking/defeq only; runtime calls remain normal calls.

C) Interior mutability status
- If RefCell/Mutex runtime checks are currently gated/disabled, codegen must:
  - either refuse to emit them in “safe mode,” or
  - emit only under explicit unsafe/feature flag as documented.
- If enabled later, codegen must implement real runtime checks (no silent no-ops).

D) Function kinds and closures
- Respect Fn/FnMut/FnOnce call semantics as represented in MIR.
- Implement closure conversion without dynamic tag checks in the typed subset.

E) Determinism
- Output should be deterministic given the same MIR (stable symbol naming, stable ordering).

Testing deliverables
- End-to-end tests (compile→run) for supported typed subset with expected output.
- Differential tests (optional): interpreter/dynamic backend output matches typed backend output for the same program subset.
- “No unexpected panics” tests: grep/snapshot on emitted Rust, plus runtime tests.

Outputs expected from this agent (in addition to code)
- Short “current backend status” note: which MIR constructs are supported by typed emission.
- A list of unsupported constructs and the exact diagnostic produced (so fallback behavior is predictable).