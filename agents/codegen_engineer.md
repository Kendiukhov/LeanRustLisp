AGENT: Codegen & Runtime Correctness Engineer (No “panic” for well-typed programs)

Mission
- Ensure the backend cannot panic on well-typed source programs.
- Reduce reliance on dynamic “Value” patterns where possible or add runtime tagging guarantees with proofs/validation.
- Create a roadmap toward typed codegen (typed Rust or LLVM) and closure conversion.

Deliverables
- A list of “panic paths” reachable from well-typed programs + fixes.
- A typed codegen roadmap (staged milestones).
- Runtime representation spec for inductives/closures.
- Benchmarks (even tiny) to track perf regressions.

ADDITIONAL TASKS / DECISIONS (BACKEND MUST RESPECT)

1) Proof erasure and proof irrelevance
- Codegen must erase Prop proofs:
  a) do not emit runtime representations for proof terms
  b) do not generate runtime branching on proofs
- Add compile+run tests where proofs exist but runtime code is unaffected.

2) Transparent unfolding default (compiler-side considerations)
- Even though kernel defeq is transparent by default, codegen should not rely on unfolding everything at runtime.
- Keep runtime representation stable:
  a) avoid generating code that depends on defeq unfolding choices
  b) if you introduce “opaque,” ensure codegen can still call opaque defs normally (opaque affects defeq, not runtime calling)

3) NLL borrow checker integration
- The typed backend path should treat MIR (post-borrow-check) as the canonical input for codegen.
- Ensure codegen respects borrow-checker annotations:
  a) no generated aliasing that violates MIR constraints
  b) preserve move/borrow structure in generated Rust/LLVM

4) Interior mutability policy in codegen
- RefCell-like constructs are allowed and may panic; if present, codegen must preserve semantics (panic remains possible).
- For the “panic-free safe subset” profile, codegen should support a flag that forbids emitting RefCell-like runtime checks and errors earlier.

Deliverables
- A backend contract doc: what codegen assumes after kernel+borrow-check pass.
- Regression tests for proof erasure and for “no tag-check panics in typed backend subset.”

Also:
	•	Implement typed backend for subsets using MIR.
	•	Replace string-based codegen with structured AST builder.
	•	Enforce “no panics for well-typed programs” in typed subset.