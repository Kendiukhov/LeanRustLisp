AGENT: Borrow Checker Architect (Rust-grade Lifetimes + MIR Strategy)

Mission
- Design and implement a Rust-like borrowing story that scales.
- Decide where borrow checking lives (separate from kernel), and create a MIR suitable for it.
- Implement an MVP borrow checker (lexical first, then constraint-based / NLL-ish).

Deliverables
- MIR design doc + typing/ownership invariants.
- Borrow checker MVP plan + classic Rust test cases ported into LRL.
- A set of negative tests: use-after-free, double-mutable-alias, mutation-during-iteration, etc.
- Clear integration points: where borrow checking runs in the pipeline.

ADDITIONAL TASKS / DECISIONS (PRIMARY RESPONSIBILITY)

Decisions for this subsystem are now fixed:
1) Borrow checking must be NLL / constraint-based (Rust modern style)
   - Design MIR and borrow checker around NLL from the beginning:
     a) Build a CFG-based MIR (basic blocks, explicit control flow).
     b) Represent loans/borrows and their regions.
     c) Generate region constraints (outlives + subset + liveness).
     d) Solve constraints and produce precise error messages.
   - Do NOT implement lexical lifetimes as the final design. Lexical may exist only as a debugging mode if needed, but NLL is the target.

2) Interior mutability policy (selected compromise)
   - Define categories:
     a) RefCell-like: safe, dynamic borrow checks, may panic on violation.
     b) Mutex/atomics: safe concurrency primitives; no borrow panics (but may block).
     c) Panic-free safe subset: lint/profile that forbids RefCell-like types (and other panic-prone patterns).
   - Specify in MIR:
     - which operations create “dynamic borrow checks”
     - how interior mutability interacts with NLL (it typically bypasses static alias rules by moving checks to runtime)
   - Ensure the borrow checker:
     - remains sound even with interior mutability types present
     - clearly separates “static borrow” vs “interior mutability” patterns in diagnostics

Required deliverables
- docs/spec/mir/borrows-regions.md updated with NLL constraint model.
- docs/spec/mir/nll-constraints.md describing:
  - constraint generation
  - solving
  - error reporting strategy
- A canonical test suite mirroring Rust:
  - accepted + rejected examples
  - plus specific tests for RefCell-like behavior:
    - allowed in safe code
    - flagged by panic-free linter profile (if linter exists)

  Also:
  	•	Implement MIR with CFG + places + region variables.
	•	Implement NLL constraint generation/solving.
	•	Interior mutability classification and panic-free lint hooks (policy design).