AGENT: Kernel Guardian (TCB Minimizer + Definitional Equality Specialist)

Mission
- Make the kernel truly tiny and trustworthy.
- Specify and implement definitional equality robustly (prefer NbE or a disciplined normalizer).
- Ensure inductives/eliminators are general and correct.
- Enforce the total fragment boundary so typechecking cannot depend on nontermination/effects.

Deliverables
- A “Kernel Boundary” document: what is trusted and why.
- Refactor proposal (or PR) that removes parsing/macro/elaboration from kernel.
- A definitional equality test suite (β/δ/ι/ζ + transparency rules).
- A clear story for Prop/Type levels and Pi universe rules.

ADDITIONAL TASKS / DECISIONS (MUST FOLLOW)

New decisions to enforce at the kernel/spec level:
1) Unfolding policy: TRANSPARENT (selected)
   - Implement transparency controls for definitions, with default behavior being transparent unfolding in definitional equality (δ-reduction) under the standard transparency context.
   - However: even with “transparent by default,” you must still implement a mechanism to prevent definitional equality from exploding (Lean uses transparency levels and allows marking defs opaque).
   - Concrete requirements:
     a) Env must store per-Const transparency metadata (Transparent vs Opaque).
     b) Definitional equality (NbE) must accept a “transparency context” parameter.
     c) Provide a way to mark certain definitions Opaque for performance/abstraction (even if default is Transparent). This is necessary for scalability.
   - Add tests: transparent def unfolds; opaque def does not unfold (baseline).

2) Proof irrelevance (selected)
   - Enforce computational irrelevance of Prop proofs:
     a) Restrict elimination from Prop into Type: disallow pattern matching / computation that depends on proof structure to produce runtime data.
     b) Document and implement a clear rule: proofs may justify typing, but cannot influence runtime computation.
   - Add negative tests: program attempting to branch on a proof to produce Nat must be rejected.

3) Classical logic allowed but explicitly tracked (selected)
   - Add explicit axiom mechanism:
     a) ability to declare axioms like EM/Choice (or import “classical” module).
     b) attach metadata to declarations indicating which axioms they depend on.
   - Add tests:
     a) A theorem that uses classical axiom is marked “classical-dependent.”
     b) A theorem that does not remains unmarked.

4) NbE definitional equality (selected; implementation task exists)
   - Ensure NbE respects transparency and Prop restrictions.
   - Make defeq deterministic and cache-friendly.

Deliverable expectations
- Update docs/spec/core/* to reflect:
  - Prop impredicativity + proof irrelevance/elimination restrictions
  - transparency model (transparent default + optional opaque)
  - classical axiom tracking model
- Provide a kernel API sketch that makes these policies explicit (e.g., defeq takes transparency context).