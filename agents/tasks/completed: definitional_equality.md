AGENT TASK: Implement Lean-grade definitional equality via NbE  - Completed.

Primary area: kernel/src/checker.rs (+ any new kernel modules you introduce)
Goal: Replace the current “WHNF + structural recursion + always unfold Const” definitional equality with a principled NbE-based definitional equality engine that is deterministic, scalable, and compatible with dependent types + inductives.

High-level success criteria
1) `is_def_eq(env, t1, t2)` is implemented using NbE (evaluation to semantic domain + normalization-by-reification).
2) The kernel’s definitional equality is:
   - sound w.r.t. the kernel calculus,
   - deterministic,
   - avoids uncontrolled unfolding by default,
   - scalable (caching + no exponential blowups on common cases).
3) Existing kernel tests continue to pass; new targeted tests are added for β/δ/ι/ζ reduction and definitional equality.

Constraints / design rules
- Keep the trusted kernel small: NbE can live in the kernel, but it must be cleanly isolated in its own module (e.g., kernel/src/nbe.rs).
- Do not rely on the frontend or any heuristic elaboration for correctness.
- Do not introduce ad-hoc “special cases” for Nat/Bool/List into definitional equality. Inductive computation rules must be handled generically.
- Introduce explicit unfolding control (transparency) rather than “always unfold constants.”

Deliverables
A) Design note (short Markdown in docs/spec/core/definitional-equality.md or a kernel comment block)
- Explain the semantic domain, evaluation function, reification function, and how equality is decided.
- Specify what reductions are included in definitional equality:
  β: lambda/app
  δ: unfolding of definitions (with transparency control)
  ζ: let-reduction
  ι: eliminator computation (recursor over constructors)
- State how universes/levels are treated (syntactic comparison vs normalization of Level expressions).

B) Implementation (code)
1) Create `kernel/src/nbe.rs` (or similarly named) containing:
   - Semantic values (domain):
     * Neutral terms (stuck computations)
     * Closures for lambdas and pis (with environments)
     * Sort/Ind/Ctor/Rec representations
   - `eval(term, env, locals) -> Value`
   - `reify(ty, value) -> NormalForm` or `quote(value) -> Term` (choose one approach and document it)
   - Optional: `readback`/`quote_neutral` for neutrals
   - A normalization function: `normalize(env, term) -> Term` (or NormalForm)

2) Replace `whnf` and `is_def_eq` behavior:
   - Keep a small WHNF reducer if needed for non-defeq tasks, but definitional equality must use NbE normalization or semantic equality.
   - Implement `is_def_eq` as:
     normalize(t1) == normalize(t2)   (in α/β-normal, de Bruijn makes α easy), OR
     semantic equality with careful handling of neutrals.
   - Ensure definitional equality is stable under binder extension (fresh variable trick / reflection variable).

3) Introduce transparency (unfolding control) for δ-reduction
- Add an enum like:
  `enum Transparency { Opaque, Reducible, Transparent }`
- Store per-Const transparency in `Env` (or a side table).
- Default: user `def` is reducible or opaque (decide and document).
- In NbE eval, unfolding only happens if permitted by transparency context.

4) Handle inductives and recursors generically in evaluation
- When evaluating `Rec I`, you will get a neutral unless applied enough.
- When fully applied to a constructor, perform ι-reduction by selecting the correct minor premise and recursively evaluating as needed.
- This must work for arbitrary inductives registered in `Env` and their constructors, not just Nat.

C) Tests (must be added; do not skip)
Add unit tests in `kernel/src/lib.rs` (or a new kernel tests module) for:
1) β-equality: `(app (lam A body) x)` equals `body[x]`.
2) ζ-equality: `let x = v in b` equals `b[x := v]`.
3) δ-equality with transparency:
   - If `def f := ...` is transparent/reducible, then `f` is defeq to its body.
   - If marked opaque, `f` is NOT defeq to body (unless both sides are `f`).
4) ι-equality:
   - A Nat-like inductive with recursor: `rec motive base step zero` defeq `base`
   - `rec motive base step (succ n)` defeq `step n (rec ... n)`
5) Congruence sanity: defeq is reflexive/symmetric/transitive on a sample set (basic property tests).

D) Performance guardrails
- Implement memoization/caching:
  - Cache evaluated constants (δ) per transparency level.
  - Cache normalization results for repeated subterms if possible (hash-consing optional).
- Add a “fuel” or recursion depth guard ONLY if it’s necessary to prevent pathological behavior; document it if introduced.
