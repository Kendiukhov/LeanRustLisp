**Core implementation**

Below is a development plan aimed at getting LeanRustLisp from “interesting prototype with real pieces” to a language whose *core* has Lean-grade correctness, whose *programming model* has Rust-grade resource safety, and whose *user-facing power* has Lisp-grade extensibility—without turning the compiler into a trusted, unreviewable blob.

I’m going to be blunt about ordering: if you want this to “fully represent the idea,” the next big work is not a large stdlib. It’s tightening the kernel boundary, locking down definitional equality \+ totality, and turning macros/borrowing/effects into first-class, principled mechanisms.

I. Non‑negotiable north star: what must be true when you’re “done”

A. Tiny trusted kernel (Lean)

1. The only trusted code is: core AST \+ definitional equality \+ type checker for the core calculus (and a small amount of primitive axioms).  
2. Parsing, macro expansion, elaboration, borrow checking, optimization, and codegen are NOT trusted; they must emit artifacts the kernel can check (directly or via validators).

B. Resource safety in safe code (Rust)

1. Safe code cannot trigger UB: no use-after-free, no double free, no data races, no invalid aliasing.  
2. All “escape hatches” are explicit (`unsafe`) and auditable.  
3. Effects and resources are not ambient. They are typed/capability-based.

C. Programmable language (Lisp)

1. Users can define new surface constructs via macros.  
2. Macros are hygienic by default, staged, deterministic, and tooling-friendly.  
3. (Optional but ideal) Type-aware elaborator macros/tactics exist, but don’t enlarge the trusted kernel.

D. Separation of total vs partial computation (Lean \+ reality)

1. Anything that can affect typechecking/definitional equality must be terminating (or explicitly marked as an axiom with a “here be dragons” label).  
2. General recursion, IO, FFI, etc. live in a computational fragment that cannot leak into types.

Keep those as acceptance criteria for every subsystem decision.

II. Phase 0: Freeze the design contract (spec-first, not code-first)

Deliverables (write these docs before doing major refactors)

1. “Core calculus spec”  
* Core term grammar (Sort/Π/λ/App/Let/Inductive/Constructor/Eliminator/Const/Var).  
* Universe level story (Prop vs Type u, cumulativity rules, level constraints).  
* Definitional equality rules (what reduces, when, with what transparency).  
2. “Fragment separation spec”  
* What counts as total `def`.  
* What counts as `partial def` (and what is forbidden in types/defeq).  
* What `unsafe` permits and what it doesn’t.  
3. “Ownership \+ effects spec”  
* What is owned, what is affine/linear, what is copyable.  
* Reference types (`&ρ A`, `&ρ mut A`) and lifetime/region constraints.  
* Effect type shape (rows, capabilities, or monad-like `Comp ε A`) and how it interacts with the above.

Exit condition for Phase 0: you can point to a written rule for every “why does the compiler allow/reject this” question for the core.

III. Phase 1: Kernel hardening (make the Lean part real)

This is the most leverage per line of code you’ll ever get.

A. Shrink the trusted boundary

1. Remove parsing from the kernel crate (or rename the crate to avoid claiming it’s the kernel).  
* Parsing should be in frontend only.  
* Kernel should take core terms, not source strings.  
2. Make the kernel API minimal and explicit, e.g.:  
* `check_decl(core_decl) -> Result<()>`  
* `infer(core_term, ctx) -> Result<core_type>`  
* `defeq(t1, t2) -> bool` (or `Result<bool>` if fuel/timeouts are explicit)  
* `whnf/normalize` for kernel-internal use only

B. Implement definitional equality properly  
Right now prototypes often “sort of normalize” and then compare. That breaks fast once you add universes/inductives/eliminators seriously.

Target: a robust definitional equality engine, ideally Normalization-By-Evaluation (NbE) for speed and correctness.

* Define exactly which reductions count (β, δ, ι, ζ and eliminator computation rules).  
* Add transparency levels: reducible/semireducible/irreducible (or simpler at first).  
* Ensure definitional equality cannot run arbitrary partial computation.

C. Inductives and eliminators: from “it works for Nat/Bool/List” to “general”  
You want:

* General inductive declarations with parameters/indices.  
* Positivity check (even a conservative one to start).  
* Universe level constraints for inductives.  
* General eliminator/recursor \+ computation rules (ι-reduction) in definitional equality.

D. Totality/termination for the total fragment  
Pick a first workable rule set:

* Structural recursion on inductives (like Lean’s guarded recursion).  
* Well-founded recursion optionally, but that needs proof infrastructure.

If you’re not ready to implement termination checking immediately:

* Introduce explicit `axiom` / `unsafe_total` markers that are tracked and cannot pretend to be normal defs.  
* Your kernel must clearly distinguish “proved/checked” from “assumed”.

Kernel test suite (must be built in this phase)

1. “Kernel conformance tests”: a folder of core terms that must typecheck and a folder that must fail.  
2. Property/fuzz tests: random ASTs should never crash the kernel.  
3. Mechanization alignment: every time the kernel rules change, the Lean mechanization files must be updated or marked stale.

Exit condition for Phase 1: you trust the kernel enough that you’re willing to build on it for years, because you can explain its semantics and it is small.

IV. Phase 2: Make macros real (the Lisp part, but disciplined)

You already have a macro hook (`defmacro` appears in the CLI/compiler pipeline). The plan is to evolve it from “expander that rewrites nodes” into an industrial macro system that doesn’t murder tooling.

A. Syntax objects with hygiene and spans  
Implement a `Syntax` representation that carries:

* Source span  
* Scope/mark information for hygiene  
* Structured forms (lists/symbols/literals) not just strings

Hygiene strategy

* Use “marks/renaming” (Scheme-style) or “syntax parameters” (Racket-ish).  
* Provide explicit escape hatches: `datum->syntax` / `syntax->datum` equivalents for controlled capture when needed.

B. Staging and determinism

* Macros run at compile-time in a `Meta` phase (no runtime effects unless explicitly allowed).  
* Expansion is deterministic given the same inputs and macro environment.  
* Cache expansions (critical for IDE responsiveness).

C. Macro debugging and transparency

* A `:expand` REPL/CLI command that shows fully expanded syntax.  
* Preserve spans through expansion so errors point to user code, not generated sludge.

D. Type-aware macros (optional in first iteration; high value later)  
Two-tier approach:

1. Pure syntax macros (fast, deterministic).  
2. Elaborator plugins (type-directed rewriting) that are untrusted but produce kernel-checkable output.

Exit condition for Phase 2: users can define meaningful new surface constructs (notation, pattern matching sugar, small DSLs) without breaking hygiene or error reporting.

V. Phase 3: Elaborator upgrades (the “make dependent typing usable” part)

Right now, the REPL/compiler are doing special-case handling for `def`/`inductive`. That’s fine for bootstrapping, but you eventually want a real front-end pipeline with declarations, modules, and elaboration that produces fully explicit core terms.

A. Move from “REPL special forms” to a real declaration AST

* Parse source into a sequence of declarations \+ expressions.  
* Declarations: `def`, `theorem`, `inductive`, `structure`, `defmacro`, etc.  
* Elaborator elaborates declarations into kernel core.

B. Bidirectional elaboration \+ metavariables

* Implement holes/metavariables and unification constraints.  
* Use bidirectional typing (check/infer) to keep inference predictable.  
* Restrict higher-order unification to pattern fragments (Lean does this carefully).

C. Implicits and implicit arguments

* Support implicit Π-binders and implicit argument insertion.  
* Add explicit syntax to control inference when it gets ambiguous.

D. Pattern matching elaboration

* Elaborate match syntax into eliminators/recursors in core.  
* Generate equations and check coverage/exhaustiveness progressively.  
* Preserve definitional equalities that users expect (esp. for dependent pattern matches).

E. Typeclass/trait resolution (bridge Lean \+ Rust)

* Implement a deterministic instance search with termination limits.  
* Coherence rules (orphan-like): prevent conflicting instances across modules/packages.  
* Use traits both for math structures (Lean-style) and for resource properties (`Copy`, `Drop`, `Send`, `Sync`).

F. Tactic/proof scripting (Lean-grade usability)  
Even a minimal tactic framework is a force multiplier:

* `rfl`, `simp`\-style rewriting, `cases`, `induction`  
* Goal display and proof state in REPL  
* All tactics must elaborate to proof terms the kernel checks

Exit condition for Phase 3: writing dependently typed programs and small proofs is ergonomic enough that you don’t need to drop into raw core ASTs.

VI. Phase 4: Ownership and borrowing (make the Rust part real)

This is the most “new research engineering” part, but you can do it incrementally if you choose the right architecture.

A. Decide: ownership checking in kernel or as a separate analysis?  
Strong recommendation: keep it out of the trusted kernel.

* Kernel checks logical soundness of terms/types.  
* A borrow checker checks resource discipline on a computational IR.  
* The compiler only emits code if both pass.

B. Introduce a Mid-level IR (LRL-MIR)  
Why: borrow checking is vastly easier on an explicit, statement-like IR than on a λ-calculus directly.  
MIR should have:

* Explicit locals, blocks, control flow  
* `move`, `copy`, `borrow_shared`, `borrow_mut`  
* explicit `drop`  
* explicit pattern matching / switch on constructors  
* explicit call and return

C. Borrow checker MVP  
Start with lexical lifetimes (simple), then evolve to NLL-style constraints.  
Enforce:

* One mutable borrow OR many shared borrows  
* No use after move  
* Drops occur exactly once  
* References do not outlive owners

D. Lifetimes/regions as a constraint system

* Generate region constraints from MIR.  
* Solve constraints; on success, annotate MIR with lifetimes.  
* Produce excellent errors (“this borrow overlaps that borrow because …”).

E. Interaction with dependent types (avoid the swamp)  
Rule that keeps you sane:

* Anything behind `&mut` must keep its type stable (indices definitionally equal).  
* If an operation changes an index (typestate change), it consumes ownership and returns a new value.  
* For “mutable sized containers,” use existential packaging (`Σ n, Vec A n`) behind a stable handle.

F. Concurrency and `Send/Sync`

* Encode `Send` and `Sync` as trait predicates derived for safe types.  
* Provide safe primitives: channels with move semantics, mutexes, atomics.  
* Ensure data races require `unsafe`.

Exit condition for Phase 4: you can port a handful of classic Rust borrow-checker examples and get the same accept/reject behavior in safe code.

VII. Phase 5: Effects, `partial`, and `unsafe` (real computation without poisoning the logic)

A. Effect system shape  
Pick one:

1. Effect rows: `Comp {IO, Alloc} A`  
2. Capability-passing: `World ⊸ (A × World)` style (linear token)  
3. Graded monads (resource bounds) if you want “fuel” built-in

A strong hybrid:

* `Comp ε A` for effects  
* Some effects require linear capabilities (tokens) so you can’t duplicate authority

B. Enforce the separation boundary

* Total `def` can appear in types and definitional equality.  
* `partial def` cannot appear in types/defeq; it lives in `Comp`.  
* `unsafe def` is explicitly marked and gated.

C. FFI design

* `extern` declarations with explicit ABI and layout attributes  
* Safe wrappers in stdlib  
* `unsafe` required for raw pointer operations

D. Resource reasoning as types (the “advanced civ” feature)

* Optional `Fuel n` as a linear capability for step-bounded computations  
* Optional “memory budget” capabilities for allocation-heavy code

Exit condition for Phase 5: you can write real programs (IO, allocation) while keeping the proof/total fragment pure and terminating.

VIII. Phase 6: Backend and runtime (make it fast and remove “panic” from the happy path)

Your current approach (compiling to Rust with a dynamic `Value`) is a reasonable bootstrap, but it has two big drawbacks:

* It can panic at runtime even if the source is well-typed (because `Value` is untyped).  
* It blocks performance and optimization.

Plan for evolution:

A. Keep the current backend as a reference interpreter/codegen

* Useful for debugging semantics.

B. Add a typed backend path  
Option 1: Generate typed Rust

* Generate Rust enums for inductives, typed functions, and generics.  
* Avoid `Value` except at FFI boundaries.

Option 2: LLVM/MLIR backend

* Lower MIR to LLVM with explicit data layout.  
* More work, more control.

C. Closure conversion and data layout

* Implement closure conversion with explicit environment structs.  
* Define runtime representation of inductives (tag \+ fields), and make it stable.

D. Proof erasure

* Erase `Prop` terms fully.  
* Erase computationally irrelevant arguments (where safe).

E. Translation validation (eventually)

* For optimizations, add validators that check “before and after” equivalence for a pass (reduces trust in the optimizer).

Exit condition for Phase 6: well-typed programs don’t panic from internal tag/type mismatches, and performance is not hostage to dynamic dispatch everywhere.

IX. Phase 7: Only now—stdlib and “language feel”

Once the core semantics are stable (kernel \+ elaborator \+ borrowing \+ effects), then stdlib becomes leverage instead of sandbags.

Strategy:

1. “Kernel-proximal” stdlib first (math \+ proofs)  
* Equality lemmas, rewriting helpers, induction principles, basic decidable predicates  
* Simple data types: `Nat`, `Bool`, `List`, `Option`, `Sigma`, `Prod`  
2. “Rust-grade” stdlib next (safe systems)  
* `Vec`, slices, strings, maps  
* Allocators/arenas as explicit capabilities  
* Concurrency primitives  
3. “Lisp-grade” stdlib (metaprogramming)  
* Macro utilities, syntax traversal, quasiquote  
* Verified desugaring helpers where possible

Exit condition for stdlib growth: every new “nice” abstraction doesn’t weaken the core safety story and doesn’t require kernel changes.

X. Tooling and UX (because without this, nobody survives the power)

A. LSP server

* Incremental parsing, macro expansion, elaboration  
* Goal display for proofs  
* “go to definition” through expanded code

B. Formatter

* Deterministic formatting for s-exprs \+ any notation layer

C. Error reporting

* Spans preserved through macros and elaboration  
* “explain borrow error” style diagnostics

D. Build tool/package manager

* Reproducible builds, lockfiles, deterministic macro expansion  
* Coherence-friendly module system

XI. A “do not proceed to huge stdlib yet” checklist

Don’t scale stdlib until these are true:

1. Kernel does not parse source; it checks core terms.  
2. Definitional equality rules are precise and implemented robustly (NbE or equivalent).  
3. Total vs partial boundary is enforced mechanically.  
4. Inductives/eliminators are general and their computation rules participate in defeq.  
5. Macro hygiene \+ staging are real and debuggable.  
6. Borrow checking exists on a MIR and rejects the classic bad patterns.  
7. Codegen is on track to eliminate dynamic `panic` on well-typed programs.

If any of those are “kinda,” build minimal prelude only—just enough to test the compiler.

XII. “Power demos” to drive development (keep you honest)

Pick a small set of flagship programs/proofs that must work, and use them as a regression suite. Examples:

1. Dependent programming: length-indexed `Vec` with safe `head` and `append` preserving lengths.  
2. Proof: verified `sort` (sorted \+ permutation) where proofs erase.  
3. Borrowing: return a slice into a buffer with correct lifetime; reject use-after-free.  
4. Macros: a hygienic `match` macro \+ a small typed DSL macro.  
5. Effects: `IO` program that cannot be called from pure code without `Comp`.  
6. FFI: safe wrapper around a tiny C function with explicit `unsafe` boundary.

Those demos keep the “Lean+Rust+Lisp” synthesis from drifting into three disconnected feature piles.

If you implement this plan in order, you’ll end up with something that isn’t just “Lean with parentheses” or “Rust with proofs.” It will be its own coherent machine: a small kernel of truth, a disciplined resource model, and an extensible surface language that stays inside the truth-preserving pipeline. That’s the whole point of the joke—except you’re trying to actually ship the joke.

