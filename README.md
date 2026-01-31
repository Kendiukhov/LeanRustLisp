# LeanRustLisp (LRL)

> A language where types can express theorems, resources are real and tracked, and the language is programmable by its users.

The compiler is not your friend; it’s your very expensive, very literal lawyer.

## Core Goals

1.  **Soundness you can bet a civilization on**: Small trusted kernel, proofs checked, no “trust me bro” in the core.
2.  **Systems-level performance**: Predictable layout, no mandatory GC, AOT compilation, good FFI.
3.  **Rust-grade resource discipline**: Ownership/borrowing, lifetime checking, data-race freedom in safe code.
4.  **Lean-grade specification**: Dependent types, inductive types, theorem proving, proof erasure.
5.  **Lisp-grade extensibility**: Hygienic macros, syntax as data, elaborator/tactic plugins.

## Non-Goals

*   **Full type inference for dependent types everywhere**: You will write annotations. The alternative is undecidability plus suffering.
*   **Mutating dependently-typed values in-place without restrictions**: Mutable typestate + dependent indices is a swamp; we’ll do it with explicit patterns that stay decidable.
*   **A single “one ring” mechanism for metaprogramming, effects, optimization, and proofs**: That path ends in a baroque compiler that no one can modify.

## Safety Boundaries

LRL defines three distinct fragments:

1.  **`def` (Total Fragment)**: Definitions used in types/definitional equality must be strictly terminating (structural or well-founded recursion). Can appear in types.
2.  **`partial def` (Partial Fragment)**: General recursion allowed, but cannot appear in types. Lives under an effect (e.g., `Comp`).
3.  **`unsafe def` (Unsafe Fragment)**: FFI, raw pointers, manual memory. Explicitly marked. The kernel remains sound, but safety contract is user-verified.

## Intro
LeanRustLisp (LRL) is an attempt to make three things stop fighting and start cooperating: mathematical truth (Lean), resource reality (Rust), and programmable language (Lisp). The result is a language where you can write high-performance systems code, state the invariants it must satisfy, and then have the compiler refuse to build anything that doesn’t cash those checks.
The basic slogan is: your program is not just instructions. It’s a contract. And LRL’s compiler is not a friendly assistant; it’s a very literal lawyer who insists the contract is internally consistent.
LRL has a small trusted kernel that checks a minimal core calculus (dependent types, universes, inductives). Everything else—parsing, macros, elaboration, borrow checking, optimizations, code generation—is outside the trust boundary. That split matters because it keeps the “truth engine” tiny enough to audit, and it means the fancy parts of the compiler can’t smuggle in unsoundness: they must output core terms the kernel can verify. If you’ve ever watched a compiler become an unreviewable cathedral, you know why this is a civilizational design constraint.
From Lean, LRL takes the idea that types can express theorems. A function’s signature isn’t a suggestion; it can encode precise invariants: non-empty vectors, dimension-safe matrix multiplication, protocol states, resource budgets. And proofs are not runtime baggage. Proof terms live in Prop and are erased, so you can ship fast binaries that still carry compile-time correctness guarantees. You don’t just test “sort works”; you can prove sortedness and permutation, then erase the proof and keep the speed.
From Rust, LRL takes the stance that resources are real. Memory, aliasing, mutation, and concurrency aren’t “advanced topics”; they are the default failure modes of ambitious software. LRL uses an explicit ownership and borrowing discipline, checked on a dedicated mid-level IR, so safe code can’t create use-after-free, double-free, or data races. The key point is that this safety is part of the language’s semantics, not an accident of one backend. You can transpile to Rust today and target LLVM tomorrow without changing what “safe LRL” means.
From Lisp, LRL takes the refusal to freeze the language. The syntax is designed to be transformed. Macros are first-class: you can define new surface constructs, new notation, tiny DSLs, and new proof automation. But unlike the “wild west” macro cultures of history, LRL aims for hygienic, staged, deterministic macro expansion with good tooling. You get to bend the language without breaking scoping, without breaking error spans, and without turning compilation into a non-reproducible séance.
One of the most important conceptual moves in LRL is the separation of worlds. There is a total fragment—definitions that are allowed to influence types and definitional equality—and a computational fragment—general recursion, IO, allocation, concurrency—that lives under explicit effects. That keeps typechecking decidable and the kernel sane, while still letting you write real programs. The point is to avoid the classic trap: letting “ordinary computation” leak into the logic until the logic becomes a runtime and the runtime becomes a logic and nobody can prove anything without summoning a demon.
Effects are not invisible. In LRL, doing IO is not “just calling a function.” It shows up in the type. That makes codebases easier to reason about and harder to accidentally corrupt. If you want to make it even more “advanced civilization,” effects can be capabilities: you don’t just have permission to allocate or access the network; you hold a token that can be tracked, passed, and restricted. The same machinery can express budgets: fuel, time, memory. At that point, “this computation cannot exceed N steps” stops being a comment and becomes a type-level fact.
What does this buy you in practice? It collapses entire classes of bugs from “things you find in production” into “programs you cannot write.” Out-of-bounds access becomes “type mismatch.” Dangling references become “lifetime violation.” Wrong dimension math becomes “doesn’t compile.” Race conditions become “need a safe concurrency primitive or explicit unsafe.” And the language lets you raise the bar progressively: start with simple static guarantees, then move toward proof-carrying components where it’s worth it.
LRL is also, intentionally, not pretending that safety means “no sharp edges exist.” It means sharp edges are labeled. There is unsafe, and it is explicit. If you cross the boundary into raw pointers or FFI, you’re making a local treaty with chaos, and the compiler will not let you forget where you did that. This is a philosophy as much as a feature: constrain unsafety to small, auditable regions rather than letting it leak everywhere through “temporary hacks” that become permanent.
If Rust is “systems programming without fear,” LRL is “systems programming without fear, plus the option to prove you didn’t lie to yourself.” If Lean is “proofs that compile,” LRL is “proofs that compile into performant programs.” If Lisp is “a language that grows new limbs,” LRL is “a language that grows new limbs and then proves the surgery didn’t break physics.”
In other words: it’s an attempt to build software the way you’d want to build a starship. Not because a starship is romantic, but because it’s expensive, complex, and deeply intolerant of subtle bugs. 



## License

[Apache 2.0 / MIT]
