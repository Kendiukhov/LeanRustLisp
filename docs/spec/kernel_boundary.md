# Kernel Boundary and Trust Model

This document defines the boundary of the Trusted Computing Base (TCB) for LeanRustLisp.

## 1. Trusted Core (The Kernel)

The kernel is the minimal set of components that must be correct for the system to be sound.

### Components
1.  **Type Checker (`checker.rs`)**:
    *   Verifies type correctness of terms.
    *   Validates core invariants on incoming terms (e.g., no metas, explicit recursor levels) and checks
        `ty : Sort` plus `value : ty` (when provided) before admission. Closedness is enforced implicitly
        by type-checking in an empty context, not by a separate syntactic pass.
    *   Enforces universe levels (including impredicative `Prop`), including the universe rule
        for inductive declarations: constructor fields of an inductive in `Sort u` (not Prop) have
        types in universes at most `u`; parameters and indices are unconstrained
        (`core_calculus.md` §4).
    *   Checks inductive declarations before admission: the arity is a type ending in a sort, every
        constructor type is a type returning the inductive, strict positivity (no occurrence in
        the domain of an arrow at any depth, and none in the arguments of a constructor's result
        type; `let`s are expanded first), no nested occurrences, no Prop fields in data types
        (`core_calculus.md` §4). A rejected declaration leaves nothing in the environment.
    *   Enforces termination (structural/well-founded) for total definitions: a recursive call
        must supply the decreasing argument (a partial application that omits it is rejected),
        that argument must be structurally smaller, and a field of a recursor is smaller only
        when the recursor's major premise is the decreasing argument or already smaller — an
        induction hypothesis of a minor premise is never smaller (`core_calculus.md` §4).
    *   Enforces effect boundaries (Total vs Partial vs Unsafe).
    *   Checks fixpoints (T-Fix): the body against the annotation weakened over the recursive
        binder, and the result type at the end of the annotation's Pi telescope may not be a
        proposition (`K0055`: proofs are erased, so a looping fixpoint would stand for a proof).
        Type checking never unfolds a fixpoint (`K0049`), also not when it normalises a type to
        expose a Pi or a sort (`core_calculus.md` §5, §7).
    *   Admits a definition without a value only as an axiom (`K0053`), and records an axiom's
        dependency on itself (the client-supplied dependency list is not trusted).
    *   Under `allow_redefinition` (CLI `--allow-redefine`), refuses to redefine a definition
        or inductive that other entries refer to (`K0054`), in `add_definition`,
        `add_inductive` and `insert_inductive_placeholder`: entries are never re-checked, so a
        redefinition under them would keep entries that no longer check (closed proofs of
        `False`, `core_calculus.md` §8).
    *   Enforces elimination restrictions (Prop -> Type), also for inductives that may be
        propositions (an arity ending in `Sort u` or `Sort (imax 1 u)`, as in Lean 4).
    *   Enforces ownership/linearity on values: the affine ownership walk
        (`docs/spec/ownership_model.md` §6.2) runs on every definition value at
        `Env::add_definition` (`K0021`). It covers moves, reads and mutable uses of
        non-Copy variables (use after move), erased positions (types, proofs, motives,
        recursor parameters and indices: no effect), borrows (`borrow_shared` = read,
        `borrow_mut` = mutable use, never a move), closures (captures bounded by the
        closure's kind), recursors (branches of a saturated non-recursive elimination are
        alternatives; minor premises that may run more than once, including every minor
        premise of a recursor applied without its scrutinee, may not move outer
        values; recursive fields are consumed by their induction hypotheses) and
        fixpoints. It does **not** check borrows against each other (conflicting
        loans, moves while borrowed, references outliving their referent): that is
        the MIR borrow checker's job, outside the TCB.
    *   Decides Copy (`is_copy_type`): sorts, erased types (type families,
        propositions), `Ref Shared _`, and inductives with a Copy instance; it derives
        instances structurally except for interior-mutable and `affine` inductives and
        rejects `copy` + `affine` (`K0052`). A Copy instance belongs to the declaration it was
        derived for: redeclaring a name (only under `--allow-redefine`) drops the old instance
        before the new declaration derives its own, so redeclaring a type as `affine` makes it
        non-Copy and an affine value cannot then be used twice. A `Derived` instance submitted
        through `Env::add_copy_instance` is accepted only if it is exactly the instance the
        kernel derives itself for the registered declaration (`K0029` otherwise); the
        instance table is private (read access: `Env::copy_instances()`).
    *   Validates function kind annotations on `Lam`/`Pi` (Fn/FnMut/FnOnce) and
        rejects misuse without an explicit coercion. The kind a lambda requires is
        computed by the kernel's uses analysis (`term_variable_uses`), which is also
        what the elaborator uses to infer kinds and what MIR uses for required capture
        modes (`K0043` if the annotation is smaller).
    *   Validates capture-mode annotations only for **structural correctness**
        (closure id exists, capture indices reference actual free variables). It
        does **not** enforce capture-mode *strength*.
    *   Tracks axiom dependencies.
2.  **Definitional Equality (`nbe.rs`)**:
    *   Implements conversion checking via Normalization-by-Evaluation.
    *   Respects **transparency** settings (unfolding vs opaque).
    *   Uses fuel-bounded evaluation to keep defeq total; fuel is configurable via `LRL_DEFEQ_FUEL`.
        Fuel exhaustion is reported with guidance to mark large definitions `opaque` or raise the fuel.
        One budget covers a whole check (evaluation and read-back together) and every step is
        charged (δ, ι, β, ζ, and each binder opened by read-back or comparison); the nesting
        depth of a fuelled computation is limited to `nbe::MAX_EVAL_DEPTH` (`K0056`). The limit
        is sized for the CLI's 1 GiB compiler stack: a kernel client must run the checker on a
        comparably large stack. The type checker's normalisation (`whnf`, `whnf_in_ctx`) uses
        the same configuration as conversion: fixpoints are never unfolded.
    *   Unfolds a self-referential total definition only when its decreasing argument is a
        constructor application (guarded δ, `core_calculus.md` §5).
3.  **AST (`ast.rs`)**:
    *   Defines the core term structure (CIC with De Bruijn indices).

### Policies
*   **Transparency**: Default is transparent. Opaque definitions hide implementation details from the kernel's automatic unfolding, but can be forced open if needed (e.g. by reflective tools, though standard checking respects opacity). Prop classification respects `opaque` by default; explicit contexts can opt in to unfolding for checks like large elimination and Prop-in-data. MIR lowering may peek through opaque aliases to detect `Ref`/interior mutability for borrow checking; these checks do not affect definitional equality.
*   **Proof Irrelevance**: Proofs (terms in `Prop`) are computationally irrelevant. They cannot influence the runtime behavior of programs (except via their existence as a precondition).
*   **Axiom Tracking**: The kernel does not forbid axioms, but strictly tracks their usage. Classical
    classification is explicit: axioms carry tags (e.g., `classical`), and dependency analysis only uses
    those tags (no name-based heuristics). A "proven" theorem depending on a tagged axiom is tainted.
    This includes implicit unsafe axioms introduced by explicit Copy instances
    (`copy_instance(TypeName)` with the `unsafe` tag).
*   **Reserved primitives**: Names like `Ref`, `Shared`, `Mut`, `borrow_shared`, `borrow_mut`,
    and `index_*` are reserved. These are treated as compiler intrinsics during MIR lowering.
    The kernel only admits them as axioms with fixed signatures (intended for the prelude); user
    code must not define them.
    `Ref`/`Shared`/`Mut` define the reference type constructor and mutability tags used in
    ownership checks. `borrow_shared`/`borrow_mut` are safe primitives usable in total code, with
    safety enforced by the MIR borrow checker. `index_*` remain `unsafe` axioms until their safety
    contract is enforced.
*   **Capture modes (TCB note)**: Capture-mode *strength* is enforced in MIR lowering
    (which recomputes required capture modes with the kernel's uses analysis). The kernel
    only checks that capture annotations are well-formed and does not trust them for
    safety. The kernel's own ownership walk does not read capture annotations: it derives
    the effect of a capture from the closure's kind, which it checks.

### Prelude and Macro Boundary
*   **Prelude stack is trusted**: compile paths load `stdlib/prelude_api.lrl` plus a backend platform
    layer (`stdlib/prelude_impl_dynamic.lrl` or `stdlib/prelude_impl_typed.lrl`) before user code.
    These prelude files are part of the TCB and are compiled with reserved primitives enabled.
    They may define unsafe/classical axioms that user code cannot introduce silently.
*   **Macro boundary is strict for prelude stack**: prelude files are compiled with
    `MacroBoundaryPolicy::Deny`, so macro expansion cannot introduce unsafe/classical forms unless
    the macro is explicitly allowlisted in the compiler. Any such forms must appear explicitly in
    the prelude source or via an allowlisted macro.
*   **User code defaults to Deny**: `--macro-boundary-warn` downgrades macro boundary violations to
    warnings for user code (not for the prelude).

## 2. Untrusted Periphery

These components verify properties or transform code, but their correctness is not critical for the logical consistency of the kernel (though bugs here can produce invalid code that the kernel rejects, or runtime bugs).

1.  **Elaborator**: Infers types, implicit arguments, universe levels, and function kinds (with the kernel's uses analysis, so the kinds it stamps are the kinds the kernel re-check requires). Produces full kernel terms, including explicit universe levels on recursors (kernel rejects missing levels). It also records the source name of every binder term, which the driver uses to name variables in kernel ownership errors.
2.  **Parser**: Converts text to surface syntax.
3.  **Code Generator**: Compiles core terms to Rust/binary. Relies on the kernel's erasure of proofs.
4.  **Borrow Checker**: Implemented in the `mir` crate as NLL-style analysis. It is outside the TCB
    but enforces the safety contract for `borrow_shared`/`borrow_mut` in compiled code. It also
    enforces function-call borrow semantics: `Fn` calls take a shared borrow of the closure
    environment, `FnMut` calls take a mutable borrow, and `FnOnce` calls consume the closure.
    **Release-bar invariant:** the production pipeline must run MIR typing + NLL for top-level
    user-defined bodies and derived closure bodies. Canonical constructor aliases are excluded:
    constructors are resolved as constructor values from inductive metadata and are not admitted
    as ordinary kernel definitions.

### Division of the ownership guarantee
*   **Affinity** (a non-Copy value is moved at most once, never used after a move; a closure is
    never called in a way its kind forbids; a minor premise or fixpoint body that may run several
    times never moves an outer value) is enforced by the kernel (trusted) and re-checked on the
    control-flow graph by MIR's move analysis (untrusted, defence in depth).
*   **Borrowing** (no conflicting live loans, no move or reuse while borrowed, no reference
    outliving its referent) is enforced only by the MIR borrow checker (untrusted). The kernel
    treats references as ordinary values and borrows as reads / mutable uses.
*   The two checks accept different sets of programs: MIR rejects some kernel-accepted programs
    (borrow conflicts; MIR's own limitations such as non-Copy recursive fields), and every
    definition that reaches code generation has passed both.

## 3. Interaction

The periphery constructs `Definition` objects and submits them to the kernel (`Env::add_definition`). The
kernel accepts them only if they pass its add-time checks (core invariants, type correctness, ownership,
termination/effects for total definitions), and defeq/whnf are fuel-bounded (and depth-limited) to avoid
divergence. The environment does not expose mutable access to definitions or Copy instances in the public
API (definitions are added only by `add_definition`, Copy instances only by `add_copy_instance` and the
kernel's own derivation). Once accepted, a definition is trusted and immutable; under `allow_redefinition`
it can be replaced only while nothing refers to it (`K0054`).

**Limits of the Rust API as a boundary.** `Env` still has public fields — `inductives`, `axioms` and
`known_inductives` — and two unchecked helpers for the elaborator, `insert_inductive_placeholder` (which
refuses to replace an inductive that others refer to, but otherwise inserts the placeholder as given) and
`restore_inductive`. A Rust client that writes these directly bypasses the kernel's checks (the CLI driver
itself removes its placeholder through `inductives` before calling `add_inductive`). The guarantees above
therefore hold for environments built through the checked methods (`add_inductive`, `add_definition`,
`add_copy_instance`), which is how the CLI builds every user declaration; they are not a defence against
an arbitrary Rust program linked against the kernel.

For detailed phase contracts and elaboration invariants, see `docs/spec/phase_boundaries.md`.
