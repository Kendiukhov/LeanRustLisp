# MIR Specification (Structure + Places)

This document defines the structural shape of MIR (Mid-level IR) in LRL, with
emphasis on places/projections and where region information lives.

## Overview

MIR is a typed, CFG-based IR used for ownership, borrow checking (NLL), and
typed backend readiness. It is the single pipeline IR for both batch compile
and REPL evaluation.

## Core Structure

A MIR body contains:
- **Locals**: typed slots (`MirType`) for arguments, temporaries, and return.
- **Basic blocks**: a sequence of statements plus a terminator.
- **CFG**: explicit control-flow edges through terminators.

Key nodes:
- `Statement::Assign(Place, Rvalue)`
- `Statement::StorageLive/StorageDead(Local)`
- `Terminator::{Return, Goto, SwitchInt, Call, Unreachable}`

## Places and Projections

A **Place** represents a memory location:
```
Place = LocalId + Projection*
```

Projections include:
- `Deref` (indirection through references or raw pointers)
- `Field(i)` (field projection for struct/ctor fields)
- `Downcast(variant_index)` (enum/ADT variant projection)
- `Index(local)` (optional; for indexed containers)

Place typing must be **projection-aware**, using ADT layout metadata so that
borrow checking and codegen can reason about field-level aliasing.

## Regions in MIR

Regions are not standalone MIR nodes; they are carried by `MirType::Ref`.
Borrow creation is explicit (`Rvalue::Ref`) and **assigns a fresh inference
region** to the new reference at the borrow site (origin location).

- `Region::Static` is reserved for globals / truly static references.
- NLL solves region constraints over CFG points.

## Semantic Identity Rule

All semantic identity in MIR is keyed by nominal IDs (DefId/AdtId/CtorId/FieldId),
not by raw strings. Borrow checking and codegen must not depend on names.

## Recursor Lowering and Its Limits

A saturated recursor application (`Rec_I params motive minors indices major`) is lowered to a
`SwitchInt` on the discriminant of the major premise, with one arm per constructor. Every binder
of a constructor after the inductive's parameters is a field (implicit binders included): it is
stored in the runtime value and bound by the kernel's minor premise, and the arm moves (or copies,
for a Copy field) it out of the major premise into a local.

**Non-recursive inductives** (no constructor has a field whose type is the inductive itself, e.g.
`Bool`, `Option`, `Pair`, `Eq`). The minor premises are *alternatives*: exactly one of them runs,
once. Each minor is lowered inside its own arm, after the switch:

- a minor that is a syntactic λ-chain binding exactly the constructor's fields is inlined: the
  field locals play the role of the λ-binders and the λ-body is lowered directly into the
  destination (no closure is built);
- any other minor is evaluated in its arm and applied to the field locals (the minor of a
  field-less constructor is simply evaluated there).

Consequently an owned outer value consumed by several minors is moved only on the path that
runs, and only the taken branch is evaluated (before, every minor was evaluated before the
switch, so `(match b Nat (case (true) (print_nat 1)) (case (false) (print_nat 2)))` printed both
numbers). The parameters, the motive and the indices are not evaluated (they are only needed by
induction hypotheses, of which there are none). Whether the kernel accepts a program that
consumes the same owned value in two branches is decided by the kernel's ownership rules
(`docs/spec/ownership_model.md`), not by MIR.

**Recursive inductives** (`Nat`, `List`, `Vec A n`, trees). The minor premises are evaluated
once, before the switch, into closure (or value) locals; in each arm the induction hypotheses
are computed eagerly by a recursive recursor call that receives the minor locals and the
recursive field, and then the arm's minor premise is called. The minor of a constructor with a
recursive field is therefore both passed to the recursive call(s) and called, so it must be
duplicable:

- Following Rust's rule, a closure value is `Copy` when every capture is `Copy` or captured by
  shared reference. When lowering such a minor, captures that are only read (including function
  values that are only called with kind `Fn`) are captured by shared reference instead of being
  moved into the closure environment, so the minor is `Copy` and is passed to the recursive call
  by copy. The minor never outlives the recursor application; NLL tracks the loans held by the
  closure like any other loan (a result that would carry such a reference out of the function is
  rejected as an escaping reference). Nested closures inside the minor re-capture the reference.
- A minor that captures a value by move (it consumes it) or by mutable reference (it mutates it
  or calls an `FnMut` function) stays non-Copy; passing it to the recursive call and then calling
  it is rejected with `M100` (the kernel rejects consuming captures in repeated minors earlier,
  with `K0021`, but accepts mutable captures: such programs are kernel-accepted and MIR-rejected,
  e.g. `case_studies/tools/stage_matrix/gaps/g7_fnmut_minor_reborrow.lrl`).
- A local into which several closures are written (the arms of an inline `match` that produce a
  function) is Copy only if every one of them has only Copy captures: one capture-free arm does
  not make the local holding another arm's consuming closure duplicable
  (`LoweringContext::non_copy_closure_locals` / `copy_closure_locals` in `lower.rs`).

Further rules and limits:

- **Impossible arms.** An arm whose constructor's result indices clash with the scrutinee's
  indices (both constructor-headed, with different constructors at some position, after
  normalising the scrutinee's indices) can never run for a kernel-checked program; it is lowered
  to `Unreachable`. This matters for "large" eliminations whose motive computes a different type
  in the impossible case (a total `head` on `Vec A (succ n)` whose `nil` case returns a unit
  value of type `HeadTy zero`).
- **Erased single-constructor majors.** A Prop-typed major premise of a single-constructor
  inductive (an `Eq` proof) is erased at run time and has no discriminant; its only arm is
  entered directly.
- **Non-Copy recursive fields.** Computing the induction hypothesis of a recursive field of
  non-Copy type consumes the field (the kernel marks it moved inside the minor premise,
  `RecursiveFieldConsumedByIh`). If the arm's minor premise is a λ-chain binding every field and
  induction hypothesis and its body does not use such a field at run time (occurrences in types
  and other erased positions do not count; the analysis is the kernel's
  `term_runtime_variables`), the arm is not unpacked in MIR — that would move the field twice,
  into the induction-hypothesis call and into the minor's argument list. Instead the arm passes
  the whole major premise, with the parameters, motive, minor premises and indices, to the
  recursor's entry function, which performs the same dispatch (and gives the minor premise its
  own copy of the field it does not use). This is what lets `map` over a list of tokens, or
  `head`/`append` on `Vec A n` for a type variable `A`, compile. The minor premise is analysed
  in the context of the recursor application (it used to be analysed in a context shifted by
  the fields that precede the recursive field, so the analysis failed for a minor that uses a
  captured variable, e.g. a polymorphic `map` over `List A` calling the captured function, and
  the arm was unpacked and rejected with `M100`). Only a Copy (duplicable) minor premise is
  handed to the entry function, which calls it once per recursive occurrence out of MIR's
  sight; a minor that consumes a captured non-Copy value is not Copy, so its arm is unpacked and
  MIR rejects the repeated use itself (the kernel rejects such a program first,
  `ConsumedInRepeatedScope`).
- **Limitation (kept): a minor premise that uses a non-Copy recursive field.** If the body does
  use the field at run time (for example a minor that returns the tail `t` while the induction
  hypothesis consumed it), the arm is unpacked as usual and MIR rejects the double move with
  `M100`; the kernel rejects the same program earlier (`K0021`, `RecursiveFieldConsumedByIh`).
- **Limitation: effects in base cases of recursive types.** Because the minors of a recursive
  type are evaluated before the switch, an effect in the minor of a field-less constructor (e.g.
  `print_nat` in the `zero` case) runs once when the minor is evaluated, not once per time the
  case is reached, and the minors of all field-less constructors are evaluated.
- An unsaturated recursor application (fewer arguments than the recursor takes) is a lowering
  error: it has no executable lowering (it used to become an opaque constant that the dynamic
  binary reported as a panic and that the typed backend could not compile). Eta-expand it.

## Proofs in Lowering

Proofs (values whose type is a proposition) are erased at run time, and the kernel's ownership
walk never visits them (`docs/spec/ownership_model.md`, erased positions); lowering follows the
same reading, so that MIR does not reject programs that are legal for the kernel:

- a term lowered into a local that holds a proof of a non-function type (a value of `Eq A x y`,
  of a user proposition, ...) is not evaluated: the local receives `()`;
- a closure whose type is a proposition (a Pi ending in `Prop`) is built **without captures**:
  its body produces a proof, which is not evaluated, so the closure needs nothing from its
  environment and moves or borrows nothing when it is built. A capture-free closure is Copy;
- a term that computes a proof of function type (an application, a `let`, an elimination, ...)
  and is lowered into a local of that type is replaced by its eta-expansion `λx. t x`, which the
  previous rule builds as a capture-free closure, so the computation is not evaluated either;
- a local holding a proof is Copy, also when the proof has a function type (its run-time value
  is a capture-free closure or a function item), so a proof-typed closure may be passed twice
  (corpus positive control P19, `case_studies/corpus/30_proof_closure_duplicated.lrl`).

Calls of proof-typed functions produce proofs and are therefore never evaluated.

## Fixpoints

`fix f : T. body` is lowered to a closure whose environment slot 0 holds the fixpoint itself and
whose remaining slots hold its captures (the environment always records the self slot). When the
body is a syntactic λ (the usual case), its body is lowered directly with the closure argument
playing the role of the λ-binder, so closures inside it keep their source-span and capture
metadata. The dynamic backend builds the fixpoint as an `Rc<dyn Fn>` that reaches itself through
a weak reference set right after allocation.

## Transformations After the Checks

The compile path runs proof erasure, dead-code elimination, CFG simplification and copy
propagation (`transform/inline.rs`) after the MIR checks. Copy propagation is restricted to facts
that hold at every use of a flow-insensitive analysis: a destination written exactly once from a
capture-free constant, or from a `copy` of a stable source (written at most once, never killed
before the function exit). Moves, closure literals and borrowed callees are never propagated,
nor are constants of a polymorphic type (a generic global function, whose MIR type mentions its
own type parameters): the typed backend lets rustc infer the type arguments from the uses of the
local the function is stored in, and a propagated call would leave that local without uses.
Erasure keeps the lowering's `is_copy` flags (it can only make a local more copyable). As a
safety net, the compile path re-runs the MIR ownership analysis on the transformed bodies and
reports a failure as an internal compiler error instead of emitting code.
