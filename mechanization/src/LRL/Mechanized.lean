import LRL.Syntax
import LRL.Reduction
import LRL.Typing
import LRL.Metatheory
import LRL.Affine.Syntax
import LRL.Affine.Typing
import LRL.Affine.Ownership
import LRL.Affine.Substitution
import LRL.Affine.Coercion
import LRL.Affine.Semantics
import LRL.Affine.Examples

/-!
# LRL mechanization entry point

This file re-exports the results that have been **fully mechanized**. A
result appears here **only** if its proof is complete, with no `sorry` and
no `admit`, in a module imported by the `LRL` library root. The
`#print axioms` commands at the end print, at every build, the axioms each
result depends on.

## Part 1 — simply-typed fragment (`Syntax`, `Reduction`, `Typing`, `Metatheory`)

* `LRL.Ty`, `LRL.Term` (de Bruijn `var`/`lam`/`app`), `LRL.shift`,
  `LRL.subst`, `LRL.Step` (`beta`, `appL`, `appR`, `lamCg`), `LRL.Context`,
  `LRL.lookup`, `LRL.Typed`.
* Lookup lemmas `LRL.lookup_append_lt`, `LRL.lookup_append_ge`,
  `LRL.lookup_insert_ge`, `LRL.lookup_insert_lt`.
* `LRL.typed_weaken`, `LRL.typed_weaken0` (weakening),
  `LRL.typed_subst`, `LRL.typed_subst0` (substitution),
  `LRL.typed_preservation` (preservation under one step).

## Part 2 — affine core with function kinds (`Affine/*`)

A call-by-value affine λ-calculus modelling the kernel's ownership rules:
Copy base types `unit`, `nat`, an owned resource type `res`, kinded arrows
`A →[k] B` (`fn ⊑ fnMut ⊑ fnOnce`; the kind describes how a closure uses its
captured environment), `let`, `consume`/`read` of resources, an iterator
`iter n z s` (a recursor on `Nat`) and erased positions `ghost t`.

* `LRL.Affine.Own Γ S t m S'` — the ownership judgment with usage modes
  ERASED/READ/MUT/CONSUME, call modes, capture by λ with the side condition
  `required(λ) ⊑ k` (`LRL.Affine.reqKind`, `LRL.Affine.sideCondition_iff`)
  and the repetition barrier on the step function of `iter`
  (`LRL.Affine.barrier_iff`).
* (T1) `kind_widening`; (T2) `eta_coercion`, `eta_coercion_needs`
  (η-expansion of a variable) and `eta_coercion_general`,
  `eta_value_reqKind_le` (η-expansion of any term, as the elaborator builds
  it); (T3) `typed_subst`, `own_subst`; (T4) `preservation`, `progress`;
  (T5) `no_double_consume`, `affine_safety`.
* Examples: `barrier_needed`, `subst_nonvalue_breaks_side_condition`,
  `read_after_consume`, `reads_then_consumes`, `eta_compound_needs_fnOnce`,
  `double_use_rejected`, `fnOnce_called_twice_rejected`.

## What is NOT mechanized

* Dependent types (universe levels, Π with dependency, inductive families);
  `Dependent.lean` is a scaffold with a `sorry` and is not imported here.
* The kernel's full recursor rule (fields, induction hypotheses, branching
  types), fixpoints, constructors and borrows of the real calculus; the
  affine core has one iterator on `Nat` without the predecessor argument.
* Reads after a move through a closure that captured by READ: the judgment,
  like the kernel's, does not rule them out (`read_after_consume`); that is
  the MIR borrow checker's job, which is not modelled.
* Any statement about the Rust implementation itself (the kernel's
  `check_ownership_*` functions, MIR): the mechanization is a model.
-/

namespace LRL

-- Part 1: simply-typed fragment.

/-- Substitution, simply-typed fragment, general form. -/
abbrev MechanizedSubstitution := @typed_subst

/-- Substitution, simply-typed fragment, position-0 form. -/
abbrev MechanizedSubstitution0 := @typed_subst0

/-- Weakening, simply-typed fragment, general form. -/
abbrev MechanizedWeakening := @typed_weaken

/-- Weakening, simply-typed fragment, position-0 form. -/
abbrev MechanizedWeakening0 := @typed_weaken0

/-- Preservation under one step, simply-typed fragment. -/
abbrev MechanizedPreservation := @typed_preservation

-- Part 2: affine core with function kinds.

/-- (T1) Kind widening. -/
abbrev MechanizedKindWidening := @Affine.kind_widening

/-- (T2) The η-expansion coercion is well-owned with required kind `k`. -/
abbrev MechanizedEtaCoercion := @Affine.eta_coercion

/-- (T2, converse) The η-expansion is well-owned only at kinds `⊒ k`. -/
abbrev MechanizedEtaCoercionNeeds := @Affine.eta_coercion_needs

/-- (T2, general form) η-expansion of an arbitrary term. -/
abbrev MechanizedEtaCoercionGeneral := @Affine.eta_coercion_general

/-- (T3) Value substitution for the typing judgment of λ^aff. -/
abbrev MechanizedAffineSubstitution := @Affine.typed_subst

/-- (T3) Value substitution for the ownership judgment. -/
abbrev MechanizedOwnSubst := @Affine.own_subst

/-- (T4) Preservation of typing, ownership and store agreement. -/
abbrev MechanizedAffinePreservation := @Affine.preservation

/-- (T4) Progress. -/
abbrev MechanizedAffineProgress := @Affine.progress

/-- (T5) No resource is consumed twice. -/
abbrev MechanizedNoDoubleConsume := @Affine.no_double_consume

/-- (T5) Affine safety for closed programs started with everything live. -/
abbrev MechanizedAffineSafety := @Affine.affine_safety

/-! ### Self-check: statements and axioms of each mechanized result -/

#check @MechanizedSubstitution
#check @MechanizedSubstitution0
#check @MechanizedWeakening
#check @MechanizedWeakening0
#check @MechanizedPreservation
#check @MechanizedKindWidening
#check @MechanizedEtaCoercion
#check @MechanizedEtaCoercionNeeds
#check @MechanizedEtaCoercionGeneral
#check @MechanizedAffineSubstitution
#check @MechanizedOwnSubst
#check @MechanizedAffinePreservation
#check @MechanizedAffineProgress
#check @MechanizedNoDoubleConsume
#check @MechanizedAffineSafety

#print axioms typed_subst
#print axioms typed_subst0
#print axioms typed_weaken
#print axioms typed_weaken0
#print axioms typed_preservation
#print axioms Affine.kind_widening
#print axioms Affine.eta_coercion
#print axioms Affine.eta_coercion_needs
#print axioms Affine.eta_coercion_general
#print axioms Affine.eta_var_reqKind
#print axioms Affine.eta_value_reqKind_le
#print axioms Affine.typed_subst
#print axioms Affine.own_subst
#print axioms Affine.preservation
#print axioms Affine.progress
#print axioms Affine.no_double_consume
#print axioms Affine.affine_safety
#print axioms Affine.barrier_needed
#print axioms Affine.subst_nonvalue_breaks_side_condition
#print axioms Affine.read_after_consume
#print axioms Affine.reads_then_consumes
#print axioms Affine.eta_compound_needs_fnOnce
#print axioms Affine.double_use_rejected
#print axioms Affine.fnOnce_called_twice_rejected

end LRL
