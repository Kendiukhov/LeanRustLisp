/-!
# LRL dependent fragment — scaffold

This file defines a Pi-type (type-family) extension of the STLC core and
states (without proving) the substitution lemma for it. It exists to
document precisely what the dependent version of Lemma~\\ref{lem:subst}
from the paper would look like, and to give a Lean skeleton for future
work. **Nothing in this file is added to `Mechanized.lean`.** The proofs
are left as `sorry` so the structure is visible; the build target
`lake build LRL.Dependent` is not part of the `LRL` library root.

This is deliberately isolated: `LRL.lean` does not import it, and no
`Mechanized*` alias cites anything from this file. If a future session
closes the `sorry`s, add the corresponding lemma to `Mechanized.lean`
with a corresponding note in the paper's §9. Until then, the paper
states the dependent substitution lemma as a paper-level sketch.

Set `set_option warningAsError false` so the `sorry`s do not break the
build of the library as a whole if this file is ever imported.
-/

set_option warningAsError false

namespace LRL.Dependent

/-- Types are themselves terms (a universe hierarchy). -/
inductive Term : Type where
  | var : Nat → Term
  | sort : Nat → Term
  | pi : Term → Term → Term
  | lam : Term → Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

/-- Shift free variables by `d` above cutoff `c`. -/
def shift (d : Nat) : Nat → Term → Term
  | _, .sort u      => .sort u
  | c, .var k       => if k < c then .var k else .var (k + d)
  | c, .pi a b      => .pi (shift d c a) (shift d (c + 1) b)
  | c, .lam a b     => .lam (shift d c a) (shift d (c + 1) b)
  | c, .app f a     => .app (shift d c f) (shift d c a)

/-- Substitute `s` for de Bruijn index `j`. -/
def subst (j : Nat) (s : Term) : Term → Term
  | .sort u  => .sort u
  | .var k   => if k = j then s else if k > j then .var (k - 1) else .var k
  | .pi a b  => .pi (subst j s a) (subst (j + 1) (shift 1 0 s) b)
  | .lam a b => .lam (subst j s a) (subst (j + 1) (shift 1 0 s) b)
  | .app f a => .app (subst j s f) (subst j s a)

abbrev Context := List Term

def lookup : Context → Nat → Option Term
  | [], _ => none
  | τ :: _, 0 => some τ
  | _ :: Γ, n + 1 => lookup Γ n

/-- Dependent typing judgment — sketch only. Several rules are omitted
    (conversion, universe cumulativity, application substitution sanity). -/
inductive Typed : Context → Term → Term → Prop where
  | sort {Γ u} : Typed Γ (.sort u) (.sort (u + 1))
  | var  {Γ n τ} : lookup Γ n = some τ → Typed Γ (.var n) (shift (n + 1) 0 τ)
  | pi   {Γ a b u₁ u₂} :
      Typed Γ a (.sort u₁) →
      Typed (a :: Γ) b (.sort u₂) →
      Typed Γ (.pi a b) (.sort (max u₁ u₂))
  | lam  {Γ a b τ u} :
      Typed Γ a (.sort u) →
      Typed (a :: Γ) b τ →
      Typed Γ (.lam a b) (.pi a τ)
  | app  {Γ f arg a b} :
      Typed Γ f (.pi a b) →
      Typed Γ arg a →
      Typed Γ (.app f arg) (subst 0 arg b)

/-!
### Substitution lemma (NOT PROVED)

The dependent substitution lemma is stated here for clarity but left as
`sorry`. Closing it requires additional reasoning about how substitution
commutes with the return type in the `app` rule and how the shifts in
the `var` rule interact with inserted contexts — neither of which is a
one-line adaptation of the STLC proof.

Do not add this theorem to `Mechanized.lean` until the `sorry` is gone.
-/
theorem typed_subst_dependent_SORRY
    {Γ₁ Γ₂ : Context} {σ : Term} {s t τ : Term}
    (_ : Typed (Γ₁ ++ σ :: Γ₂) t τ)
    (_ : Typed (Γ₁ ++ Γ₂) s σ) :
    Typed (Γ₁ ++ Γ₂) (subst Γ₁.length s t) (subst Γ₁.length s τ) := by
  sorry

end LRL.Dependent
