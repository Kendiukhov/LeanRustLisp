import LRL.Syntax

/-!
# LRL typing — simply-typed fragment

Context is a `List Ty`; de Bruijn index 0 refers to the head, i.e. the
most recently bound variable. The typing judgment `Typed Γ t τ` is the
standard STLC derivation with `var`, `lam`, and `app` constructors.

`insertAt n σ Γ` inserts `σ` into `Γ` at position `n` (0 = innermost).
This is the operation needed to state weakening uniformly.
-/

namespace LRL

/-- Typing context: innermost binding at the head. -/
abbrev Context := List Ty

/-- Look up the type of de Bruijn index `n` in the context. -/
def lookup : Context → Nat → Option Ty
  | [],     _     => none
  | τ :: _, 0     => some τ
  | _ :: Γ, n + 1 => lookup Γ n

/-- Insert `σ` into `Γ` at position `n`. -/
def insertAt : Nat → Ty → Context → Context
  | 0,     σ, Γ        => σ :: Γ
  | _ + 1, σ, []       => [σ]
  | n + 1, σ, τ :: Γ   => τ :: insertAt n σ Γ

/-- Simply-typed derivation. -/
inductive Typed : Context → Term → Ty → Prop where
  | var   {Γ n τ}     : lookup Γ n = some τ → Typed Γ (.var n) τ
  | lam   {Γ τ₁ τ₂ b} : Typed (τ₁ :: Γ) b τ₂ → Typed Γ (.lam τ₁ b) (.arrow τ₁ τ₂)
  | app   {Γ f a τ₁ τ₂} :
      Typed Γ f (.arrow τ₁ τ₂) →
      Typed Γ a τ₁ →
      Typed Γ (.app f a) τ₂

end LRL
