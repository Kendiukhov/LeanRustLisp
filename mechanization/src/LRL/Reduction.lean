import LRL.Syntax

/-!
# LRL reduction — simply-typed fragment

`shift` increments free variables above a cutoff.
`subst` substitutes a term for a specific de Bruijn index and shifts the
remaining free variables down by one (the standard de Bruijn substitution).
`Step` is the single-step call-by-name/full-reduction relation with β,
appL, appR, and lam congruences.
-/

namespace LRL

/-- `shift d c t`: add `d` to every free variable in `t` whose index is ≥ `c`. -/
def shift (d : Nat) : Nat → Term → Term
  | c, .var k   => if k < c then .var k else .var (k + d)
  | c, .lam τ b => .lam τ (shift d (c + 1) b)
  | c, .app f a => .app (shift d c f) (shift d c a)

/-- `subst j s t`: substitute `s` for de Bruijn index `j` in `t`, decrementing
    free variables above `j` by one. Variables under binders are handled by
    incrementing `j` and shifting `s` by one. -/
def subst (j : Nat) (s : Term) : Term → Term
  | .var k =>
      if k = j then s
      else if k > j then .var (k - 1)
      else .var k
  | .lam τ b => .lam τ (subst (j + 1) (shift 1 0 s) b)
  | .app f a => .app (subst j s f) (subst j s a)

/-- Single-step reduction with β and standard congruences. -/
inductive Step : Term → Term → Prop where
  | beta  {τ b a}   : Step (.app (.lam τ b) a) (subst 0 a b)
  | appL  {f f' a}  : Step f f' → Step (.app f a) (.app f' a)
  | appR  {f a a'}  : Step a a' → Step (.app f a) (.app f a')
  | lamCg {τ b b'}  : Step b b' → Step (.lam τ b) (.lam τ b')

end LRL
