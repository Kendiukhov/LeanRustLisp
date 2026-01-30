import LRL.Syntax

namespace LRL

/-- Shift indices in a term by `d` above cutoff `c`. -/
def shift (t : Term) (c d : Nat) : Term :=
  match t with
  | Term.var k => if k < c then Term.var k else Term.var (k + d)
  | Term.sort l => Term.sort l
  | Term.const n ls => Term.const n ls
  | Term.app t1 t2 => Term.app (shift t1 c d) (shift t2 c d)
  | Term.lam ty b => Term.lam (shift ty c d) (shift b (c + 1) d)
  | Term.pi ty b => Term.pi (shift ty c d) (shift b (c + 1) d)
  | Term.letE ty v b => Term.letE (shift ty c d) (shift v c d) (shift b (c + 1) d)

/-- Substitute `s` for variable `k` in `t`. -/
def subst (t : Term) (k : Nat) (s : Term) : Term :=
  match t with
  | Term.var i =>
    if i == k then s
    else if i > k then Term.var (i - 1)
    else Term.var i
  | Term.sort l => Term.sort l
  | Term.const n ls => Term.const n ls
  | Term.app t1 t2 => Term.app (subst t1 k s) (subst t2 k s)
  | Term.lam ty b => Term.lam (subst ty k s) (subst b (k + 1) (shift s 0 1))
  | Term.pi ty b => Term.pi (subst ty k s) (subst b (k + 1) (shift s 0 1))
  | Term.letE ty v b => Term.letE (subst ty k s) (subst v k s) (subst b (k + 1) (shift s 0 1))

/-- Single step beta reduction. -/
inductive Step : Term -> Term -> Prop where
  | beta : Step (Term.app (Term.lam _ b) arg) (subst b 0 arg)
  -- Add congruence rules here...

/-- Definitional equality (conversion). -/
inductive Conv : Term -> Term -> Prop where
  | refl (t : Term) : Conv t t
  | step (t t' t'' : Term) : Step t t' -> Conv t' t'' -> Conv t t''
  -- Add symmetry, transitivity, eta...

end LRL
