/-!
Q4 (negative: an index used as a run-time value). The length index `n` of the user-defined
inductive family `Vec α n` is an ordinary implicit argument of type `Nat`, so a function may
return it at run time (`Vec.len`); Lean has no quantity/erasure annotation that would forbid
this. Accepted (the same definition is part of `Q4_erasure.lean`, whose IR shows that `cons`
stores the index). Compare `../idris2/Q4_erased_index_neg.idr` (rejected: quantity 0) and
`../lrl/q04_erasure__index_at_runtime.lrl` (accepted).
-/

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.len (_ : Vec α n) : Nat := n

def main : IO Unit :=
  IO.println s!"len [5, 6, 7] = {(Vec.cons 5 (.cons 6 (.cons 7 .nil))).len}"
