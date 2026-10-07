/-!
Q2 (negative). An `append` that drops an element cannot be given the sum type.
-/

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.append : Vec α n → Vec α m → Vec α (m + n)
  | .nil,       ys => ys
  | .cons _ xs, ys => Vec.append xs ys   -- bug: the element is dropped
