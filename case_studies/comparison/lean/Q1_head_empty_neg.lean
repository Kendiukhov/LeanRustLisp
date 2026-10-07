/-!
Q1 (negative). `head` of an empty user-defined `Vec` must be rejected at compile time.
-/

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.head : Vec α (n + 1) → α
  | .cons x _ => x

def bad : Nat := Vec.head (Vec.nil : Vec Nat 0)
