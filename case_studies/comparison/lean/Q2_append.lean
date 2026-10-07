/-!
Q2 (positive). `append` whose result length is the sum of the input lengths.

The index is written `m + n` (not `n + m`) because `Nat.add` recurses on its second
argument: `m + (k + 1)` reduces to `(m + k) + 1`, so the `cons` case type-checks by
definitional unfolding alone, with no cast. The core library's `Vector.append` has type
`Vector α n → Vector α m → Vector α (n + m)` (implemented on `Array`, with a proof).
-/

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.append : Vec α n → Vec α m → Vec α (m + n)
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (Vec.append xs ys)

def Vec.toList : Vec α n → List α
  | .nil       => []
  | .cons x xs => x :: xs.toList

-- The length is checked statically: 2 + 3 = 5.
def five : Vec Nat 5 :=
  Vec.append (.cons 1 (.cons 2 .nil)) (.cons 3 (.cons 4 (.cons 5 .nil)))

-- Core library equivalent.
def fiveCore : Vector Nat 5 := (#v[1, 2] : Vector Nat 2) ++ (#v[3, 4, 5] : Vector Nat 3)

#check @Vector.append

def main : IO Unit := do
  IO.println s!"Vec.append    = {five.toList}"
  IO.println s!"Vector.append = {fiveCore.toArray}"
