/-!
Q9 (positive). Two mutable references (`IO.Ref`) to two different locations are passed to one
function, which writes through both. Lean's mutable references are ordinary values: nothing
tracks how many references to one location are live (see `Q9_alias_neg.lean`).
-/

def touch2 (a b : IO.Ref Nat) : IO Unit := do
  a.modify (· + 1)
  b.modify (· + 10)

def main : IO Unit := do
  let x ← IO.mkRef 0
  let y ← IO.mkRef 0
  touch2 x y
  IO.println s!"x = {← x.get}, y = {← y.get}"
