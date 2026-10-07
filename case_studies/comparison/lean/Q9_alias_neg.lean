/-!
Q9 (negative). Identical to `Q9_two_refs.lean` except for the line marked CHANGED: the same
reference is passed twice, so `touch2` holds two live mutable references to one location and
both writes go to it. Lean has no borrow checker: the program is accepted and runs.
Compare `../rust/q09_two_mut_refs.rs --cfg alias_call` (rejected, E0499).
-/

def touch2 (a b : IO.Ref Nat) : IO Unit := do
  a.modify (· + 1)
  b.modify (· + 10)

def main : IO Unit := do
  let x ← IO.mkRef 0
  let y ← IO.mkRef 0
  touch2 x x                                  -- CHANGED: was `touch2 x y`
  IO.println s!"x = {← x.get} (both writes went to x), y = {← y.get}"
