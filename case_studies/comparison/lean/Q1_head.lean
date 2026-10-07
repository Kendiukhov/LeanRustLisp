/-!
Q1 (positive). Length-indexed vector with a total `head`.

`Vec.head` has a single case: the index `n + 1` rules out `nil`, so Lean's coverage
checker accepts it without a `nil` case. The IR printed by `trace.compiler.ir.result`
shows that the compiled `head` is a bare field projection (no tag test, no panic path).
The same holds for the core-library `Vector α n` (an `Array` plus an erased size proof).
-/

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

set_option trace.compiler.ir.result true in
def Vec.head : Vec α (n + 1) → α
  | .cons x _ => x

-- Core library: `Vector.head` needs `NeZero n`, which holds for `n + 1`.
set_option trace.compiler.ir.result true in
def vectorHead (v : Vector Nat (n + 1)) : Nat := v.head

def main : IO Unit := do
  IO.println s!"Vec.head [1, 2] = {(Vec.cons 1 (Vec.cons 2 .nil)).head}"
  IO.println s!"Vector.head #v[7, 8, 9] = {vectorHead #v[7, 8, 9]}"
