/-!
Q11. In-place update of an unshared structure (Lean 4: reference counting with
destructive update when the reference count is 1, "functional but in place").

We compare the address of the array buffer before and after an update:
* `Vector.reverse`, `Array.set!` on an UNSHARED value: same address (updated in place);
* the same operations on a SHARED value (still used afterwards): new address (copied),
  and the original is unchanged.
In-place reuse is decided at run time (reference count = 1), not guaranteed statically.
The final IR of `revAcc` (a list reverse with an accumulator) tests `isShared` on each
cons cell: an unshared cell is reused (`set x_6[1] := ...`), a shared one is copied
(`ctor_1[List.cons]`).
-/

/-- Build a vector at run time from a seed, so the optimiser cannot share it. -/
@[noinline] def mkVec (k : Nat) : Vector Nat 8 := Vector.ofFn (fun i => i.val + k)

unsafe def addr {α} (a : α) : USize := ptrAddrUnsafe a

@[noinline] unsafe def reverseUnique (v : Vector Nat 8) : IO (Bool × Vector Nat 8) := do
  let before := addr v.toArray
  let r := v.reverse                      -- last use of `v`
  return (before == addr r.toArray, r)

@[noinline] unsafe def reverseShared (v : Vector Nat 8) : IO (Bool × Vector Nat 8 × Vector Nat 8) := do
  let before := addr v.toArray
  let r := v.reverse                      -- `v` is returned too, so it is shared here
  return (before == addr r.toArray, v, r)

@[noinline] unsafe def setUnique (a : Array Nat) : IO (Bool × Array Nat) := do
  let before := addr a
  let b := a.set! 0 99                    -- last use of `a`
  return (before == addr b, b)

@[noinline] unsafe def setShared (a : Array Nat) : IO (Bool × Array Nat × Array Nat) := do
  let before := addr a
  let b := a.set! 0 99                    -- `a` is returned too, so it is shared here
  return (before == addr b, a, b)

set_option trace.compiler.ir.result true in
def revAcc : List α → List α → List α
  | [],      acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

unsafe def mainImpl : IO Unit := do
  -- run-time seeds (always 0): the vectors are built at run time, no closed-term sharing
  let (u1, r1) ← reverseUnique (mkVec (← IO.rand 0 0))
  let (s1, v2, r2) ← reverseShared (mkVec (← IO.rand 0 0))
  let (u2, b3) ← setUnique (mkVec (← IO.rand 0 0)).toArray
  let (s2, a4, b4) ← setShared (mkVec (← IO.rand 0 0)).toArray
  IO.println s!"same buffer after the update? Vector.reverse: unshared {u1}, shared {s1}; Array.set!: unshared {u2}, shared {s2}"
  IO.println s!"Vector.reverse: unshared result {r1.toArray}; shared: original {v2.toArray}, result {r2.toArray}"
  IO.println s!"Array.set!: unshared result {b3}; shared: original {a4}, result {b4}"
  IO.println s!"revAcc [1, 2, 3, 4] [] = {revAcc [1, 2, 3, 4] []}"

@[implemented_by mainImpl] opaque mainSafe : IO Unit
def main : IO Unit := mainSafe
