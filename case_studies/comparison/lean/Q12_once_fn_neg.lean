import Std.Sync.Channel

/-!
Q12 (negative). A function value that should be callable only once (it consumes the
channel it captures) is called twice. Lean 4 has no once-only (linear) function types:
every closure may be called any number of times, so the program is accepted and both
calls send on a channel whose type promised one message.
-/
open Std

structure Chan (n : Nat) where
  raw : CloseableChannel.Sync Nat

def Chan.new (n : Nat) : IO (Chan n × CloseableChannel.Sync Nat) := do
  let raw ← CloseableChannel.Sync.new
  return (⟨raw⟩, raw)

def Chan.send (c : Chan (n + 1)) (x : Nat) : IO (Chan n) := do
  c.raw.send x
  return ⟨c.raw⟩

def Chan.close (c : Chan 0) : IO Unit := c.raw.close

partial def drain (rx : CloseableChannel.Sync Nat) (acc : Array Nat := #[]) : IO (Array Nat) := do
  match ← rx.recv with
  | some x => drain rx (acc.push x)
  | none   => return acc

def main : IO Unit := do
  let (c, rx) ← Chan.new 1
  let sendOnce : Nat → IO (Chan 0) := fun x => c.send x   -- captures (consumes) `c`
  let c1 ← sendOnce 1
  let _c2 ← sendOnce 2                                     -- second call: accepted
  c1.close
  IO.println s!"received: {← drain rx}"
