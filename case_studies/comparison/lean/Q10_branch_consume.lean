import Std.Sync.Channel

/-!
Q10 (positive). A channel consumed in both branches of a conditional is accepted.
In Lean this holds trivially: there is no usage discipline at all, so a value may be
used in one branch, both branches, or several times (see `Q5_channel_reuse_neg.lean`).
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

/-- Each branch consumes `c` (sends the final message, then closes). -/
def finish (ok : Bool) (c : Chan 1) : IO Unit :=
  if ok then do (← c.send 1).close
  else do (← c.send 0).close

partial def drain (rx : CloseableChannel.Sync Nat) (acc : Array Nat := #[]) : IO (Array Nat) := do
  match ← rx.recv with
  | some x => drain rx (acc.push x)
  | none   => return acc

def main : IO Unit := do
  let (c, rx) ← Chan.new 1
  finish false c
  IO.println s!"received: {← drain rx}"
