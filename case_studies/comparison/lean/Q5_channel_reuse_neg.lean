import Std.Sync.Channel

/-!
Q5 (negative). The channel value `c` is used again after `send` consumed it.
Lean 4 has no linear or affine types, so nothing stops the reuse at compile time:
the program is accepted, both messages are sent on a channel whose type promised one,
and the second `close` fails only at run time inside `Std.CloseableChannel`.
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
  let c1 ← c.send 10
  let c2 ← c.send 20        -- reuse of `c`: accepted
  c1.close
  IO.println s!"received: {← drain rx}"
  c2.close                  -- the channel is already closed: run-time error
