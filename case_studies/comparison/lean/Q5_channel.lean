import Std.Sync.Channel

/-!
Q5/Q6 (positive). A channel wrapper indexed by the number of messages still to be sent,
built on the core library's `Std.CloseableChannel.Sync`. Used correctly: one `send` on a
`Chan 1`, then `close` on the resulting `Chan 0`.
-/
open Std

/-- Sending end of a channel on which exactly `n` more messages must be sent. -/
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
  let c ← c.send 10
  c.close
  IO.println s!"received: {← drain rx}"
