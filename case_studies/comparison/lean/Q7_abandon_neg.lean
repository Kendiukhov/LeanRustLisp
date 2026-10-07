import Std.Sync.Channel

/-!
Q7 (negative: abandon). Identical to `Q7_send_vector.lean` except for `main` (marked CHANGED):
a channel opened for 2 messages receives one and is then dropped, with one message still owed;
it is never closed. Lean has no linear types, so nothing forces the remaining send and the
`close`: the program is accepted and runs. Compare `../lrl/q07_protocol_length__abandon.lrl` and
`../rust/q07_protocol_length.rs --cfg abandon` (both accepted: affine, not linear) and
`../idris2/Q7_abandon_neg.idr` (rejected: linear).
-/
open Std

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

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

def sendAll : Vec Nat n → Chan n → IO (Chan 0)
  | .nil,       c => pure c
  | .cons x xs, c => do sendAll xs (← c.send x)

def main : IO Unit := do
  let (c, _rx) ← Chan.new 2
  let _c1 ← c.send 1                                  -- CHANGED: one send, then
  IO.println "sent 1 of 2 messages; the Chan 1 is dropped"  -- CHANGED: the channel is abandoned
