import Std.Sync.Channel

/-!
Q7 (negative: one message too many). The `cons` case sends the element twice.
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
  | .cons x xs, c => do
      let c ← c.send x
      let c ← c.send x      -- one message too many
      sendAll xs c
