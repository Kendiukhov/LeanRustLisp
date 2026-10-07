import Std.Sync.Channel

/-!
Q7 (positive). Protocol length tied to data length: `sendAll` sends every element of a
`Vec Nat n` over a channel in state "n messages remaining" and returns it in state 0,
where `close` is allowed. The same `n` indexes the vector and the channel.
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

partial def drain (rx : CloseableChannel.Sync Nat) (acc : Array Nat := #[]) : IO (Array Nat) := do
  match ← rx.recv with
  | some x => drain rx (acc.push x)
  | none   => return acc

def main : IO Unit := do
  let v : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))
  let (c, rx) ← Chan.new 3
  let c ← sendAll v c
  c.close
  IO.println s!"received: {← drain rx}"
