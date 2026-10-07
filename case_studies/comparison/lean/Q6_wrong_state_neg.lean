import Std.Sync.Channel

/-!
Q6 (negative). `close` is called while one message is still owed (state `Chan 1`);
`close` requires `Chan 0`, so the call is rejected at compile time.
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

def main : IO Unit := do
  let (c, _rx) ← Chan.new 2
  let c ← c.send 10
  c.close                   -- wrong state: `Chan 1`, but `close` needs `Chan 0`
