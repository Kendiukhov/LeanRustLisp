import Std.Sync.Channel

/-!
Q10 (limit probe; the negative of Q10_branch_consume.lean). The channel `c` is consumed
in both branches of the conditional (`finish` sends the last message and closes it) and
then used again. Lean 4 has no usage discipline, so this is accepted; the extra `send`
fails only at run time, inside `Std.CloseableChannel`, because the channel is closed.
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

def finish (ok : Bool) (c : Chan 1) : IO Unit :=
  if ok then do (← c.send 1).close
  else do (← c.send 0).close

def main : IO Unit := do
  let (c, _rx) ← Chan.new 1
  finish false c
  let _ ← c.send 2          -- `c` was consumed by `finish`: accepted, fails at run time
  IO.println "unreachable if the second send fails"
