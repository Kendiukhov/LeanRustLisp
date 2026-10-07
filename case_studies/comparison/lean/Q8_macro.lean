/-!
Q8 (positive). Hygienic macros.

(1) `protocol P carrying T` is a command macro that generates a typed channel type
    `P.Chan n` (indexed by the number of messages still to be sent) and typed operations
    `P.start`, `P.send`, `P.close`. The generated names are built with `mkIdentFrom`
    so that they are visible to the user; everything else in the template is hygienic.
(2) `add_one! e` expands to `let x := 1; e + x`. Lean's macro hygiene renames the
    template's `x`, so a user variable also called `x` inside `e` is not captured:
    the result below is 11 (capture would give 2). As a control, `add_one_unhygienic!`
    deliberately builds its binder with `mkIdent` (opting out of hygiene); it captures
    the user's `x` and yields 2.
-/
open Lean in
macro "protocol " name:ident " carrying " msg:term : command => do
  let chan  := mkIdentFrom name (name.getId ++ `Chan)
  let start := mkIdentFrom name (name.getId ++ `start)
  let send  := mkIdentFrom name (name.getId ++ `send)
  let close := mkIdentFrom name (name.getId ++ `close)
  `(structure $chan (n : Nat) where
      sent : List $msg
    def $start (n : Nat) : $chan n := ⟨[]⟩
    def $send {n : Nat} (c : $chan (n + 1)) (m : $msg) : $chan n := ⟨m :: c.sent⟩
    def $close (c : $chan 0) : List $msg := c.sent.reverse)

protocol Temp carrying Nat

#check @Temp.send     -- generated, typed operation

def readings : List Nat := Temp.close (Temp.send (Temp.send (Temp.start 2) 20) 21)

macro "add_one! " e:term : term => `(let x := 1; $e + x)

def userX : Nat := let x := 10; add_one! x

example : userX = 11 := rfl     -- checked at compile time: no capture

open Lean in
macro "add_one_unhygienic! " e:term : term => do
  let x := mkIdent `x
  `(let $x := 1; $e + $x)

def userXCaptured : Nat := let x := 10; add_one_unhygienic! x

example : userXCaptured = 2 := rfl

def main : IO Unit := do
  IO.println s!"generated ops: {readings}"
  IO.println s!"add_one! x with user x = 10: {userX} (11 = hygienic, 2 = captured)"
  IO.println s!"add_one_unhygienic! x (control, mkIdent): {userXCaptured}"
