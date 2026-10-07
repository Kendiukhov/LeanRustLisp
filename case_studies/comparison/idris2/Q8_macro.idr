-- Q8 (positive). Macros via elaborator reflection (`%language ElabReflection`).
--
-- (1) `genOps msg` is an elaborator script that declares a channel type `Chan n`
--     (indexed by the number of messages still to be sent) and typed operations
--     `start`, `send`, `close` for message type `msg`; `%runElab` runs it inside
--     `namespace Temp`. The declarations come from a declaration quote `[ ... ]
--     with the message type spliced in by `~(msg)`.
-- (2) Hygiene. Idris 2 quotes are not hygienic: `addOne` splices the user's term under
--     a template binder `x`, and a user variable also called `x` IS captured (result 2).
--     Hygiene is obtained by hand with `genSym` (`addOneHyg`, result 11).
module Main

import Language.Reflection

%language ElabReflection

genOps : TTImp -> Elab ()
genOps msg = declare `[
  public export
  data Chan : Nat -> Type where
    MkChan : List ~(msg) -> Chan n
  public export
  start : (n : Nat) -> Chan n
  start n = MkChan []
  public export
  send : Chan (S n) -> ~(msg) -> Chan n
  send (MkChan l) m = MkChan (m :: l)
  public export
  close : Chan 0 -> List ~(msg)
  close (MkChan l) = reverse l ]

namespace Temp
  %runElab genOps `(Nat)

%macro
addOne : TTImp -> Elab Nat
addOne e = check `(let x : Nat = 1 in ~(e) + x)

%macro
addOneHyg : TTImp -> Elab Nat
addOneHyg e = do
  x <- genSym "x"
  check (ILet EmptyFC EmptyFC MW x `(Nat) `(1) `(~(e) + ~(IVar EmptyFC x)))

userX : Nat
userX = let x : Nat = 10 in addOne `(x)

userXHyg : Nat
userXHyg = let x : Nat = 10 in addOneHyg `(x)

main : IO ()
main = do
  putStrLn ("generated ops: " ++ show (Temp.close (Temp.send (Temp.send (Temp.start 2) 20) 21)))
  putStrLn ("addOne `(x) with user x = 10 (plain quote): " ++ show userX ++ " (11 = hygienic, 2 = captured)")
  putStrLn ("addOneHyg `(x) with user x = 10 (genSym): " ++ show userXHyg)
