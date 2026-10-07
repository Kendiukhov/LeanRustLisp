-- Q10 (positive). A linear channel consumed in both branches of a conditional is
-- accepted: each branch uses `c` exactly once.
module Main

import Control.Linear.LIO
import System.Concurrency.Session

OneMsg : Session
OneMsg = Send Nat End

finish : Bool -> Channel OneMsg -@ L IO ()
finish ok c =
  if ok
    then do c <- send c 1
            end c
    else do c <- send c 0
            end c

receiver : Channel (Dual OneMsg) -@ L IO Nat
receiver c = do
  (x # c) <- recv c
  end c
  pure x

main : IO ()
main = do
  (_, x) <- run (fork OneMsg (finish False) receiver)
  putStrLn ("received: " ++ show x)
