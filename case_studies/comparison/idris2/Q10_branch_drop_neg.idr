-- Q10 (negative control). Quantity 1 means "exactly once", not "at most once":
-- a linear channel used in one branch and dropped in the other is rejected.
module Main

import Control.Linear.LIO
import System.Concurrency.Session

finish : Bool -> Channel (Send Nat End) -@ L IO ()
finish ok c =
  if ok
    then do c <- send c 1
            end c
    else pure ()           -- `c` is not used in this branch
