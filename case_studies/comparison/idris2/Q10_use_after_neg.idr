-- Q10 (negative). `finish` consumes the linear channel in both branches of its
-- conditional (as in Q10_branch_consume.idr); `reuse` then uses the channel again.
-- (Without the last two lines, i.e. `finish ok c` followed by `pure ()`, it is accepted.)
module Main

import Control.Linear.LIO
import System.Concurrency.Session

finish : Bool -> Channel (Send Nat End) -@ L IO ()
finish ok c =
  if ok
    then do c <- send c 1
            end c
    else do c <- send c 0
            end c

reuse : Bool -> Channel (Send Nat End) -@ L IO ()
reuse ok c = do
  finish ok c
  c <- send c 2          -- `c` was consumed by `finish`
  end c
