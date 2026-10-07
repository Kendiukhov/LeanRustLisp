-- Q5 (negative). The channel `c` is used again after `send` consumed it.
module Main

import Control.Linear.LIO
import System.Concurrency.Session

sender : Channel (Send Nat End) -@ L IO ()
sender c = do
  c1 <- send c 10
  c2 <- send c 20        -- reuse of `c`
  end c1
  end c2
