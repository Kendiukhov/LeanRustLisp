-- Q12 (negative). The once-only function value `k` (quantity 1) is called twice.
module Main

import Control.Linear.LIO
import System.Concurrency.Session

withSender : (1 k : Nat -> L1 IO (Channel End)) -> L IO ()
withSender k = do
  c1 <- k 1
  c2 <- k 2              -- second call
  end c1
  end c2
