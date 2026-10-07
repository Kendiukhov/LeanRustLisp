-- Q12 (negative, second form). A closure that captures the linear channel `c` is
-- passed where an unrestricted function (callable any number of times) is expected.
module Main

import Control.Linear.LIO
import System.Concurrency.Session

withSender : (k : Nat -> L1 IO (Channel End)) -> L IO ()
withSender k = do
  c <- k 1
  end c

sender : Channel (Send Nat End) -@ L IO ()
sender c = withSender (\x => send c x)
