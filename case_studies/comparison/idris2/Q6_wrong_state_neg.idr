-- Q6 (negative). `end` is called while one message is still owed: the channel is in
-- state `Send Nat End`, but `end` requires `End`.
module Main

import Control.Linear.LIO
import System.Concurrency.Session

sender : Channel (Send Nat (Send Nat End)) -@ L IO ()
sender c = do
  c <- send c 10
  end c                  -- wrong state
