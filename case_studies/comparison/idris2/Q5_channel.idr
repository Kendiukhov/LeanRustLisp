-- Q5/Q6 (positive). A session-typed linear channel from the library
-- (`System.Concurrency.Session`, package `linear`): `send` takes the channel with
-- quantity 1 and returns the channel at the next protocol state. Used correctly here:
-- one `send` on a `Channel (Send Nat End)`, then `end` on the resulting `Channel End`.
module Main

import Control.Linear.LIO
import System.Concurrency.Session

OneMsg : Session
OneMsg = Send Nat End

sender : Channel OneMsg -@ L IO ()
sender c = do
  c <- send c 10
  end c

receiver : Channel (Dual OneMsg) -@ L IO Nat
receiver c = do
  (x # c) <- recv c
  end c
  pure x

main : IO ()
main = do
  (_, x) <- run (fork OneMsg sender receiver)
  putStrLn ("received: " ++ show x)
