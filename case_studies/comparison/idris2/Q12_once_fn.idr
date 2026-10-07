-- Q12 (positive). A once-only function value: `k` is bound with quantity 1 and is
-- called exactly once. The closure passed for `k` captures the linear channel `c`;
-- this is accepted because `k` has quantity 1 (with an unrestricted `k` it is rejected,
-- see Q12_capture_unrestricted_neg.idr).
module Main

import Control.Linear.LIO
import System.Concurrency.Session

OneMsg : Session
OneMsg = Send Nat End

withSender : (1 k : Nat -> L1 IO (Channel End)) -> L IO ()
withSender k = do
  c <- k 1
  end c

sender : Channel OneMsg -@ L IO ()
sender c = withSender (\x => send c x)

receiver : Channel (Dual OneMsg) -@ L IO Nat
receiver c = do
  (x # c) <- recv c
  end c
  pure x

main : IO ()
main = do
  (_, x) <- run (fork OneMsg sender receiver)
  putStrLn ("received: " ++ show x)
