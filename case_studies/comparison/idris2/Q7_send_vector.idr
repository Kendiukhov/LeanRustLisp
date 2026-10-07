-- Q7 (positive). Protocol length tied to data length. `Msgs n` is the session type
-- "send exactly n natural numbers, then end" (library `System.Concurrency.Session`).
-- `sendAll` sends every element of a `Vect n Nat` over a `Channel (Msgs n)` and then
-- ends it; the channel is linear (`-@`), so each state is used exactly once.
module Main

import Data.Vect
import Control.Linear.LIO
import System.Concurrency.Session

%default total

Msgs : Nat -> Session
Msgs Z     = End
Msgs (S k) = Send Nat (Msgs k)

sendAll : Vect n Nat -> Channel (Msgs n) -@ L IO ()
sendAll []        c = end c
sendAll (x :: xs) c = do
  c <- send c x
  sendAll xs c

recvAll : (n : Nat) -> Channel (Dual (Msgs n)) -@ L IO (List Nat)
recvAll Z     c = do
  end c
  pure []
recvAll (S k) c = do
  (x # c) <- recv c
  xs <- recvAll k c
  pure (x :: xs)

main : IO ()
main = do
  (_, xs) <- run (fork (Msgs 3) (sendAll [1, 2, 3]) (recvAll 3))
  putStrLn ("received: " ++ show xs)
