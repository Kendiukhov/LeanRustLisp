-- Q7 (negative: abandon). Identical to Q7_send_vector.idr except for the lines marked
-- CHANGED: a sender for a 2-message protocol sends one message and then stops, leaving a
-- channel that still owes a message unused. The channel is linear (quantity 1, `-@`), so
-- leaving it unused is rejected. Compare ../lrl/q07_protocol_length__abandon.lrl and
-- ../rust/q07_protocol_length.rs --cfg abandon (both accepted: affine, not linear).
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

sendOneOfTwo : Channel (Msgs 2) -@ L IO ()   -- CHANGED: instead of sendAll [1, 2]
sendOneOfTwo c = do
  c <- send c 1
  pure ()                                     -- CHANGED: `c : Channel (Msgs 1)` is abandoned

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
  (_, xs) <- run (fork (Msgs 2) sendOneOfTwo (recvAll 2))   -- CHANGED
  putStrLn ("received: " ++ show xs)
