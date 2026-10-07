-- Q7 (negative: one message too many). The cons clause sends the element twice.
module Main

import Data.Vect
import Control.Linear.LIO
import System.Concurrency.Session

Msgs : Nat -> Session
Msgs Z     = End
Msgs (S k) = Send Nat (Msgs k)

sendAll : Vect n Nat -> Channel (Msgs n) -@ L IO ()
sendAll []        c = end c
sendAll (x :: xs) c = do
  c <- send c x
  c <- send c x          -- one message too many
  sendAll xs c
