-- Q7 (negative: one message too few). The cons clause forgets to send the element.
module Main

import Data.Vect
import Control.Linear.LIO
import System.Concurrency.Session

Msgs : Nat -> Session
Msgs Z     = End
Msgs (S k) = Send Nat (Msgs k)

sendAll : Vect n Nat -> Channel (Msgs n) -@ L IO ()
sendAll []        c = end c
sendAll (_ :: xs) c = sendAll xs c    -- one message too few
