-- Q1 (negative). `head` of an empty vector is rejected at compile time.
module Main

import Data.Vect

bad : Nat
bad = Data.Vect.head (the (Vect 0 Nat) [])
