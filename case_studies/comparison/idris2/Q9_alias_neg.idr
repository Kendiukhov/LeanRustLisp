-- Q9 (negative). Identical to Q9_two_arrays.idr except for the line marked CHANGED: the same
-- linear array handle is passed twice, so `touch2` would hold two live handles to one
-- mutable array. Rejected: the linear name is used twice.
-- Compare ../rust/q09_two_mut_refs.rs --cfg alias_call (rejected, E0499).
module Main

import Data.Linear.Array
import Data.Linear.Notation

-- Cells hold unrestricted values (`!* Int`), so a value read back is unrestricted.
Cell : Type
Cell = !* Int

val : Maybe Cell -> Int
val (Just (MkBang x)) = x
val Nothing = 0

-- consumes the value read from the second array and the first array
finish : (1 _ : Maybe Cell) -> (1 a : LinArray Cell) -> (Int, Int)
finish Nothing a = toIArray a (\ia => (val (read ia 0), 0))
finish (Just (MkBang y)) a = toIArray a (\ia => (val (read ia 0), y))

-- writes 1 through the first handle and 10 through the second
touch2 : (1 a : LinArray Cell) -> (1 b : LinArray Cell) -> (Int, Int)
touch2 a b =
  let (_ # a) = write a 0 (MkBang 1)
      (_ # b) = write b 0 (MkBang 10)
  in finish (read b 0) a

main : IO ()
main = do
  let (x, y) = newArray 1 (\a => touch2 a a)   -- CHANGED: was newArray 1 (\a => newArray 1 (\b => touch2 a b))
  putStrLn ("x = " ++ show x ++ ", y = " ++ show y)
