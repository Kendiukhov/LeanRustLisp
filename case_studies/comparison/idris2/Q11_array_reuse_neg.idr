-- Q11 (negative). After `write` has consumed the linear array handle, the old handle
-- cannot be read: the program would otherwise observe the destructive update.
-- (Reading the new handle instead, `read arr' 0`, is accepted.)
module Main

import Data.Linear.Array

peekOld : (1 arr : LinArray Int) -> Maybe Int
peekOld arr =
  let (_ # arr') = write arr 0 99
  in read arr 0          -- `arr` was consumed by `write`
