/-!
Q3 (positive). Compiler-checked proofs that reverse is an involution.

(1) Lists: `rev` is a user-defined (quadratic) list reverse; `rev_rev` is proved by
    induction with one auxiliary lemma.
(2) Length-indexed vectors: a user-defined `Vec α n` with `snoc` and a length-preserving
    `Vec.reverse : Vec α n → Vec α n`; `Vec.reverse_reverse` is proved the same way.
(3) The core library proves the law for its own `List.reverse` and for the array-based
    length-indexed `Vector.reverse`; we restate both.
`#print axioms` lists the axioms each proof depends on (no `sorryAx`).
-/

def rev : List α → List α
  | []      => []
  | x :: xs => rev xs ++ [x]

theorem rev_append (xs ys : List α) : rev (xs ++ ys) = rev ys ++ rev xs := by
  induction xs with
  | nil => simp [rev]
  | cons x xs ih => simp [rev, ih, List.append_assoc]

theorem rev_rev (xs : List α) : rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, rev_append, ih]

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.snoc : Vec α n → α → Vec α (n + 1)
  | .nil,       y => .cons y .nil
  | .cons x xs, y => .cons x (xs.snoc y)

def Vec.reverse : Vec α n → Vec α n
  | .nil       => .nil
  | .cons x xs => xs.reverse.snoc x

theorem Vec.reverse_snoc (xs : Vec α n) (y : α) :
    (xs.snoc y).reverse = .cons y xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Vec.snoc, Vec.reverse, ih]

theorem Vec.reverse_reverse (xs : Vec α n) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Vec.reverse, Vec.reverse_snoc, ih]

def Vec.toList : Vec α n → List α
  | .nil       => []
  | .cons x xs => x :: xs.toList

-- Core-library theorems (length-indexed `Vector` and `List`).
theorem vector_rev_rev (v : Vector α n) : v.reverse.reverse = v := Vector.reverse_reverse v
theorem list_rev_rev (xs : List α) : xs.reverse.reverse = xs := List.reverse_reverse xs

#print axioms rev_rev
#print axioms Vec.reverse_reverse

def main : IO Unit := do
  IO.println s!"rev (rev [1, 2, 3]) = {rev (rev [1, 2, 3])}"
  let v : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))
  IO.println s!"Vec.reverse [1, 2, 3] = {v.reverse.toList}"
