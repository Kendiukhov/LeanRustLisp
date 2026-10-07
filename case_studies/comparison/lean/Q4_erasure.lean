/-!
Q4. Are proofs and indices absent at run time? Evidence: the compiler's final IR
(`trace.compiler.ir.result`). `◾` marks an erased (irrelevant) argument.

(a) `safeDiv` takes a proof `_h : b > 0`; the IR signature marks it `◾` and the
    specialised worker `safeDiv._redArg` drops it entirely.
(b) The core `Vector α n` is passed as a bare `Array` (the size proof is gone).
(c) A subtype `{ k : Nat // k > 0 }` is represented as a bare `Nat`.
(d) A user-defined *inductive* `Vec α n`: its index `n` is an ordinary implicit
    constructor argument of type `Nat` (not a proposition), so `cons` stores it as a
    field (the first field of `ctor_1[Vec.cons]`) and `Vec.push` receives it as a
    run-time argument; it is NOT erased. Consequently a function may return the index
    at run time (`Vec.len`); there is no quantity/erasure annotation to forbid this.
-/

set_option trace.compiler.ir.result true in
def safeDiv (a b : Nat) (_h : b > 0) : Nat := a / b

set_option trace.compiler.ir.result true in
def useSafeDiv (a : Nat) : Nat := safeDiv a 2 (by decide)

set_option trace.compiler.ir.result true in
def vectorSize (v : Vector Nat n) : Nat := v.toArray.size

set_option trace.compiler.ir.result true in
def mkPos (k : Nat) : { k : Nat // k > 0 } := ⟨k + 1, Nat.succ_pos k⟩

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

set_option trace.compiler.ir.result true in
def Vec.push (x : α) (v : Vec α n) : Vec α (n + 1) := .cons x v

set_option trace.compiler.ir.result true in
def Vec.len (_ : Vec α n) : Nat := n

def main : IO Unit := do
  IO.println s!"safeDiv 10 2 = {useSafeDiv 10}, size = {vectorSize #v[1, 2, 3]}, pos = {(mkPos 4).val}"
  IO.println s!"len (push 1 [2, 3]) = {(Vec.push 1 (.cons 2 (.cons 3 .nil))).len}"
