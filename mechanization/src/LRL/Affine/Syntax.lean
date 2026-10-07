/-!
# Affine core with function kinds — syntax

A small call-by-value affine λ-calculus that models the ownership rules of
the LRL kernel (see `docs/spec/ownership_model.md` and
`docs/spec/function_kinds.md` in the repository).

* Types: `unit` and `nat` (Copy), `res` (an owned resource, not Copy) and
  kinded arrows `arr k A B`, written `A →[k] B` (not Copy).
* Function kinds `fn ⊑ fnMut ⊑ fnOnce`.  The kind of a λ describes how the
  closure uses its **captured environment**; it never describes the argument.
* Usage modes `erased < read < mutate < consume` (ERASED / READ / MUT /
  CONSUME).
* Terms are in de Bruijn form.  `loc l` is a resource constant (a store
  location); `consume t` destroys a resource, `read t` observes a resource
  without destroying it, `iter n z s` runs the step function `s` `n` times
  from `z` (a recursor for `Nat`), and `ghost t` is a computationally
  irrelevant (erased) occurrence of `t`, e.g. a proof argument.

Substitution `subst j v t` is substitution of a **closed** value: it does
not shift `v` when it goes under a binder.  This is the only substitution
that the call-by-value semantics of closed programs performs
(`Semantics.lean`); every lemma that uses it assumes `Typed [] v A`.
-/

namespace LRL.Affine

/-! ### Function kinds -/

/-- Function kinds, ordered `fn ⊑ fnMut ⊑ fnOnce`. -/
inductive Kind : Type where
  | fn
  | fnMut
  | fnOnce
  deriving DecidableEq, Repr

/-- Position of a kind in the order `fn ⊑ fnMut ⊑ fnOnce`. -/
def Kind.rank : Kind → Nat
  | .fn => 0
  | .fnMut => 1
  | .fnOnce => 2

/-- The kind order `k ⊑ k'`. -/
instance : LE Kind := ⟨fun k k' => k.rank ≤ k'.rank⟩

instance (k k' : Kind) : Decidable (k ≤ k') :=
  inferInstanceAs (Decidable (k.rank ≤ k'.rank))

theorem Kind.le_def {k k' : Kind} : k ≤ k' ↔ k.rank ≤ k'.rank := Iff.rfl

theorem Kind.le_trans {k₁ k₂ k₃ : Kind} (h₁ : k₁ ≤ k₂) (h₂ : k₂ ≤ k₃) : k₁ ≤ k₃ :=
  Nat.le_trans h₁ h₂

theorem Kind.le_refl (k : Kind) : k ≤ k := Nat.le_refl _

/-! ### Usage modes -/

/-- Usage modes of an occurrence: ERASED (type/proof positions; no effect),
    READ (shared use, e.g. calling an `fn` value), MUT (`mutate`; unique
    non-consuming use, e.g. calling an `fnMut` value) and CONSUME (move). -/
inductive Mode : Type where
  | erased
  | read
  | mutate
  | consume
  deriving DecidableEq, Repr

/-- Position of a mode in the order `erased < read < mutate < consume`. -/
def Mode.rank : Mode → Nat
  | .erased => 0
  | .read => 1
  | .mutate => 2
  | .consume => 3

/-- `capmode k`: the strongest mode in which a closure of kind `k` may use a
    captured variable (Fn → READ, FnMut → MUT, FnOnce → CONSUME). -/
def capmode : Kind → Mode
  | .fn => .read
  | .fnMut => .mutate
  | .fnOnce => .consume

/-- `callmode k`: the mode in which calling a function value of kind `k` uses
    that value (Fn → READ, FnMut → MUT, FnOnce → CONSUME). -/
def callmode : Kind → Mode
  | .fn => .read
  | .fnMut => .mutate
  | .fnOnce => .consume

theorem callmode_eq_capmode (k : Kind) : callmode k = capmode k := by
  cases k <;> rfl

/-- The least kind whose capture mode admits a use of rank `r`:
    ranks 0–1 (ERASED/READ) need `fn`, rank 2 (MUT) needs `fnMut`,
    rank 3 (CONSUME) needs `fnOnce`. -/
def kindOfRank (r : Nat) : Kind :=
  if r ≤ 1 then .fn else if r = 2 then .fnMut else .fnOnce

theorem capmode_rank_mono {k k' : Kind} (h : k ≤ k') :
    (capmode k).rank ≤ (capmode k').rank := by
  cases k <;> cases k' <;> simp_all [Kind.le_def, Kind.rank, capmode, Mode.rank]

/-- Galois connection between `kindOfRank` and `capmode`: for a rank of
    an actual mode (`r ≤ 3`), the least admissible kind is below `k`
    exactly when `r` is below the capture mode of `k`. -/
theorem kindOfRank_le_iff {r : Nat} (hr : r ≤ 3) (k : Kind) :
    kindOfRank r ≤ k ↔ r ≤ (capmode k).rank := by
  cases k <;> simp only [kindOfRank, capmode, Mode.rank, Kind.le_def] <;>
    split <;> (try split) <;> simp [Kind.rank] <;> omega

/-! ### Types -/

/-- Types: `unit`, `nat`, owned resources `res`, kinded arrows. -/
inductive Ty : Type where
  | unit
  | nat
  | res
  | arr (k : Kind) (A B : Ty)
  deriving DecidableEq, Repr

/-- `Copy(T)`: `unit` and `nat` are duplicable; resources and function
    types are not. -/
def Ty.copy : Ty → Bool
  | .unit => true
  | .nat => true
  | .res => false
  | .arr _ _ _ => false

/-! ### Terms -/

/-- Terms in de Bruijn form. `letE A v b` is `let x : A = v in b`. -/
inductive Term : Type where
  | var (i : Nat)
  | unit
  | lit (n : Nat)
  | loc (l : Nat)
  | lam (k : Kind) (A : Ty) (b : Term)
  | app (f a : Term)
  | letE (A : Ty) (v b : Term)
  | consume (t : Term)
  | read (t : Term)
  | iter (n z s : Term)
  | ghost (t : Term)
  deriving DecidableEq, Repr

/-- Typing contexts: innermost binder first. -/
abbrev Ctx := List Ty

/-- Look up the type of de Bruijn index `n`. -/
def lookup : Ctx → Nat → Option Ty
  | [], _ => none
  | A :: _, 0 => some A
  | _ :: Γ, n + 1 => lookup Γ n

/-- Substitution of a closed value `v` for de Bruijn index `j`; indices above
    `j` are decremented.  `v` is not shifted under binders, which is correct
    because every substituted value is closed (see the module docstring). -/
def subst (j : Nat) (v : Term) : Term → Term
  | .var i => if i = j then v else if j < i then .var (i - 1) else .var i
  | .unit => .unit
  | .lit n => .lit n
  | .loc l => .loc l
  | .lam k A b => .lam k A (subst (j + 1) v b)
  | .app f a => .app (subst j v f) (subst j v a)
  | .letE A w b => .letE A (subst j v w) (subst (j + 1) v b)
  | .consume t => .consume (subst j v t)
  | .read t => .read (subst j v t)
  | .iter n z s => .iter (subst j v n) (subst j v z) (subst j v s)
  | .ghost t => .ghost (subst j v t)

/-- Values of the call-by-value semantics. -/
inductive Value : Term → Prop where
  | unit : Value .unit
  | lit (n : Nat) : Value (.lit n)
  | loc (l : Nat) : Value (.loc l)
  | lam (k : Kind) (A : Ty) (b : Term) : Value (.lam k A b)

/-! ### Lookup lemmas -/

theorem lookup_lt {Γ : Ctx} {i : Nat} {A : Ty} (h : lookup Γ i = some A) :
    i < Γ.length := by
  induction Γ generalizing i with
  | nil => simp [lookup] at h
  | cons B Γ ih =>
      cases i with
      | zero => simp
      | succ i => simp [lookup] at h; simpa using ih h

theorem lookup_append_lt (Γ₁ Γ₂ : Ctx) :
    ∀ i, i < Γ₁.length → lookup (Γ₁ ++ Γ₂) i = lookup Γ₁ i := by
  induction Γ₁ with
  | nil => intro i hi; simp at hi
  | cons B Γ₁ ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simp at hi; omega)

theorem lookup_append_ge (Γ₁ Γ₂ : Ctx) :
    ∀ i, Γ₁.length ≤ i → lookup (Γ₁ ++ Γ₂) i = lookup Γ₂ (i - Γ₁.length) := by
  induction Γ₁ with
  | nil => intro i _; simp
  | cons B Γ₁ ih =>
      intro i hi
      cases i with
      | zero => simp at hi
      | succ i =>
          simp only [List.cons_append, lookup, List.length_cons]
          rw [ih i (by simp at hi; omega)]
          congr 1
          omega

theorem lookup_mid (Γ₁ Γ₂ : Ctx) (A : Ty) :
    lookup (Γ₁ ++ A :: Γ₂) Γ₁.length = some A := by
  rw [lookup_append_ge _ _ _ (Nat.le_refl _)]
  simp [lookup]

theorem lookup_mid_lt (Γ₁ Γ₂ : Ctx) (A : Ty) {i : Nat} (h : i < Γ₁.length) :
    lookup (Γ₁ ++ A :: Γ₂) i = lookup (Γ₁ ++ Γ₂) i := by
  rw [lookup_append_lt _ _ _ h, lookup_append_lt _ _ _ h]

theorem lookup_mid_gt (Γ₁ Γ₂ : Ctx) (A : Ty) {i : Nat} (h : Γ₁.length < i) :
    lookup (Γ₁ ++ A :: Γ₂) i = lookup (Γ₁ ++ Γ₂) (i - 1) := by
  rw [lookup_append_ge _ _ _ (by omega), lookup_append_ge _ _ _ (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, i = Γ₁.length + k + 1 := ⟨i - Γ₁.length - 1, by omega⟩
  have e1 : Γ₁.length + k + 1 - Γ₁.length = k + 1 := by omega
  have e2 : Γ₁.length + k + 1 - 1 - Γ₁.length = k := by omega
  rw [e1, e2]
  rfl

/-- The index of a variable after substitution at position `j` removes the
    `j`-th binder (for `i ≠ j`). -/
theorem subst_var_ne {j i : Nat} (v : Term) (h : i ≠ j) :
    subst j v (.var i) = .var (if j < i then i - 1 else i) := by
  simp [subst, h]
  split <;> rfl

theorem lookup_subst_ne (Γ₁ Γ₂ : Ctx) (A : Ty) {i : Nat} (h : i ≠ Γ₁.length) :
    lookup (Γ₁ ++ Γ₂) (if Γ₁.length < i then i - 1 else i) = lookup (Γ₁ ++ A :: Γ₂) i := by
  split
  · rw [lookup_mid_gt _ _ _ (by assumption)]
  · rw [lookup_mid_lt _ _ _ (by omega)]

end LRL.Affine
