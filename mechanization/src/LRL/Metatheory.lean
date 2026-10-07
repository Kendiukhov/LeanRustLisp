import LRL.Syntax
import LRL.Reduction
import LRL.Typing

/-!
# LRL metatheory — simply-typed fragment

Proved lemmas about the STLC fragment defined in `Syntax.lean`,
`Reduction.lean`, and `Typing.lean`. Every theorem in this file is a
complete proof: no `sorry`, no `admit`. The file is designed around
context splitting `Γ₁ ++ Γ₂` rather than an `insertAt` function, because
`++` is total and avoids the edge cases of inserting into an empty
context at a nonzero position.

Lemmas proved (in dependency order):

1. `lookup_append_lt`      — lookup into `Γ₁ ++ Γ₂` when the index is inside `Γ₁`
2. `lookup_append_ge`      — lookup into `Γ₁ ++ Γ₂` when the index is ≥ `Γ₁.length`
3. `lookup_insert_ge`      — lookup above an inserted binding (index shifts by 1)
4. `lookup_insert_lt`      — lookup below an inserted binding (unchanged)
5. `typed_weaken_aux`      — weakening, auxiliary form with an explicit context equation
6. `typed_weaken`          — weakening: insert a binding at position `Γ₁.length`
7. `typed_weaken0`         — special case of weakening at position 0
8. `typed_subst_aux`       — substitution, auxiliary form with an explicit context equation
9. `typed_subst`           — substitution lemma at position `Γ₁.length`
10. `typed_subst0`         — special case of substitution at position 0
11. `typed_preservation`   — preservation under single-step β reduction
-/

namespace LRL

/-! ### Lookup lemmas on context splits -/

/-- Lookup inside the prefix of a context split. -/
theorem lookup_append_lt (Γ₁ Γ₂ : Context) :
    ∀ k, k < Γ₁.length → lookup (Γ₁ ++ Γ₂) k = lookup Γ₁ k := by
  intro k hk
  induction Γ₁ generalizing k with
  | nil =>
      exact absurd hk (Nat.not_lt_zero k)
  | cons τ Γ₁' ih =>
      cases k with
      | zero =>
          rfl
      | succ k' =>
          have hk' : k' < Γ₁'.length := Nat.lt_of_succ_lt_succ hk
          exact ih k' hk'

/-- Lookup into the suffix of a context split. Argument order `k + Γ₁.length`
    lines up with `lookup`'s pattern match on `n + 1`, making both cases
    definitional equalities. -/
theorem lookup_append_ge (Γ₁ Γ₂ : Context) :
    ∀ k, lookup (Γ₁ ++ Γ₂) (k + Γ₁.length) = lookup Γ₂ k := by
  induction Γ₁ with
  | nil =>
      intro k
      rfl
  | cons τ Γ₁' ih =>
      intro k
      exact ih k

/-- Inserting a new binding at position `Γ₁.length` shifts lookups: the
    variable that was at index `k + Γ₁.length` in `Γ₁ ++ Γ₂` is now at
    index `k + Γ₁.length + 1` in `Γ₁ ++ σ :: Γ₂`. -/
theorem lookup_insert_ge (Γ₁ Γ₂ : Context) (σ : Ty) :
    ∀ k, lookup (Γ₁ ++ σ :: Γ₂) (k + Γ₁.length + 1) = lookup Γ₂ k := by
  induction Γ₁ with
  | nil =>
      intro k
      -- Goal: lookup (σ :: Γ₂) (k + 0 + 1) = lookup Γ₂ k
      -- = lookup (σ :: Γ₂) (k + 1) = lookup Γ₂ k (by lookup cons/succ)
      rfl
  | cons τ Γ₁' ih =>
      intro k
      exact ih k

/-- Lookups below the insertion point are unaffected by inserting `σ`. -/
theorem lookup_insert_lt (Γ₁ Γ₂ : Context) (σ : Ty) :
    ∀ k, k < Γ₁.length →
      lookup (Γ₁ ++ σ :: Γ₂) k = lookup (Γ₁ ++ Γ₂) k := by
  intro k hk
  induction Γ₁ generalizing k with
  | nil =>
      exact absurd hk (Nat.not_lt_zero k)
  | cons τ Γ₁' ih =>
      cases k with
      | zero =>
          rfl
      | succ k' =>
          have hk' : k' < Γ₁'.length := Nat.lt_of_succ_lt_succ hk
          exact ih k' hk'

/-! ### Weakening -/

/-- Auxiliary form of weakening with an explicit equality on the context,
    so `induction ht` sees a bound variable `Γ` in the target rather than
    the compound index `Γ₁ ++ Γ₂`. -/
theorem typed_weaken_aux {Γ : Context} {t : Term} {τ : Ty}
    (ht : Typed Γ t τ) :
    ∀ (Γ₁ Γ₂ : Context) (σ : Ty),
      Γ = Γ₁ ++ Γ₂ →
      Typed (Γ₁ ++ σ :: Γ₂) (shift 1 Γ₁.length t) τ := by
  induction ht with
  | @var Γ' n τ' hn =>
      intro Γ₁ Γ₂ σ hΓ
      subst hΓ
      by_cases hlt : n < Γ₁.length
      · -- n < Γ₁.length: shift is a no-op; lookup unchanged
        simp [shift, hlt]
        apply Typed.var
        rw [lookup_insert_lt Γ₁ Γ₂ σ n hlt]
        exact hn
      · -- n ≥ Γ₁.length: shift adds 1; lookup_insert_ge applies
        simp [shift, hlt]
        apply Typed.var
        have hge : Γ₁.length ≤ n := Nat.le_of_not_lt hlt
        obtain ⟨k, rfl⟩ : ∃ k, n = k + Γ₁.length := ⟨n - Γ₁.length, by omega⟩
        rw [lookup_insert_ge Γ₁ Γ₂ σ k]
        rw [← lookup_append_ge Γ₁ Γ₂ k]
        exact hn
  | @lam Γ' τ₁ τ₂ b _ ih =>
      intro Γ₁ Γ₂ σ hΓ
      subst hΓ
      simp [shift]
      apply Typed.lam
      -- Instantiate IH with Γ₁ := τ₁ :: Γ₁, same Γ₂, same σ
      exact ih (τ₁ :: Γ₁) Γ₂ σ rfl
  | @app Γ' f a τ₁ τ₂ _ _ ihf iha =>
      intro Γ₁ Γ₂ σ hΓ
      subst hΓ
      simp [shift]
      exact Typed.app (ihf Γ₁ Γ₂ σ rfl) (iha Γ₁ Γ₂ σ rfl)

/-- Weakening: inserting a binding at position `Γ₁.length` preserves typing
    after shifting free variables at that position or above. -/
theorem typed_weaken (Γ₁ Γ₂ : Context) (σ : Ty) (t : Term) (τ : Ty)
    (ht : Typed (Γ₁ ++ Γ₂) t τ) :
    Typed (Γ₁ ++ σ :: Γ₂) (shift 1 Γ₁.length t) τ :=
  typed_weaken_aux ht Γ₁ Γ₂ σ rfl

/-- The canonical special case: weakening at position 0. -/
theorem typed_weaken0 (Γ : Context) (σ : Ty) (t : Term) (τ : Ty)
    (ht : Typed Γ t τ) :
    Typed (σ :: Γ) (shift 1 0 t) τ :=
  typed_weaken [] Γ σ t τ ht

/-! ### Substitution

The substitution lemma is stated with `s` already typed in the *flattened*
context `Γ₁ ++ Γ₂`. Callers who have `s : Γ₂` must pre-shift before using
this form; `typed_subst0` below is the common case with `Γ₁ = []`, where
no pre-shifting is needed.
-/

/-- Auxiliary substitution lemma with explicit equality on the context. -/
theorem typed_subst_aux {Γ : Context} {t : Term} {τ : Ty}
    (ht : Typed Γ t τ) :
    ∀ (Γ₁ Γ₂ : Context) (σ : Ty) (s : Term),
      Γ = Γ₁ ++ σ :: Γ₂ →
      Typed (Γ₁ ++ Γ₂) s σ →
      Typed (Γ₁ ++ Γ₂) (subst Γ₁.length s t) τ := by
  induction ht with
  | @var Γ' n τ' hn =>
      intro Γ₁ Γ₂ σ s hΓ hs
      subst hΓ
      rcases Nat.lt_trichotomy n Γ₁.length with hlt | heq | hgt
      · -- n < Γ₁.length: subst leaves var n alone; lookup below insertion
        simp [subst, Nat.ne_of_lt hlt, Nat.not_lt_of_lt hlt]
        apply Typed.var
        rw [← lookup_insert_lt Γ₁ Γ₂ σ n hlt]
        exact hn
      · -- n = Γ₁.length: substitution replaces with s
        subst heq
        simp [subst]
        -- lookup at the insertion position is σ.
        have hlook : lookup (Γ₁ ++ σ :: Γ₂) Γ₁.length = some σ := by
          have h := lookup_append_ge Γ₁ (σ :: Γ₂) 0
          -- h : lookup (Γ₁ ++ σ :: Γ₂) (0 + Γ₁.length) = lookup (σ :: Γ₂) 0
          -- lookup (σ :: Γ₂) 0 = some σ
          -- 0 + Γ₁.length = Γ₁.length
          -- `lookup` is unfolded explicitly: under Lean 4.34.1 a bare
          -- `simpa using h` leaves `lookup (σ :: Γ₂) 0` unreduced.
          simpa [lookup] using h
        rw [hlook] at hn
        -- Now hn : some σ = some τ', so τ' = σ
        have hτσ : τ' = σ := by
          injection hn with h
          exact h.symm
        subst hτσ
        -- Goal: Typed (Γ₁ ++ Γ₂) s σ; that's hs directly.
        exact hs
      · -- n > Γ₁.length: subst leaves var (n-1); lookup above insertion
        have hne : n ≠ Γ₁.length := Nat.ne_of_gt hgt
        have hnle : ¬ (n < Γ₁.length) := Nat.not_lt_of_lt hgt
        simp [subst, hne, hgt]
        apply Typed.var
        -- From hn : lookup (Γ₁ ++ σ :: Γ₂) n = some τ'
        -- With n = k + Γ₁.length + 1 for k = n - Γ₁.length - 1
        obtain ⟨k, rfl⟩ : ∃ k, n = k + Γ₁.length + 1 :=
          ⟨n - Γ₁.length - 1, by omega⟩
        -- Goal: lookup (Γ₁ ++ Γ₂) (k + Γ₁.length + 1 - 1) = some τ'
        -- Simplify the index: k + Γ₁.length + 1 - 1 = k + Γ₁.length
        have hidx : k + Γ₁.length + 1 - 1 = k + Γ₁.length := by omega
        rw [hidx]
        rw [lookup_append_ge Γ₁ Γ₂ k]
        -- Goal: lookup Γ₂ k = some τ'
        rw [lookup_insert_ge Γ₁ Γ₂ σ k] at hn
        exact hn
  | @lam Γ' τ₁ τ₂ b _ ih =>
      intro Γ₁ Γ₂ σ s hΓ hs
      subst hΓ
      simp [subst]
      apply Typed.lam
      -- Extend the split: Γ₁' := τ₁ :: Γ₁; s shifts by 1 at position 0.
      have hs' : Typed (τ₁ :: (Γ₁ ++ Γ₂)) (shift 1 0 s) σ :=
        typed_weaken0 (Γ₁ ++ Γ₂) τ₁ s σ hs
      -- Goal after simp: Typed (τ₁ :: Γ₁ ++ Γ₂) (subst (Γ₁.length + 1) (shift 1 0 s) b) τ₂
      -- which matches ih with Γ₁ := τ₁ :: Γ₁, Γ₂ := Γ₂, σ := σ, s := shift 1 0 s.
      exact ih (τ₁ :: Γ₁) Γ₂ σ (shift 1 0 s) rfl hs'
  | @app Γ' f a τ₁ τ₂ _ _ ihf iha =>
      intro Γ₁ Γ₂ σ s hΓ hs
      subst hΓ
      simp [subst]
      exact Typed.app (ihf Γ₁ Γ₂ σ s rfl hs) (iha Γ₁ Γ₂ σ s rfl hs)

/-- Substitution lemma (general form): replacing the binding at position
    `Γ₁.length` with a term `s : σ` (typed in the flattened context) preserves
    typing. -/
theorem typed_subst (Γ₁ Γ₂ : Context) (σ : Ty) (s t : Term) (τ : Ty)
    (ht : Typed (Γ₁ ++ σ :: Γ₂) t τ)
    (hs : Typed (Γ₁ ++ Γ₂) s σ) :
    Typed (Γ₁ ++ Γ₂) (subst Γ₁.length s t) τ :=
  typed_subst_aux ht Γ₁ Γ₂ σ s rfl hs

/-- Substitution lemma (position 0 form): the common case used by β reduction. -/
theorem typed_subst0 (Γ : Context) (σ : Ty) (s t : Term) (τ : Ty)
    (ht : Typed (σ :: Γ) t τ)
    (hs : Typed Γ s σ) :
    Typed Γ (subst 0 s t) τ :=
  typed_subst [] Γ σ s t τ ht hs

/-! ### Preservation -/

/-- Preservation under a single β-step. If `t` is well-typed and `t` steps
    to `t'`, then `t'` is well-typed with the same type in the same context. -/
theorem typed_preservation {Γ : Context} {t t' : Term} {τ : Ty}
    (ht : Typed Γ t τ) (hstep : Step t t') :
    Typed Γ t' τ := by
  induction ht generalizing t' with
  | @var Γ n τ hn =>
      cases hstep
  | @lam Γ τ₁ τ₂ b hb ih =>
      cases hstep with
      | lamCg hb' =>
          exact Typed.lam (ih hb')
  | @app Γ f a τ₁ τ₂ hf ha ihf iha =>
      cases hstep with
      | @beta τ_b b =>
          -- After unification: f := lam τ_b b, t' := subst 0 a b
          -- hf : Typed Γ (lam τ_b b) (arrow τ₁ τ₂)
          cases hf with
          | @lam _ _ _ _ hb =>
              -- From Typed.lam, τ_b = τ₁ and hb : Typed (τ₁ :: Γ) b τ₂
              exact typed_subst0 Γ τ₁ a b τ₂ hb ha
      | appL hf' =>
          exact Typed.app (ihf hf') ha
      | appR ha' =>
          exact Typed.app hf (iha ha')

end LRL
