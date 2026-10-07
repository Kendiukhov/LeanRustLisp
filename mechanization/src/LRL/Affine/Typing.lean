import LRL.Affine.Syntax

/-!
# Affine core with function kinds — typing

`Typed Γ t A`.  As in the LRL kernel there is no kind subsumption: a
`lam k A b` has type `arr k A B` for exactly its own kind `k`.  Kind
coercion is done by the elaborator, by re-annotating a λ or by η-expansion
(theorems `kind_widening` and `eta_coercion` in `Affine/Ownership.lean`,
`eta_coercion_general` in `Affine/Coercion.lean`).  The kind side condition
of a λ (its required kind) is part of the ownership judgment
(`Affine/Ownership.lean`), not of typing.

The iterator `iter n z s : C` (a recursor on `Nat` without the
predecessor argument) types its step function as `arr k C C` for any kind
`k`: as in the kernel, the recursor type does not constrain the kind of a
minor premise.  The invocation-count discipline (the step function runs
once per predecessor, so it may not consume values bound outside it) is an
ownership rule, `Own.iter` in `Affine/Ownership.lean`.
-/

namespace LRL.Affine

/-- Typing judgment. -/
inductive Typed : Ctx → Term → Ty → Prop where
  | var {Γ i A} : lookup Γ i = some A → Typed Γ (.var i) A
  | unit {Γ} : Typed Γ .unit .unit
  | lit {Γ n} : Typed Γ (.lit n) .nat
  | loc {Γ l} : Typed Γ (.loc l) .res
  | lam {Γ k A B b} : Typed (A :: Γ) b B → Typed Γ (.lam k A b) (.arr k A B)
  | app {Γ k A B f a} : Typed Γ f (.arr k A B) → Typed Γ a A → Typed Γ (.app f a) B
  | letE {Γ A B v b} : Typed Γ v A → Typed (A :: Γ) b B → Typed Γ (.letE A v b) B
  | consume {Γ t} : Typed Γ t .res → Typed Γ (.consume t) .unit
  | read {Γ t} : Typed Γ t .res → Typed Γ (.read t) .nat
  | iter {Γ k C n z s} :
      Typed Γ n .nat → Typed Γ z C → Typed Γ s (.arr k C C) →
      Typed Γ (.iter n z s) C
  | ghost {Γ A t} : Typed Γ t A → Typed Γ (.ghost t) .unit

/-- Weakening at the end of the context (no shifting needed). -/
theorem typed_append {Γ : Ctx} {t : Term} {A : Ty} (h : Typed Γ t A) :
    ∀ Δ, Typed (Γ ++ Δ) t A := by
  induction h with
  | var hl => intro Δ; exact .var (by rw [lookup_append_lt _ _ _ (lookup_lt hl)]; exact hl)
  | unit => intro Δ; exact .unit
  | lit => intro Δ; exact .lit
  | loc => intro Δ; exact .loc
  | lam _ ih => intro Δ; exact .lam (ih Δ)
  | app _ _ ihf iha => intro Δ; exact .app (ihf Δ) (iha Δ)
  | letE _ _ ihv ihb => intro Δ; exact .letE (ihv Δ) (ihb Δ)
  | consume _ ih => intro Δ; exact .consume (ih Δ)
  | read _ ih => intro Δ; exact .read (ih Δ)
  | iter _ _ _ ihn ihz ihs => intro Δ; exact .iter (ihn Δ) (ihz Δ) (ihs Δ)
  | ghost _ ih => intro Δ; exact .ghost (ih Δ)

/-- A closed term is typable in every context. -/
theorem typed_closed {t : Term} {A : Ty} (h : Typed [] t A) (Γ : Ctx) : Typed Γ t A := by
  simpa using typed_append h Γ

/-- **Value substitution for typing** (closed values). -/
theorem typed_subst {v : Term} {A : Ty} (hv : Typed [] v A) :
    ∀ {Γ t B}, Typed Γ t B → ∀ Γ₁ Γ₂, Γ = Γ₁ ++ A :: Γ₂ →
      Typed (Γ₁ ++ Γ₂) (subst Γ₁.length v t) B := by
  intro Γ t B h
  induction h with
  | @var Γ i B hl =>
      intro Γ₁ Γ₂ hΓ
      subst hΓ
      by_cases hij : i = Γ₁.length
      · subst hij
        rw [lookup_mid] at hl
        cases hl
        simp [subst]
        exact typed_closed hv _
      · rw [subst_var_ne v hij]
        exact .var (by rw [lookup_subst_ne Γ₁ Γ₂ A hij]; exact hl)
  | unit => intro _ _ _; exact .unit
  | lit => intro _ _ _; exact .lit
  | loc => intro _ _ _; exact .loc
  | @lam Γ k A' B b _ ih =>
      intro Γ₁ Γ₂ hΓ
      subst hΓ
      exact .lam (ih (A' :: Γ₁) Γ₂ rfl)
  | app _ _ ihf iha =>
      intro Γ₁ Γ₂ hΓ
      exact .app (ihf Γ₁ Γ₂ hΓ) (iha Γ₁ Γ₂ hΓ)
  | @letE Γ A' B w b _ _ ihw ihb =>
      intro Γ₁ Γ₂ hΓ
      subst hΓ
      exact .letE (ihw Γ₁ Γ₂ rfl) (ihb (A' :: Γ₁) Γ₂ rfl)
  | consume _ ih => intro Γ₁ Γ₂ hΓ; exact .consume (ih Γ₁ Γ₂ hΓ)
  | read _ ih => intro Γ₁ Γ₂ hΓ; exact .read (ih Γ₁ Γ₂ hΓ)
  | iter _ _ _ ihn ihz ihs =>
      intro Γ₁ Γ₂ hΓ
      exact .iter (ihn Γ₁ Γ₂ hΓ) (ihz Γ₁ Γ₂ hΓ) (ihs Γ₁ Γ₂ hΓ)
  | ghost _ ih => intro Γ₁ Γ₂ hΓ; exact .ghost (ih Γ₁ Γ₂ hΓ)

/-- Substitution at position 0 (the β / let case). -/
theorem typed_subst0 {v b : Term} {A B : Ty} (hv : Typed [] v A) (hb : Typed [A] b B) :
    Typed [] (subst 0 v b) B :=
  typed_subst hv hb [] [] rfl

/-! ### Canonical forms -/

theorem canonical_res {Γ v} (hv : Value v) (h : Typed Γ v .res) : ∃ l, v = .loc l := by
  cases hv <;> cases h; exact ⟨_, rfl⟩

theorem canonical_nat {Γ v} (hv : Value v) (h : Typed Γ v .nat) : ∃ n, v = .lit n := by
  cases hv <;> cases h; exact ⟨_, rfl⟩

theorem canonical_unit {Γ v} (hv : Value v) (h : Typed Γ v .unit) : v = .unit := by
  cases hv <;> cases h; rfl

theorem canonical_arr {Γ v k A B} (hv : Value v) (h : Typed Γ v (.arr k A B)) :
    ∃ b, v = .lam k A b ∧ Typed (A :: Γ) b B := by
  cases hv <;> cases h; exact ⟨_, rfl, by assumption⟩

/-- Closed values of a Copy type are `unit` or literals. -/
theorem canonical_copy {Γ v A} (hv : Value v) (h : Typed Γ v A) (hc : A.copy = true) :
    v = .unit ∨ ∃ n, v = .lit n := by
  cases hv <;> cases h <;> simp_all [Ty.copy]

end LRL.Affine
