import LRL.Affine.Syntax
import LRL.Affine.Typing
import LRL.Affine.Ownership

/-!
# Affine core with function kinds — value substitution (T3)

Substituting a closed **value** `v : A` for a variable `x : A` preserves the
ownership judgment.  The usage state of the result is the original state
with `x` deleted (`St.sub`); if `x` had been moved, the locations consumed
by `v` count as moved instead.

Why only values.  A value of a Copy type (`unit`, a literal) uses nothing; a
value of type `res` is a location, used exactly in the mode in which `x` was
used; a value of an arrow type `A →[k] B` is a λ whose own side condition
bounds its demand by `capmode k`, which is the mode of every call of `x`.  So
the demand of every λ around an occurrence of `x` cannot grow
(`dem_subst_le`) and the kind side conditions survive.  An arbitrary term of
type `A` can have a larger demand than `x`: substituting the non-value
`consume (loc 0) : unit` for a Copy variable inside an `fn` closure yields a
closure that consumes a resource each time it is called, which violates the
side condition (`Affine/Examples.lean`, `subst_nonvalue_breaks_side_condition`).
-/

namespace LRL.Affine

/-! ### Modes compatible with a type -/

/-- The modes in which a variable of type `A` can occur in a well-typed term:
    a variable of arrow type `A →[k] B` is either called (`callmode k`) or
    consumed (passed, bound, iterated); other types are unconstrained. -/
def ModeOK : Ty → Mode → Prop
  | .arr k _ _, m => m = .consume ∨ m = callmode k
  | _, _ => True

theorem modeOK_consume (A : Ty) : ModeOK A .consume := by
  cases A <;> simp [ModeOK]

theorem modeOK_headMode {Γ f k A B} (hf : Typed Γ f (.arr k A B)) :
    ModeOK (.arr k A B) (headMode Γ f) := by
  cases f with
  | var i =>
      cases hf with
      | var hl => right; exact headMode_var_arr hl
  | _ => left; rfl

theorem callmode_ne_erased (k : Kind) : callmode k ≠ .erased := by
  cases k <;> simp [callmode]

/-! ### Context independence (typing-based) -/

theorem headMode_append {Γ f B} (h : Typed Γ f B) (Δ : Ctx) :
    headMode (Γ ++ Δ) f = headMode Γ f :=
  headMode_append_of_lt Γ Δ f (fun i hi => by subst hi; cases h with | var hl => exact lookup_lt hl)

/-- The demand of a term counts no variable of its own context once the
    threshold covers that context; it then depends neither on the rest of the
    context nor on the exact threshold. -/
theorem dem_ctx {Γ₀ t B} (h : Typed Γ₀ t B) :
    ∀ Δ Δ' d d' m, Γ₀.length ≤ d → Γ₀.length ≤ d' →
      dem (Γ₀ ++ Δ) d t m = dem (Γ₀ ++ Δ') d' t m := by
  induction h with
  | var hl =>
      intro Δ Δ' d d' m hd hd'
      have := lookup_lt hl
      simp only [dem]
      rw [ite_eq_left (show _ < d by omega), ite_eq_left (show _ < d' by omega)]
  | unit | lit | loc => intro _ _ _ _ _ _ _; simp [dem]
  | lam _ ih =>
      intro Δ Δ' d d' m hd hd'
      simp only [dem]
      exact ih Δ Δ' (d + 1) (d' + 1) .consume (by simp; omega) (by simp; omega)
  | app hf _ ihf iha =>
      intro Δ Δ' d d' m hd hd'
      simp only [dem]
      rw [headMode_append hf Δ, headMode_append hf Δ', ihf Δ Δ' d d' _ hd hd',
        iha Δ Δ' d d' _ hd hd']
  | letE _ _ ihv ihb =>
      intro Δ Δ' d d' m hd hd'
      simp only [dem]
      rw [ihv Δ Δ' d d' _ hd hd']
      exact congrArg _ (ihb Δ Δ' (d + 1) (d' + 1) .consume (by simp; omega) (by simp; omega))
  | consume _ ih => intro Δ Δ' d d' m hd hd'; simp only [dem]; exact ih Δ Δ' d d' _ hd hd'
  | read _ ih => intro Δ Δ' d d' m hd hd'; simp only [dem]; exact ih Δ Δ' d d' _ hd hd'
  | iter _ _ _ ihn ihz ihs =>
      intro Δ Δ' d d' m hd hd'
      simp only [dem]
      rw [ihn Δ Δ' d d' _ hd hd', ihz Δ Δ' d d' _ hd hd', ihs Δ Δ' d d' _ hd hd']
  | ghost _ _ => intro _ _ _ _ _ _ _; simp [dem]

/-! ### Properties of closed values -/

/-- The side condition of a closed λ value, extracted from its derivation. -/
theorem value_side {v U U'} (hvo : Own [] U v .consume U') :
    ∀ k A b, v = .lam k A b → dem [A] 1 b .consume ≤ (capmode k).rank := by
  intro k A b hv
  subst hv
  cases hvo with
  | lam _ hd => exact hd

/-- The demand of a closed value used in a mode compatible with its type is
    at most that of a variable of the same type. -/
theorem value_dem_le {v A} (hval : Value v) (hvt : Typed [] v A)
    (hside : ∀ k A' b, v = .lam k A' b → dem [A'] 1 b .consume ≤ (capmode k).rank)
    {m : Mode} (hm : ModeOK A m) (Γ : Ctx) (d : Nat) :
    dem Γ d v m ≤ effRank (some A) m := by
  cases hval with
  | unit => simp [dem]
  | lit => simp [dem]
  | loc => cases hvt; simp [dem, effRank, Ty.copy]
  | lam k A' b =>
      cases hvt with
      | lam hb =>
          simp only [dem]
          have e := dem_ctx hb Γ [] (d + 1) 1 .consume (by simp) (by simp)
          simp only [List.cons_append, List.nil_append] at e
          rw [e]
          have hs := hside k A' b rfl
          simp only [effRank, Ty.copy, Bool.false_eq_true, false_and, ite_false]
          rcases hm with rfl | rfl
          · have := dem_le_three [A'] 1 b .consume; simp [Mode.rank]; omega
          · rw [callmode_eq_capmode]; exact hs

/-- Consumption by a closed value used in a compatible mode: only a consuming
    use of a non-Copy value consumes anything. -/
theorem value_cl_mode {v A} (hval : Value v) (hvt : Typed [] v A)
    (hside : ∀ k A' b, v = .lam k A' b → dem [A'] 1 b .consume ≤ (capmode k).rank)
    {m : Mode} (hm : ModeOK A m) (l : Nat) :
    cl l v m = if m = .consume ∧ A.copy = false then cl l v .consume else 0 := by
  cases hval with
  | unit => cases hvt; simp [cl]
  | lit => cases hvt; simp [cl]
  | loc r =>
      cases hvt
      by_cases hmc : m = .consume
      · subst hmc; simp [Ty.copy]
      · simp [cl, hmc, useC, Ty.copy]
  | lam k A' b =>
      cases hvt
      by_cases hmc : m = .consume
      · subst hmc; simp [Ty.copy]
      · simp only [hmc, false_and, ite_false]
        rcases hm with h | h
        · exact absurd h hmc
        · have hs := hside k A' b rfl
          have hk : (capmode k).rank ≤ 2 := by
            cases k <;> simp_all [callmode, capmode, Mode.rank]
          exact cl_lam_of_dem (Γ := []) (by omega) l m

/-! ### Substitution and heads -/

theorem subst_nonvar {j : Nat} {v t : Term} (h : ∀ i, t ≠ .var i) : ∀ i, subst j v t ≠ .var i := by
  cases t <;> simp_all [subst]

/-- After substituting a value, the head of an application is either used in
    the same mode as before or has become a λ (whose judgment does not depend
    on the mode). -/
theorem headMode_subst {v A Γ₁ Γ₂ f k A₁ B} (hval : Value v) (hvt : Typed [] v A)
    (hf : Typed (Γ₁ ++ A :: Γ₂) f (.arr k A₁ B)) :
    headMode (Γ₁ ++ Γ₂) (subst Γ₁.length v f) = headMode (Γ₁ ++ A :: Γ₂) f ∨
      ∃ k' A' b, subst Γ₁.length v f = .lam k' A' b := by
  cases f with
  | var i =>
      cases hf with
      | var hl =>
          by_cases hij : i = Γ₁.length
          · subst hij
            rw [lookup_mid] at hl
            cases hl
            right
            obtain ⟨b, hb, _⟩ := canonical_arr hval hvt
            exact ⟨k, A₁, b, by simp [subst, hb]⟩
          · left
            rw [subst_var_ne v hij]
            simp only [headMode, lookup_subst_ne Γ₁ Γ₂ A hij]
  | _ =>
      left
      rw [headMode_nonvar (subst_nonvar (by simp)), headMode_nonvar (by simp)]

/-! ### Demand does not grow under value substitution -/

theorem dem_subst_le {v A} (hval : Value v) (hvt : Typed [] v A)
    (hside : ∀ k A' b, v = .lam k A' b → dem [A'] 1 b .consume ≤ (capmode k).rank) :
    ∀ {Γ t B}, Typed Γ t B → ∀ m, ModeOK B m → ∀ Γ₁ Γ₂ d, Γ = Γ₁ ++ A :: Γ₂ →
      d ≤ Γ₁.length → dem (Γ₁ ++ Γ₂) d (subst Γ₁.length v t) m ≤ dem Γ d t m := by
  intro Γ t B h
  induction h with
  | @var Γ i B hl =>
      intro m hm Γ₁ Γ₂ d hΓ hd
      subst hΓ
      by_cases hij : i = Γ₁.length
      · subst hij
        rw [lookup_mid] at hl
        cases hl
        simp only [subst, ite_true, dem, ite_eq_right (show ¬ (Γ₁.length < d) by omega), lookup_mid]
        exact value_dem_le hval hvt hside hm _ _
      · rw [subst_var_ne v hij]
        simp only [dem, lookup_subst_ne Γ₁ Γ₂ A hij]
        by_cases hji : Γ₁.length < i
        · simp only [hji, ite_true]
          rw [ite_eq_right (show ¬ (i - 1 < d) by omega), ite_eq_right (show ¬ (i < d) by omega)]
          exact Nat.le_refl _
        · simp only [hji, ite_false]
          exact Nat.le_refl _
  | unit | lit | loc => intro _ _ _ _ _ _ _; simp [subst, dem]
  | @lam Γ k A' B' b hb ih =>
      intro m hm Γ₁ Γ₂ d hΓ hd
      subst hΓ
      simp only [subst, dem]
      exact ih .consume (modeOK_consume _) (A' :: Γ₁) Γ₂ (d + 1) rfl (by simp; omega)
  | @app Γ k A₁ B f a hf ha ihf iha =>
      intro m hm Γ₁ Γ₂ d hΓ hd
      subst hΓ
      simp only [subst, dem]
      have h1 := ihf _ (modeOK_headMode hf) Γ₁ Γ₂ d rfl hd
      have h2 := iha .consume (modeOK_consume _) Γ₁ Γ₂ d rfl hd
      rcases headMode_subst hval hvt hf with he | ⟨k', A', b, he⟩
      · rw [he]; omega
      · have : dem (Γ₁ ++ Γ₂) d (subst Γ₁.length v f) (headMode (Γ₁ ++ Γ₂) (subst Γ₁.length v f)) =
            dem (Γ₁ ++ Γ₂) d (subst Γ₁.length v f) (headMode (Γ₁ ++ A :: Γ₂) f) := by
          rw [he]; simp [dem]
        omega
  | @letE Γ A' B w b hw hb ihw ihb =>
      intro m hm Γ₁ Γ₂ d hΓ hd
      subst hΓ
      simp only [subst, dem]
      have h1 := ihw .consume (modeOK_consume _) Γ₁ Γ₂ d rfl hd
      have h2 := ihb .consume (modeOK_consume _) (A' :: Γ₁) Γ₂ (d + 1) rfl (by simp; omega)
      simp only [List.cons_append, List.length_cons] at h2
      omega
  | consume _ ih =>
      intro m hm Γ₁ Γ₂ d hΓ hd
      simp only [subst, dem]; exact ih .consume trivial Γ₁ Γ₂ d hΓ hd
  | read _ ih =>
      intro m hm Γ₁ Γ₂ d hΓ hd
      simp only [subst, dem]; exact ih .read trivial Γ₁ Γ₂ d hΓ hd
  | iter _ _ _ ihn ihz ihs =>
      intro m hm Γ₁ Γ₂ d hΓ hd
      simp only [subst, dem]
      have h1 := ihn .consume trivial Γ₁ Γ₂ d hΓ hd
      have h2 := ihz .consume (modeOK_consume _) Γ₁ Γ₂ d hΓ hd
      have h3 := ihs .consume (modeOK_consume _) Γ₁ Γ₂ d hΓ hd
      omega
  | ghost _ _ => intro _ _ _ _ _ _ _; simp [subst, dem]

/-! ### The state map of a substitution -/

/-- `St.sub j v S`: delete variable `j` from the state; if it had been moved,
    the locations consumed by the value `v` substituted for it are moved. -/
def St.sub (j : Nat) (v : Term) (S : St) : St :=
  ⟨fun i => if i < j then S.v i else S.v (i + 1), fun l => S.l l || (S.v j && pos (cl l v .consume))⟩

theorem St.sub_push (j : Nat) (v : Term) (S : St) :
    St.sub (j + 1) v S.push = (St.sub j v S).push := by
  apply St.ext
  · funext i
    cases i with
    | zero => simp [St.sub]
    | succ i =>
        simp only [St.sub, St.push_v_succ]
        by_cases h : i < j
        · simp [h]
        · simp [h]
  · funext l; simp [St.sub]

theorem St.sub_pop (j : Nat) (v : Term) (S : St) :
    (St.sub (j + 1) v S).pop = St.sub j v S.pop := by
  apply St.ext
  · funext i
    simp only [St.sub, St.pop_v]
    by_cases h : i < j
    · simp [h]
    · simp [h]
  · funext l; simp [St.sub]

theorem St.sub_v_ne (j : Nat) (v : Term) (S : St) {i : Nat} (h : i ≠ j) :
    (St.sub j v S).v (if j < i then i - 1 else i) = S.v i := by
  simp only [St.sub]
  by_cases hji : j < i
  · simp only [hji, ite_true]
    rw [ite_eq_right (show ¬ (i - 1 < j) by omega), show i - 1 + 1 = i by omega]
  · simp only [hji, ite_false]
    rw [ite_eq_left (show i < j by omega)]

theorem St.sub_moveV_ne (j : Nat) (v : Term) (S : St) {i : Nat} (h : i ≠ j) :
    St.sub j v (S.moveV i) = (St.sub j v S).moveV (if j < i then i - 1 else i) := by
  apply St.ext
  · funext x
    simp only [St.sub, St.moveV_v]
    by_cases hx : x < j
    · simp only [hx, ite_true]
      by_cases hji : j < i
      · simp [hji, show x ≠ i by omega, show x ≠ i - 1 by omega]
      · simp [hji]
    · simp only [hx, ite_false]
      by_cases hji : j < i
      · simp only [hji, ite_true]
        by_cases hxi : x + 1 = i
        · subst hxi; simp
        · simp [hxi, show x ≠ i - 1 by omega]
      · simp [hji, show x + 1 ≠ i by omega, show x ≠ i by omega]
  · funext l
    simp [St.sub, Ne.symm h]

theorem St.sub_moveL (j : Nat) (v : Term) (S : St) (r : Nat) :
    St.sub j v (S.moveL r) = (St.sub j v S).moveL r := by
  apply St.ext
  · rfl
  · funext l
    simp only [St.sub, St.moveL_l, St.moveL_v]
    split <;> simp

theorem St.sub_zero_push (v : Term) (S : St) : St.sub 0 v S.push = S := by
  apply St.ext
  · funext i; simp [St.sub]
  · funext l; simp [St.sub]

/-! ### T3: value substitution for the ownership judgment -/

/-- **(T3) Value substitution.**  Let `v` be a closed, well-typed value of
    type `A` that is well-owned in some state.  If `t` is well-typed and
    well-owned in a context binding `x : A` at position `|Γ₁|`, used in a mode
    compatible with its type, and the locations consumed by `v` are not moved
    by the end of `t`, then `t[v/x]` is well-owned in the context without `x`,
    from and to the states with `x` deleted (`St.sub`). -/
theorem own_subst {v A U U'} (hval : Value v) (hvt : Typed [] v A) (hvo : Own [] U v .consume U') :
    ∀ {Γ S t m S'}, Own Γ S t m S' → ∀ {B}, Typed Γ t B → ModeOK B m →
      ∀ Γ₁ Γ₂, Γ = Γ₁ ++ A :: Γ₂ → (∀ l, 0 < cl l v .consume → S'.l l = false) →
      Own (Γ₁ ++ Γ₂) (St.sub Γ₁.length v S) (subst Γ₁.length v t) m (St.sub Γ₁.length v S') := by
  have hside := value_side hvo
  intro Γ S t m S' h
  induction h with
  | @var Γ S i A₀ m hl hreq =>
      intro B ht hm Γ₁ Γ₂ hΓ hfree
      subst hΓ
      cases ht with
      | var hl' =>
          rw [hl] at hl'
          cases hl'
          by_cases hij : i = Γ₁.length
          · subst hij
            rw [lookup_mid] at hl
            cases hl
            simp only [subst, ite_true]
            have hcl := value_cl_mode hval hvt hside hm
            have hfree' : ∀ l, 0 < cl l v m → (St.sub Γ₁.length v S).l l = false := by
              intro l hl
              rw [hcl l] at hl
              split at hl
              · rename_i hc
                have h1 := hfree l hl
                rw [ite_eq_left hc] at h1
                simp only [St.moveV_l] at h1
                simp only [St.sub, h1, hreq (by rw [hc.1]; simp), Bool.false_and, Bool.or_false]
              · omega
            refine (own_value hval hvo _ _ m hfree').cast ?_
            apply St.ext
            · funext x
              simp only [St.sub]
              by_cases hx : x < Γ₁.length
              · simp only [hx, ite_true]; split <;> simp [show x ≠ Γ₁.length by omega]
              · simp only [hx, ite_false]; split <;> simp [show x + 1 ≠ Γ₁.length by omega]
            · funext l
              dsimp only
              rw [hcl l]
              by_cases hc : m = .consume ∧ A.copy = false
              · have hj := hreq (by rw [hc.1]; simp)
                simp [St.sub, hc, hj]
              · simp [St.sub, hc]
          · rw [subst_var_ne v hij]
            refine (Own.var (by rw [lookup_subst_ne Γ₁ Γ₂ A hij]; exact hl)
              (fun hme => by rw [St.sub_v_ne _ _ _ hij]; exact hreq hme)).cast ?_
            split
            · exact (St.sub_moveV_ne _ _ _ hij).symm
            · rfl
  | @loc Γ S r m hreq =>
      intro B ht hm Γ₁ Γ₂ hΓ hfree
      refine (Own.loc (fun hmc => ?_)).cast ?_
      · have h1 := hreq hmc
        have h2 : cl r v .consume = 0 := by
          by_cases hc : 0 < cl r v .consume
          · have := hfree r hc; simp [hmc] at this
          · omega
        simp [St.sub, h1, h2]
      · split
        · exact (St.sub_moveL _ _ _ _).symm
        · rfl
  | unit => intros; exact .unit
  | lit => intros; exact .lit
  | ghost => intros; exact .ghost
  | @lam Γ S S'' k A' b m hb hd ih =>
      intro B ht hm Γ₁ Γ₂ hΓ hfree
      subst hΓ
      cases ht with
      | @lam _ _ _ B' _ hbt =>
          have ih' := ih hbt (modeOK_consume _) (A' :: Γ₁) Γ₂ rfl
            (fun l hl => by simpa using hfree l hl)
          simp only [List.length_cons, List.cons_append] at ih'
          rw [St.sub_push] at ih'
          have hd' := dem_subst_le hval hvt hside hbt .consume (modeOK_consume _) (A' :: Γ₁) Γ₂ 1
            rfl (by simp)
          simp only [List.length_cons, List.cons_append] at hd'
          exact (Own.lam ih' (Nat.le_trans hd' hd)).cast (St.sub_pop _ _ _)
  | @app Γ S S₁ S₂ f a m hf ha ihf iha =>
      intro B ht hm Γ₁ Γ₂ hΓ hfree
      subst hΓ
      cases ht with
      | @app _ k A₁ _ _ _ hft hat =>
          have h1 := ihf hft (modeOK_headMode hft) Γ₁ Γ₂ rfl
            (fun l hl => by
              have := hfree l hl
              cases h2 : S₁.l l
              · rfl
              · rw [(own_ge ha).2 l h2] at this; exact this)
          have h2 := iha hat (modeOK_consume _) Γ₁ Γ₂ rfl hfree
          have h1' : Own (Γ₁ ++ Γ₂) (St.sub Γ₁.length v S) (subst Γ₁.length v f)
              (headMode (Γ₁ ++ Γ₂) (subst Γ₁.length v f)) (St.sub Γ₁.length v S₁) := by
            rcases headMode_subst hval hvt hft with he | ⟨k', A', b, he⟩
            · rw [he]; exact h1
            · rw [he] at h1 ⊢; exact own_lam_mode h1 _
          exact .app h1' h2
  | @letE Γ S S₁ S₂ A' w b m hw hb ihw ihb =>
      intro B ht hm Γ₁ Γ₂ hΓ hfree
      subst hΓ
      cases ht with
      | letE hwt hbt =>
          have h1 := ihw hwt (modeOK_consume _) Γ₁ Γ₂ rfl
            (fun l hl => by
              have := hfree l hl
              cases h2 : S₁.l l
              · rfl
              · rw [St.pop_l, (own_ge hb).2 l (by simpa using h2)] at this; exact this)
          have h2 := ihb hbt (modeOK_consume _) (A' :: Γ₁) Γ₂ rfl
            (fun l hl => by simpa using hfree l hl)
          simp only [List.length_cons, List.cons_append] at h2
          rw [St.sub_push] at h2
          exact (Own.letE h1 h2).cast (St.sub_pop _ _ _)
  | consume _ ih =>
      intro B ht hm Γ₁ Γ₂ hΓ hfree
      cases ht with
      | consume ht' => exact .consume (ih ht' trivial Γ₁ Γ₂ hΓ hfree)
  | read _ ih =>
      intro B ht hm Γ₁ Γ₂ hΓ hfree
      cases ht with
      | read ht' => exact .read (ih ht' trivial Γ₁ Γ₂ hΓ hfree)
  | @iter Γ S S₁ S₂ S₃ n z k C b m hn hz hs hd ihn ihz ihs =>
      intro B ht hm Γ₁ Γ₂ hΓ hfree
      cases ht with
      | iter hnt hzt hst =>
          have hge₂ := own_ge hs
          have hge₁ := St.le_trans (own_ge hz) hge₂
          have h1 := ihn hnt trivial Γ₁ Γ₂ hΓ (fun l hl => by
            have := hfree l hl
            cases h2 : S₁.l l
            · rfl
            · rw [hge₁.2 l h2] at this; exact this)
          have h2 := ihz hzt (modeOK_consume _) Γ₁ Γ₂ hΓ (fun l hl => by
            have := hfree l hl
            cases h3 : S₂.l l
            · rfl
            · rw [hge₂.2 l h3] at this; exact this)
          have h3 := ihs hst (modeOK_consume _) Γ₁ Γ₂ hΓ hfree
          simp only [subst] at h3 ⊢
          cases hst with
          | lam hbt =>
              subst hΓ
              have hd' := dem_subst_le hval hvt hside hbt .consume (modeOK_consume _) (C :: Γ₁) Γ₂ 1
                rfl (by simp)
              simp only [List.length_cons, List.cons_append] at hd'
              exact .iter h1 h2 h3 (Nat.le_trans hd' hd)

end LRL.Affine
