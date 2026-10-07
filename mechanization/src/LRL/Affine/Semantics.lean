import LRL.Affine.Syntax
import LRL.Affine.Typing
import LRL.Affine.Ownership
import LRL.Affine.Substitution

/-!
# Affine core with function kinds — semantics and affine safety (T4, T5)

A call-by-value, left-to-right small-step semantics over configurations
`(σ, t)`, where the resource store `σ : Nat → Bool` says which locations are
live.  A step is labelled with the location it consumes, if any.

* `consume (loc l)` steps only when `l` is live, and kills it.  Consuming a
  dead resource is **stuck** (`ConsumesDead`, `consumesDead_stuck`).
* `read (loc l)` observes a resource and does not check liveness (reads are
  not tracked by the kernel judgment; see `Affine/Ownership.lean`).
* `iter (lit (n+1)) z s ⟶ s (iter (lit n) z s)`: the step function `s` is
  duplicated, which is why the ownership rule for `iter` imposes the
  repetition barrier on it.
* `ghost t ⟶ unit` without evaluating `t` (erased position).

`Agree σ S` relates the store to a usage state: every dead location is
marked moved.  Preservation (`preservation`) keeps typing, the ownership
judgment (from the state updated by the step, with a smaller final state)
and `Agree`; progress (`progress`) says a well-typed, well-owned closed term
is a value or steps.  Affine safety (`no_double_consume`): along every
execution of such a program the consumed locations are pairwise distinct,
every reachable configuration is a value or steps, and none tries to consume
a dead resource.
-/

namespace LRL.Affine

/-! ### Stores and steps -/

/-- Resource store: `σ l = true` iff location `l` is live. -/
abbrev Store := Nat → Bool

/-- Kill location `l`. -/
def Store.kill (σ : Store) (l : Nat) : Store := fun i => if i = l then false else σ i

/-- The store after a step labelled `o`. -/
def Store.after (σ : Store) : Option Nat → Store
  | none => σ
  | some l => σ.kill l

/-- The usage state after a step labelled `o`. -/
def St.after (S : St) : Option Nat → St
  | none => S
  | some l => S.moveL l

/-- Small-step semantics `(σ, t) ⟶[o] (σ', t')`; `o = some l` when the step
    consumes location `l`. -/
inductive Step : Store → Term → Option Nat → Store → Term → Prop where
  | appL {σ σ' f f' a o} : Step σ f o σ' f' → Step σ (.app f a) o σ' (.app f' a)
  | appR {σ σ' f a a' o} : Value f → Step σ a o σ' a' → Step σ (.app f a) o σ' (.app f a')
  | beta {σ k A b v} : Value v → Step σ (.app (.lam k A b) v) none σ (subst 0 v b)
  | letV {σ σ' A v v' b o} : Step σ v o σ' v' → Step σ (.letE A v b) o σ' (.letE A v' b)
  | letB {σ A v b} : Value v → Step σ (.letE A v b) none σ (subst 0 v b)
  | consumeC {σ σ' t t' o} : Step σ t o σ' t' → Step σ (.consume t) o σ' (.consume t')
  | consumeL {σ l} : σ l = true → Step σ (.consume (.loc l)) (some l) (σ.kill l) .unit
  | readC {σ σ' t t' o} : Step σ t o σ' t' → Step σ (.read t) o σ' (.read t')
  | readL {σ l} : Step σ (.read (.loc l)) none σ (.lit 0)
  | iterN {σ σ' n n' z s o} : Step σ n o σ' n' → Step σ (.iter n z s) o σ' (.iter n' z s)
  | iterZ {σ σ' n z z' s o} :
      Value n → Step σ z o σ' z' → Step σ (.iter n z s) o σ' (.iter n z' s)
  | iterS {σ σ' n z s s' o} :
      Value n → Value z → Step σ s o σ' s' → Step σ (.iter n z s) o σ' (.iter n z s')
  | iter0 {σ z s} : Value z → Value s → Step σ (.iter (.lit 0) z s) none σ z
  | iterSucc {σ n z s} :
      Value z → Value s →
      Step σ (.iter (.lit (n + 1)) z s) none σ (.app s (.iter (.lit n) z s))
  | ghost {σ t} : Step σ (.ghost t) none σ .unit

/-- Multi-step execution; the list collects the consumed locations in order. -/
inductive Steps : Store → Term → List Nat → Store → Term → Prop where
  | refl {σ t} : Steps σ t [] σ t
  | step {σ t o σ₁ t₁ tr σ₂ t₂} :
      Step σ t o σ₁ t₁ → Steps σ₁ t₁ tr σ₂ t₂ → Steps σ t (o.toList ++ tr) σ₂ t₂

/-- The next redex consumes a dead resource (evaluation-context closure). -/
inductive ConsumesDead (σ : Store) : Term → Prop where
  | here {l} : σ l = false → ConsumesDead σ (.consume (.loc l))
  | appL {f a} : ConsumesDead σ f → ConsumesDead σ (.app f a)
  | appR {f a} : Value f → ConsumesDead σ a → ConsumesDead σ (.app f a)
  | letV {A v b} : ConsumesDead σ v → ConsumesDead σ (.letE A v b)
  | consume {t} : ConsumesDead σ t → ConsumesDead σ (.consume t)
  | read {t} : ConsumesDead σ t → ConsumesDead σ (.read t)
  | iterN {n z s} : ConsumesDead σ n → ConsumesDead σ (.iter n z s)
  | iterZ {n z s} : Value n → ConsumesDead σ z → ConsumesDead σ (.iter n z s)
  | iterS {n z s} : Value n → Value z → ConsumesDead σ s → ConsumesDead σ (.iter n z s)

/-- Every location the store marks dead is marked moved in the usage state. -/
def Agree (σ : Store) (S : St) : Prop := ∀ l, σ l = false → S.l l = true

/-! ### Basic facts -/

theorem value_no_step {σ t o σ' t'} (hv : Value t) : ¬ Step σ t o σ' t' := by
  intro h; cases hv <;> cases h

theorem step_store {σ t o σ' t'} (h : Step σ t o σ' t') : σ' = σ.after o := by
  induction h <;> first | rfl | assumption

theorem step_live {σ t o σ' t'} (h : Step σ t o σ' t') : ∀ l, o = some l → σ l = true := by
  induction h with
  | consumeL hl => intro l e; cases e; exact hl
  | appL _ ih | appR _ _ ih | letV _ ih | consumeC _ ih | readC _ ih | iterN _ ih
  | iterZ _ _ ih | iterS _ _ _ ih => exact ih
  | _ => intro l e; cases e

theorem agree_mono {σ S T} (h : Agree σ S) (hle : S ≤ T) : Agree σ T :=
  fun l hl => hle.2 l (h l hl)

theorem agree_after {σ S} (h : Agree σ S) (o : Option Nat) : Agree (σ.after o) (S.after o) := by
  cases o with
  | none => exact h
  | some l =>
      intro i hi
      simp only [Store.after, Store.kill, St.after, St.moveL_l] at hi ⊢
      split at hi
      · simp_all
      · simp [h i hi]

theorem consumesDead_not_value {σ t} (h : ConsumesDead σ t) : ¬ Value t := by
  intro hv; cases h <;> cases hv

/-- Consuming a dead resource is stuck. -/
theorem consumesDead_stuck {σ t} (h : ConsumesDead σ t) : ∀ o σ' t', ¬ Step σ t o σ' t' := by
  induction h with
  | here hl =>
      intro o σ' t' hs
      cases hs with
      | consumeC hs' => exact value_no_step (.loc _) hs'
      | consumeL hl' => simp_all
  | @appL f a hf ih =>
      intro o σ' t' hs
      cases hs with
      | appL hs' => exact ih _ _ _ hs'
      | appR hv _ => exact consumesDead_not_value hf hv
      | beta _ => exact consumesDead_not_value hf (.lam _ _ _)
  | @appR f a hfv ha ih =>
      intro o σ' t' hs
      cases hs with
      | appL hs' => exact value_no_step hfv hs'
      | appR _ hs' => exact ih _ _ _ hs'
      | beta hv => exact consumesDead_not_value ha hv
  | letV hv ih =>
      intro o σ' t' hs
      cases hs with
      | letV hs' => exact ih _ _ _ hs'
      | letB hv' => exact consumesDead_not_value hv hv'
  | consume ht ih =>
      intro o σ' t' hs
      cases hs with
      | consumeC hs' => exact ih _ _ _ hs'
      | consumeL _ => exact consumesDead_not_value ht (.loc _)
  | read ht ih =>
      intro o σ' t' hs
      cases hs with
      | readC hs' => exact ih _ _ _ hs'
      | readL => exact consumesDead_not_value ht (.loc _)
  | iterN hn ih =>
      intro o σ' t' hs
      cases hs with
      | iterN hs' => exact ih _ _ _ hs'
      | iterZ hv _ | iterS hv _ _ => exact consumesDead_not_value hn hv
      | iter0 _ _ | iterSucc _ _ => exact consumesDead_not_value hn (.lit _)
  | iterZ hnv hz ih =>
      intro o σ' t' hs
      cases hs with
      | iterN hs' => exact value_no_step hnv hs'
      | iterZ _ hs' => exact ih _ _ _ hs'
      | iterS _ hv _ | iter0 hv _ | iterSucc hv _ => exact consumesDead_not_value hz hv
  | iterS hnv hzv hs₀ ih =>
      intro o σ' t' hs
      cases hs with
      | iterN hs' => exact value_no_step hnv hs'
      | iterZ _ hs' => exact value_no_step hzv hs'
      | iterS _ _ hs' => exact ih _ _ _ hs'
      | iter0 _ hv | iterSucc _ hv => exact consumesDead_not_value hs₀ hv

/-! ### Typing is preserved -/

theorem typed_step {σ t o σ' t'} (h : Step σ t o σ' t') : ∀ {A}, Typed [] t A → Typed [] t' A := by
  induction h with
  | appL _ ih => intro A ht; cases ht with | app hf ha => exact .app (ih hf) ha
  | appR _ _ ih => intro A ht; cases ht with | app hf ha => exact .app hf (ih ha)
  | beta _ =>
      intro A ht
      cases ht with
      | app hf ha => cases hf with | lam hb => exact typed_subst0 ha hb
  | letV _ ih => intro A ht; cases ht with | letE hv hb => exact .letE (ih hv) hb
  | letB _ => intro A ht; cases ht with | letE hv hb => exact typed_subst0 hv hb
  | consumeC _ ih => intro A ht; cases ht with | consume h' => exact .consume (ih h')
  | consumeL _ => intro A ht; cases ht; exact .unit
  | readC _ ih => intro A ht; cases ht with | read h' => exact .read (ih h')
  | readL => intro A ht; cases ht; exact .lit
  | iterN _ ih => intro A ht; cases ht with | iter hn hz hs => exact .iter (ih hn) hz hs
  | iterZ _ _ ih => intro A ht; cases ht with | iter hn hz hs => exact .iter hn (ih hz) hs
  | iterS _ _ _ ih => intro A ht; cases ht with | iter hn hz hs => exact .iter hn hz (ih hs)
  | iter0 _ _ => intro A ht; cases ht with | iter _ hz _ => exact hz
  | iterSucc _ _ =>
      intro A ht
      cases ht with
      | iter _ hz hs => exact .app hs (.iter .lit hz hs)
  | ghost => intro A ht; cases ht; exact .unit

/-! ### T4: preservation of the ownership judgment -/

/-- **(T4a) Preservation (ownership).**  If a closed, well-typed term is
    well-owned from `S` to `S'` and takes a step labelled `o`, then the
    consumed location was not moved in `S`, and the result is well-owned from
    the updated state `S.after o` to a state below `S'`. -/
theorem own_step {σ t o σ' t'} (h : Step σ t o σ' t') :
    ∀ {A S m S'}, Typed [] t A → Own [] S t m S' →
      (∀ l, o = some l → S.l l = false) ∧ ∃ T', Own [] (S.after o) t' m T' ∧ T' ≤ S' := by
  induction h with
  | appL _ ih =>
      intro A S m S' ht ho
      cases ht with
      | app hft _ =>
          cases ho with
          | app hof hoa =>
              rw [headMode_nil] at hof
              obtain ⟨hl, T₁, hT₁, hle₁⟩ := ih hft hof
              obtain ⟨T₂, hT₂, hle₂⟩ := own_mono hoa T₁ hle₁
              exact ⟨hl, T₂, .app (by rw [headMode_nil]; exact hT₁) hT₂, hle₂⟩
  | @appR σ' f a a' o hfv _ ih =>
      intro A S m S' ht ho
      cases ht with
      | app _ hat =>
          cases ho with
          | @app _ _ S₁ S₂ _ _ _ hof hoa =>
              rw [headMode_nil] at hof
              obtain ⟨hl, T₂, hT₂, hle₂⟩ := ih hat hoa
              cases o with
              | none =>
                  exact ⟨(fun _ e => nomatch e), T₂, .app (by rw [headMode_nil]; exact hof) hT₂, hle₂⟩
              | some l =>
                  have hS₁ : S₁.l l = false := hl l rfl
                  have hS : S.l l = false := by
                    cases hs : S.l l
                    · rfl
                    · rw [(own_ge hof).2 l hs] at hS₁; exact hS₁
                  have hF := own_frame hof [] (S.moveL l) (fun i hi => absurd hi (by simp))
                    (fun l' hl' => by
                      simp only [St.moveL_l]
                      by_cases he : l' = l
                      · subst he
                        have := own_l hof l'
                        rw [hS₁] at this
                        simp at this; omega
                      · simp [he, own_cl_req hof l' hl'])
                  have hFle : St.frame 0 S₁ (S.moveL l) f .consume ≤ S₁.moveL l := by
                    refine ⟨fun i hi => ?_, fun l' hl' => ?_⟩
                    · simp only [St.frame, Nat.not_lt_zero, ite_false, St.moveL_v] at hi ⊢
                      exact (own_ge hof).1 i hi
                    · simp only [St.frame, St.moveL_l, Bool.or_eq_true] at hl' ⊢
                      by_cases he : l' = l
                      · simp [he]
                      · simp only [he, ite_false] at hl' ⊢
                        rcases hl' with h1 | h1
                        · exact (own_ge hof).2 l' h1
                        · rw [own_l hof l']; simp [h1]
                  obtain ⟨T₂', hT₂', hle'⟩ := own_mono hT₂ _ hFle
                  exact ⟨(fun l' e => by cases e; exact hS), T₂',
                    .app (by rw [headMode_nil]; exact hF) hT₂', St.le_trans hle' hle₂⟩
  | @beta k A' b v hv =>
      intro A S m S' ht ho
      cases ht with
      | app hft hat =>
          cases hft with
          | lam hbt =>
              cases ho with
              | @app _ _ S₁ S₂ _ _ _ hof hoa =>
                  cases hof with
                  | @lam _ _ B' _ _ _ _ hob _ =>
                      have hsub := own_subst hv hat hoa hob hbt (modeOK_consume _) [] [] rfl
                        (fun l hl => by simpa using own_cl_req hoa l hl)
                      simp only [List.length_nil, List.nil_append] at hsub
                      rw [St.sub_zero_push] at hsub
                      obtain ⟨X, hX, hle⟩ := own_mode hsub m
                      refine ⟨(fun _ e => nomatch e), X, hX, St.le_trans hle ?_⟩
                      refine ⟨fun i hi => ?_, fun l hl => ?_⟩
                      · simp only [St.sub, Nat.not_lt_zero, ite_false] at hi
                        rw [own_v_out hoa i (Nat.zero_le _)]
                        simpa using hi
                      · simp only [St.sub, Bool.or_eq_true, Bool.and_eq_true] at hl
                        rcases hl with h1 | ⟨_, h1⟩
                        · exact (own_ge hoa).2 l (by simpa using h1)
                        · rw [own_l hoa l]; simp [h1]
  | letV _ ih =>
      intro A S m S' ht ho
      cases ht with
      | letE hvt _ =>
          cases ho with
          | letE hov hob =>
              obtain ⟨hl, T₁, hT₁, hle₁⟩ := ih hvt hov
              obtain ⟨T₂, hT₂, hle₂⟩ := own_mono hob T₁.push (St.push_le hle₁)
              exact ⟨hl, T₂.pop, .letE hT₁ hT₂, St.pop_le hle₂⟩
  | @letB A' v b hv =>
      intro A S m S' ht ho
      cases ht with
      | letE hvt hbt =>
          cases ho with
          | @letE _ _ S₁ S₂ _ _ _ _ hov hob =>
              obtain ⟨B'', hob', hle⟩ := own_mono hob S.push (St.push_le (own_ge hov))
              have hfree : ∀ l, 0 < cl l v .consume → B''.l l = false := by
                intro l hl
                have h1 := own_cl_req hov l hl
                rw [own_l hob' l]
                simp only [St.push_l, h1, Bool.false_or, pos_eq_false]
                by_cases hb : 0 < cl l b .consume
                · have h2 := own_cl_req hob l hb
                  simp only [St.push_l] at h2
                  rw [own_l hov l] at h2
                  simp at h2; omega
                · omega
              have hsub := own_subst hv hvt hov hob' hbt (modeOK_consume _) [] [] rfl hfree
              simp only [List.length_nil, List.nil_append] at hsub
              rw [St.sub_zero_push] at hsub
              obtain ⟨X, hX, hle'⟩ := own_mode hsub m
              refine ⟨(fun _ e => nomatch e), X, hX, St.le_trans hle' ?_⟩
              refine ⟨fun i hi => ?_, fun l hl => ?_⟩
              · simp only [St.sub, Nat.not_lt_zero, ite_false] at hi
                exact hle.1 (i + 1) hi
              · simp only [St.sub, Bool.or_eq_true, Bool.and_eq_true] at hl
                simp only [St.pop_l]
                rcases hl with h1 | ⟨_, h1⟩
                · exact hle.2 l h1
                · have h2 : S₁.l l = true := by rw [own_l hov l]; simp [h1]
                  exact (own_ge hob).2 l (by simpa using h2)
  | consumeC _ ih =>
      intro A S m S' ht ho
      cases ht with
      | consume ht' =>
          cases ho with
          | consume ho' =>
              obtain ⟨hl, T', hT', hle⟩ := ih ht' ho'
              exact ⟨hl, T', .consume hT', hle⟩
  | consumeL _ =>
      intro A S m S' ht ho
      cases ho with
      | consume ho' =>
          cases ho' with
          | loc hreq =>
              refine ⟨(fun l' e => by cases e; exact hreq rfl), _, .unit, ?_⟩
              simp only [ite_true, St.after]
              exact St.le_refl _
  | readC _ ih =>
      intro A S m S' ht ho
      cases ht with
      | read ht' =>
          cases ho with
          | read ho' =>
              obtain ⟨hl, T', hT', hle⟩ := ih ht' ho'
              exact ⟨hl, T', .read hT', hle⟩
  | readL =>
      intro A S m S' ht ho
      cases ho with
      | read ho' =>
          cases ho' with
          | loc _ =>
              refine ⟨(fun _ e => nomatch e), _, .lit, ?_⟩
              simp only [St.after]
              exact St.le_refl _
  | iterN _ ih =>
      intro A S m S' ht ho
      cases ht with
      | iter hnt _ _ =>
          cases ho with
          | iter hon hoz hos hd =>
              obtain ⟨hl, T₁, hT₁, hle₁⟩ := ih hnt hon
              obtain ⟨T₂, hT₂, hle₂⟩ := own_mono hoz T₁ hle₁
              obtain ⟨T₃, hT₃, hle₃⟩ := own_mono hos T₂ hle₂
              exact ⟨hl, T₃, .iter hT₁ hT₂ hT₃ hd, hle₃⟩
  | iterZ hnv _ ih =>
      intro A S m S' ht ho
      cases ht with
      | iter hnt hzt _ =>
          obtain ⟨k, rfl⟩ := canonical_nat hnv hnt
          cases ho with
          | iter hon hoz hos hd =>
              cases hon
              obtain ⟨hl, T₂, hT₂, hle₂⟩ := ih hzt hoz
              obtain ⟨T₃, hT₃, hle₃⟩ := own_mono hos T₂ hle₂
              exact ⟨hl, T₃, .iter .lit hT₂ hT₃ hd, hle₃⟩
  | iterS _ _ hs _ =>
      intro A S m S' ht ho
      cases ho with
      | iter _ _ _ _ => exact absurd hs (value_no_step (.lam _ _ _))
  | iter0 _ _ =>
      intro A S m S' ht ho
      cases ho with
      | iter hon hoz hos _ =>
          cases hon
          obtain ⟨X, hX, hle⟩ := own_mode hoz m
          exact ⟨(fun _ e => nomatch e), X, hX, St.le_trans hle (own_ge hos)⟩
  | iterSucc _ _ =>
      intro A S m S' ht ho
      cases ho with
      | @iter _ _ _ S₂ _ _ _ k C b _ hon hoz hos hd =>
          cases hon
          have hd2 : dem (C :: []) 1 b .consume ≤ 2 := hd
          have hF := own_frame hos [] S (fun i hi => absurd hi (by simp))
            (fun l hl => by rw [cl_lam_of_dem hd2 l .consume] at hl; omega)
          have hhead : Own [] S (.lam k C b) .consume S :=
            hF.cast (own_lam_noeff hF hd2)
          exact ⟨(fun _ e => nomatch e), S',
            .app (by rw [headMode_nil]; exact hhead) (.iter .lit hoz hos hd), St.le_refl _⟩
  | ghost =>
      intro A S m S' ht ho
      cases ho
      exact ⟨(fun _ e => nomatch e), _, .unit, St.le_refl _⟩

/-- **(T4a) Preservation.**  Typing, well-ownedness (from the updated state,
    with a final state below the original one) and the store/state agreement
    are preserved by a step. -/
theorem preservation {σ t o σ' t' A S m S'} (h : Step σ t o σ' t')
    (ht : Typed [] t A) (ho : Own [] S t m S') (hag : Agree σ S) :
    Typed [] t' A ∧ Agree σ' (S.after o) ∧ ∃ T', Own [] (S.after o) t' m T' ∧ T' ≤ S' := by
  obtain ⟨_, T', hT', hle⟩ := own_step h ht ho
  refine ⟨typed_step h ht, ?_, T', hT', hle⟩
  rw [step_store h]
  exact agree_after hag o

/-! ### T4: progress -/

/-- **(T4b) Progress.**  A closed, well-typed, well-owned term whose state
    agrees with the store is a value or takes a step; in particular it never
    attempts to consume a dead resource. -/
theorem progress {t A} (ht : Typed [] t A) :
    ∀ {S m S' σ}, Own [] S t m S' → Agree σ S → Value t ∨ ∃ o σ' t', Step σ t o σ' t' := by
  generalize hΓ : ([] : Ctx) = Γ at ht
  induction ht with
  | var hl => subst hΓ; simp [lookup] at hl
  | unit => intros; exact .inl .unit
  | lit => intros; exact .inl (.lit _)
  | loc => intros; exact .inl (.loc _)
  | lam _ => intros; exact .inl (.lam _ _ _)
  | app hf ha ihf iha =>
      subst hΓ
      intro S m S' σ ho hag
      cases ho with
      | app hof hoa =>
          rcases ihf rfl hof hag with hfv | ⟨o, σ', f', hs⟩
          · rcases iha rfl hoa (agree_mono hag (own_ge hof)) with hav | ⟨o, σ', a', hs⟩
            · obtain ⟨b, rfl, _⟩ := canonical_arr hfv hf
              exact .inr ⟨_, _, _, .beta hav⟩
            · exact .inr ⟨_, _, _, .appR hfv hs⟩
          · exact .inr ⟨_, _, _, .appL hs⟩
  | letE hv _ ihv _ =>
      subst hΓ
      intro S m S' σ ho hag
      cases ho with
      | letE hov _ =>
          rcases ihv rfl hov hag with hvv | ⟨o, σ', v', hs⟩
          · exact .inr ⟨_, _, _, .letB hvv⟩
          · exact .inr ⟨_, _, _, .letV hs⟩
  | consume ht' ih =>
      subst hΓ
      intro S m S' σ ho hag
      cases ho with
      | consume ho' =>
          rcases ih rfl ho' hag with htv | ⟨o, σ', t', hs⟩
          · obtain ⟨l, rfl⟩ := canonical_res htv ht'
            cases ho' with
            | loc hreq =>
                have h1 := hreq rfl
                cases hσ : σ l
                · have := hag l hσ; simp_all
                · exact .inr ⟨_, _, _, .consumeL hσ⟩
          · exact .inr ⟨_, _, _, .consumeC hs⟩
  | read ht' ih =>
      subst hΓ
      intro S m S' σ ho hag
      cases ho with
      | read ho' =>
          rcases ih rfl ho' hag with htv | ⟨o, σ', t', hs⟩
          · obtain ⟨l, rfl⟩ := canonical_res htv ht'
            exact .inr ⟨_, _, _, .readL⟩
          · exact .inr ⟨_, _, _, .readC hs⟩
  | iter hn hz _ ihn ihz _ =>
      subst hΓ
      intro S m S' σ ho hag
      cases ho with
      | iter hon hoz _ _ =>
          rcases ihn rfl hon hag with hnv | ⟨o, σ', n', hs⟩
          · rcases ihz rfl hoz (agree_mono hag (own_ge hon)) with hzv | ⟨o, σ', z', hs⟩
            · obtain ⟨k, rfl⟩ := canonical_nat hnv hn
              cases k with
              | zero => exact .inr ⟨_, _, _, .iter0 hzv (.lam _ _ _)⟩
              | succ k => exact .inr ⟨_, _, _, .iterSucc hzv (.lam _ _ _)⟩
            · exact .inr ⟨_, _, _, .iterZ hnv hs⟩
          · exact .inr ⟨_, _, _, .iterN hs⟩
  | ghost _ _ => intros; exact .inr ⟨_, _, _, .ghost⟩

/-- A well-owned term whose state agrees with the store never has a
    consumption of a dead resource as its next redex. -/
theorem own_not_consumesDead {σ t} (h : ConsumesDead σ t) :
    ∀ {S m S'}, Own [] S t m S' → Agree σ S → False := by
  induction h with
  | @here l hl =>
      intro S m S' ho hag
      cases ho with
      | consume ho' =>
          cases ho' with
          | loc hreq => have := hag l hl; simp_all
  | appL _ ih => intro S m S' ho hag; cases ho with | app hof _ => exact ih hof hag
  | appR _ _ ih =>
      intro S m S' ho hag
      cases ho with | app hof hoa => exact ih hoa (agree_mono hag (own_ge hof))
  | letV _ ih => intro S m S' ho hag; cases ho with | letE hov _ => exact ih hov hag
  | consume _ ih => intro S m S' ho hag; cases ho with | consume ho' => exact ih ho' hag
  | read _ ih => intro S m S' ho hag; cases ho with | read ho' => exact ih ho' hag
  | iterN _ ih => intro S m S' ho hag; cases ho with | iter hon _ _ _ => exact ih hon hag
  | iterZ _ _ ih =>
      intro S m S' ho hag
      cases ho with | iter hon hoz _ _ => exact ih hoz (agree_mono hag (own_ge hon))
  | iterS _ _ hs _ =>
      intro S m S' ho hag
      cases ho with | iter _ _ _ _ => cases hs

/-! ### T5: affine safety -/

/-- Dead locations stay dead. -/
theorem steps_dead {σ t tr σ' t'} (h : Steps σ t tr σ' t') : ∀ l, σ l = false → σ' l = false := by
  induction h with
  | refl => intro l hl; exact hl
  | step hs _ ih =>
      intro l hl
      apply ih
      rw [step_store hs]
      cases ‹Option Nat› with
      | none => exact hl
      | some l' => simp only [Store.after, Store.kill]; split <;> simp_all

/-- The trace of an execution: each location is consumed at most once, and
    only while it is live. -/
theorem steps_trace {σ t tr σ' t'} (h : Steps σ t tr σ' t') :
    tr.Nodup ∧ ∀ l ∈ tr, σ l = true ∧ σ' l = false := by
  induction h with
  | refl => exact ⟨List.nodup_nil, fun _ h => by cases h⟩
  | @step σ t o σ₁ t₁ tr σ₂ t₂ hs hss ih =>
      obtain ⟨hnd, hin⟩ := ih
      have hσ₁ := step_store hs
      cases o with
      | none =>
          simp only [Option.toList, List.nil_append, Store.after] at hσ₁ ⊢
          subst hσ₁
          exact ⟨hnd, hin⟩
      | some l =>
          have hl := step_live hs l rfl
          simp only [Store.after] at hσ₁
          subst hσ₁
          simp only [Option.toList, List.singleton_append]
          refine ⟨List.nodup_cons.2 ⟨fun hmem => ?_, hnd⟩, fun l' hmem => ?_⟩
          · have := (hin l hmem).1
            simp [Store.kill] at this
          · rcases List.mem_cons.1 hmem with rfl | hmem'
            · exact ⟨hl, steps_dead hss l' (by simp [Store.kill])⟩
            · obtain ⟨h1, h2⟩ := hin l' hmem'
              refine ⟨?_, h2⟩
              simp only [Store.kill] at h1
              split at h1
              · simp at h1
              · exact h1

/-- The invariant along an execution: typing, well-ownedness and agreement. -/
theorem steps_invariant {σ t tr σ' t'} (h : Steps σ t tr σ' t') :
    ∀ {A S m S'}, Typed [] t A → Own [] S t m S' → Agree σ S →
      Typed [] t' A ∧ ∃ T T', Own [] T t' m T' ∧ Agree σ' T := by
  induction h with
  | refl => intro A S m S' ht ho hag; exact ⟨ht, S, S', ho, hag⟩
  | step hs _ ih =>
      intro A S m S' ht ho hag
      obtain ⟨ht', hag', T', hT', _⟩ := preservation hs ht ho hag
      exact ih ht' hT' hag'

/-- **(T5) A well-typed, well-owned closed program never consumes a resource
    twice.**  Along every execution from a store that agrees with the initial
    usage state, the consumed locations are pairwise distinct and were live
    when consumed, and every reachable configuration is a value or steps and
    does not try to consume a dead resource. -/
theorem no_double_consume {t A S m S' σ} (ht : Typed [] t A) (ho : Own [] S t m S')
    (hag : Agree σ S) {tr σ' t'} (hs : Steps σ t tr σ' t') :
    tr.Nodup ∧ (∀ l ∈ tr, σ l = true ∧ σ' l = false) ∧ ¬ ConsumesDead σ' t' ∧
      (Value t' ∨ ∃ o σ'' t'', Step σ' t' o σ'' t'') := by
  obtain ⟨hnd, hin⟩ := steps_trace hs
  obtain ⟨ht', T, T', hT', hag'⟩ := steps_invariant hs ht ho hag
  exact ⟨hnd, hin, fun hd => own_not_consumesDead hd hT' hag', progress ht' hT' hag'⟩

/-- **(T5) Affine safety for closed programs.**  Started with every resource
    live and nothing moved. -/
theorem affine_safety {t A S'} (ht : Typed [] t A) (ho : Own [] St.empty t .consume S')
    {tr σ' t'} (hs : Steps (fun _ => true) t tr σ' t') :
    tr.Nodup ∧ ¬ ConsumesDead σ' t' ∧ (Value t' ∨ ∃ o σ'' t'', Step σ' t' o σ'' t'') := by
  obtain ⟨h1, _, h3, h4⟩ := no_double_consume ht ho (fun l hl => by simp at hl) hs
  exact ⟨h1, h3, h4⟩

end LRL.Affine
