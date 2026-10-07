import LRL.Affine.Syntax
import LRL.Affine.Typing
import LRL.Affine.Ownership
import LRL.Affine.Substitution

/-!
# Affine core with function kinds — the elaborator's coercion in general

The elaborator coerces a function of kind `k` to an expected kind `k' ⊒ k`
in two ways (`coerce_fn_to_kind` in `frontend/src/elaborator.rs`): a λ
literal is re-annotated (kind widening, `kind_widening`), and any other term
`t` is wrapped as `λ^{k'} x:A. (↑t) x`, where `↑t` lifts the free variables
of `t` over the new binder.  `eta k' A t` is that wrapper.

`eta_coercion_general`: the wrapper is well-typed at `A →[k'] B`, its
required kind is the one demanded by *evaluating* `t` as a function head,
and it is well-owned (leaving the state that evaluating `t` leaves) whenever
that required kind is `⊑ k'`.  For a variable the required kind is exactly
`k` (`eta_coercion`, `eta_var_reqKind`); for a closed λ value it is `⊑ k`
(`eta_value_reqKind_le`); for a compound term it can exceed `k`
(`eta_compound_needs_fnOnce`): wrapping `g y` with `y : res` needs
`fnOnce`, since every call of the wrapper re-evaluates `g y` and consumes `y`.
-/

namespace LRL.Affine

/-! ### Lifting over a new binder -/

/-- `lift c t`: add one to every free variable of `t` with index `≥ c`. -/
def lift (c : Nat) : Term → Term
  | .var i => if i < c then .var i else .var (i + 1)
  | .unit => .unit
  | .lit n => .lit n
  | .loc l => .loc l
  | .lam k A b => .lam k A (lift (c + 1) b)
  | .app f a => .app (lift c f) (lift c a)
  | .letE A v b => .letE A (lift c v) (lift (c + 1) b)
  | .consume t => .consume (lift c t)
  | .read t => .read (lift c t)
  | .iter n z s => .iter (lift c n) (lift c z) (lift c s)
  | .ghost t => .ghost (lift c t)

/-- The index of variable `i` after inserting a binder at position `c`. -/
def liftIdx (c i : Nat) : Nat := if i < c then i else i + 1

theorem lift_var (c i : Nat) : lift c (.var i) = .var (liftIdx c i) := by
  simp only [lift, liftIdx]; split <;> rfl

theorem lookup_liftIdx (Γ₁ Γ₂ : Ctx) (A : Ty) (i : Nat) :
    lookup (Γ₁ ++ A :: Γ₂) (liftIdx Γ₁.length i) = lookup (Γ₁ ++ Γ₂) i := by
  simp only [liftIdx]
  split
  · exact lookup_mid_lt _ _ _ ‹_›
  · rw [lookup_mid_gt _ _ _ (by omega)]; rfl

theorem lift_nonvar {c : Nat} {t : Term} (h : ∀ i, t ≠ .var i) : ∀ i, lift c t ≠ .var i := by
  cases t <;> simp_all [lift]

theorem headMode_lift (Γ₁ Γ₂ : Ctx) (A : Ty) (f : Term) :
    headMode (Γ₁ ++ A :: Γ₂) (lift Γ₁.length f) = headMode (Γ₁ ++ Γ₂) f := by
  cases f with
  | var i => rw [lift_var]; simp only [headMode, lookup_liftIdx]
  | _ => rw [headMode_nonvar (lift_nonvar (by simp)), headMode_nonvar (by simp)]

theorem typed_lift {Γ t B} (h : Typed Γ t B) :
    ∀ Γ₁ Γ₂ A, Γ = Γ₁ ++ Γ₂ → Typed (Γ₁ ++ A :: Γ₂) (lift Γ₁.length t) B := by
  induction h with
  | var hl =>
      intro Γ₁ Γ₂ A hΓ; subst hΓ
      rw [lift_var]; exact .var (by rw [lookup_liftIdx]; exact hl)
  | unit => intros; exact .unit
  | lit => intros; exact .lit
  | loc => intros; exact .loc
  | @lam Γ k A' B' b _ ih =>
      intro Γ₁ Γ₂ A hΓ; subst hΓ
      exact .lam (ih (A' :: Γ₁) Γ₂ A rfl)
  | app _ _ ihf iha => intro Γ₁ Γ₂ A hΓ; exact .app (ihf Γ₁ Γ₂ A hΓ) (iha Γ₁ Γ₂ A hΓ)
  | @letE Γ A' B' v b _ _ ihv ihb =>
      intro Γ₁ Γ₂ A hΓ; subst hΓ
      exact .letE (ihv Γ₁ Γ₂ A rfl) (ihb (A' :: Γ₁) Γ₂ A rfl)
  | consume _ ih => intro Γ₁ Γ₂ A hΓ; exact .consume (ih Γ₁ Γ₂ A hΓ)
  | read _ ih => intro Γ₁ Γ₂ A hΓ; exact .read (ih Γ₁ Γ₂ A hΓ)
  | iter _ _ _ ihn ihz ihs =>
      intro Γ₁ Γ₂ A hΓ; exact .iter (ihn Γ₁ Γ₂ A hΓ) (ihz Γ₁ Γ₂ A hΓ) (ihs Γ₁ Γ₂ A hΓ)
  | ghost _ ih => intro Γ₁ Γ₂ A hΓ; exact .ghost (ih Γ₁ Γ₂ A hΓ)

/-- Lifting does not change the demand, with the threshold moved past the
    inserted binder when it lies at or above it. -/
theorem dem_lift (A : Ty) :
    ∀ (t : Term) (Γ₁ Γ₂ : Ctx) (d d' : Nat) (m : Mode),
      (d ≤ Γ₁.length ∧ d' = d) ∨ (Γ₁.length ≤ d ∧ d' = d + 1) →
      dem (Γ₁ ++ A :: Γ₂) d' (lift Γ₁.length t) m = dem (Γ₁ ++ Γ₂) d t m := by
  intro t
  induction t with
  | var i =>
      intro Γ₁ Γ₂ d d' m hd
      rw [lift_var]
      simp only [dem]
      rw [lookup_liftIdx]
      have hiff : liftIdx Γ₁.length i < d' ↔ i < d := by
        simp only [liftIdx]; split <;> omega
      by_cases hi : i < d
      · rw [ite_eq_left hi, ite_eq_left (hiff.2 hi)]
      · rw [ite_eq_right hi, ite_eq_right (fun h => hi (hiff.1 h))]
  | unit | lit | loc | ghost => intros; simp [lift, dem]
  | lam k B b ih =>
      intro Γ₁ Γ₂ d d' m hd
      simp only [lift, dem]
      exact ih (B :: Γ₁) Γ₂ (d + 1) (d' + 1) .consume (by simp; omega)
  | app f a ihf iha =>
      intro Γ₁ Γ₂ d d' m hd
      simp only [lift, dem]
      rw [headMode_lift, ihf Γ₁ Γ₂ d d' _ hd, iha Γ₁ Γ₂ d d' _ hd]
  | letE B v b ihv ihb =>
      intro Γ₁ Γ₂ d d' m hd
      simp only [lift, dem]
      rw [ihv Γ₁ Γ₂ d d' _ hd]
      exact congrArg _ (ihb (B :: Γ₁) Γ₂ (d + 1) (d' + 1) .consume (by simp; omega))
  | consume t ih => intro Γ₁ Γ₂ d d' m hd; simp only [lift, dem]; exact ih Γ₁ Γ₂ d d' _ hd
  | read t ih => intro Γ₁ Γ₂ d d' m hd; simp only [lift, dem]; exact ih Γ₁ Γ₂ d d' _ hd
  | iter n z s ihn ihz ihs =>
      intro Γ₁ Γ₂ d d' m hd
      simp only [lift, dem]
      rw [ihn Γ₁ Γ₂ d d' _ hd, ihz Γ₁ Γ₂ d d' _ hd, ihs Γ₁ Γ₂ d d' _ hd]

theorem cl_lift (l c : Nat) : ∀ (t : Term) (m : Mode), cl l (lift c t) m = cl l t m := by
  intro t
  induction t generalizing c with
  | var i => intro m; rw [lift_var]; simp [cl]
  | unit | lit | loc | ghost => intro m; simp [lift, cl]
  | lam k B b ih => intro m; simp only [lift, cl]; exact ih _ _
  | app f a ihf iha => intro m; simp only [lift, cl]; rw [ihf, iha]
  | letE B v b ihv ihb => intro m; simp only [lift, cl]; rw [ihv, ihb]
  | consume t ih => intro m; simp only [lift, cl]; exact ih _ _
  | read t ih => intro m; simp only [lift, cl]; exact ih _ _
  | iter n z s ihn ihz ihs => intro m; simp only [lift, cl]; rw [ihn, ihz, ihs]

/-! ### Ownership of lifted terms -/

/-- Insert a fresh (unmoved) variable at position `c` of a state. -/
def St.ins (c : Nat) (S : St) : St :=
  ⟨fun i => if i < c then S.v i else if i = c then false else S.v (i - 1), S.l⟩

theorem St.ins_zero (S : St) : St.ins 0 S = S.push := by
  apply St.ext
  · funext i; cases i <;> simp [St.ins]
  · rfl

theorem St.ins_push (c : Nat) (S : St) : St.ins (c + 1) S.push = (St.ins c S).push := by
  apply St.ext
  · funext i
    cases i with
    | zero => simp [St.ins]
    | succ i =>
        simp only [St.ins, St.push_v_succ]
        by_cases h1 : i < c
        · simp [h1]
        · by_cases h2 : i = c
          · simp [h2]
          · simp only [show ¬ (i + 1 < c + 1) by omega, show ¬ (i < c) by omega, h2,
              show ¬ (i + 1 = c + 1) by omega, ite_false]
            cases i with
            | zero => omega
            | succ i => simp
  · rfl

theorem St.ins_pop (c : Nat) (S : St) : (St.ins (c + 1) S).pop = St.ins c S.pop := by
  apply St.ext
  · funext i
    simp only [St.ins, St.pop_v]
    by_cases h1 : i < c
    · simp [h1]
    · by_cases h2 : i = c
      · simp [h2]
      · simp only [show ¬ (i + 1 < c + 1) by omega, show ¬ (i < c) by omega, h2,
          show ¬ (i + 1 = c + 1) by omega, ite_false]
        cases i with
        | zero => omega
        | succ i => simp
  · rfl

theorem St.ins_v_liftIdx (c : Nat) (S : St) (i : Nat) : (St.ins c S).v (liftIdx c i) = S.v i := by
  simp only [St.ins, liftIdx]
  by_cases h : i < c
  · simp [h]
  · simp [h, show ¬ (i + 1 < c) by omega, show i + 1 ≠ c by omega]

theorem St.ins_moveV (c : Nat) (S : St) (i : Nat) :
    St.ins c (S.moveV i) = (St.ins c S).moveV (liftIdx c i) := by
  apply St.ext
  · funext x
    simp only [St.ins, St.moveV_v, liftIdx]
    by_cases hx : x < c
    · by_cases hi : i < c
      · simp [hx, hi]
      · simp [hx, hi, show x ≠ i + 1 by omega, show x ≠ i by omega]
    · by_cases hxc : x = c
      · subst hxc
        by_cases hi : i < x
        · simp [hi, show x ≠ i by omega]
        · simp [hi, show x ≠ i + 1 by omega]
      · simp only [hx, hxc, ite_false]
        by_cases hi : i < c
        · simp [hi, show x - 1 ≠ i by omega, show x ≠ i by omega]
        · by_cases hxi : x = i + 1
          · simp [hi, hxi]
          · simp [hi, hxi, show x - 1 ≠ i by omega]
  · rfl

theorem St.ins_moveL (c : Nat) (S : St) (r : Nat) :
    St.ins c (S.moveL r) = (St.ins c S).moveL r := by
  apply St.ext <;> rfl

/-- Lifting preserves the ownership judgment (with a fresh variable inserted
    into the state). -/
theorem own_lift {Γ S t m S'} (h : Own Γ S t m S') :
    ∀ Γ₁ Γ₂ A, Γ = Γ₁ ++ Γ₂ →
      Own (Γ₁ ++ A :: Γ₂) (St.ins Γ₁.length S) (lift Γ₁.length t) m (St.ins Γ₁.length S') := by
  induction h with
  | @var Γ S i A₀ m hl hreq =>
      intro Γ₁ Γ₂ A hΓ; subst hΓ
      rw [lift_var]
      refine (Own.var (by rw [lookup_liftIdx]; exact hl)
        (fun hm => by rw [St.ins_v_liftIdx]; exact hreq hm)).cast ?_
      split
      · exact (St.ins_moveV _ _ _).symm
      · rfl
  | @loc Γ S r m hreq =>
      intro Γ₁ Γ₂ A hΓ
      refine (Own.loc (S := St.ins Γ₁.length S) (fun hm => hreq hm)).cast ?_
      split
      · exact (St.ins_moveL _ _ _).symm
      · rfl
  | unit => intros; exact .unit
  | lit => intros; exact .lit
  | ghost => intros; exact .ghost
  | @lam Γ S S'' k A' b m hb hd ih =>
      intro Γ₁ Γ₂ A hΓ; subst hΓ
      have ih' := ih (A' :: Γ₁) Γ₂ A rfl
      simp only [List.length_cons, List.cons_append] at ih'
      rw [St.ins_push] at ih'
      have hd' : dem (A' :: (Γ₁ ++ A :: Γ₂)) 1 (lift (Γ₁.length + 1) b) .consume ≤ (capmode k).rank := by
        have := dem_lift A b (A' :: Γ₁) Γ₂ 1 1 .consume (.inl ⟨by simp, rfl⟩)
        simp only [List.length_cons, List.cons_append] at this
        rw [this]; exact hd
      exact (Own.lam ih' hd').cast (St.ins_pop _ _)
  | @app Γ S S₁ S₂ f a m hf ha ihf iha =>
      intro Γ₁ Γ₂ A hΓ; subst hΓ
      have h1 := ihf Γ₁ Γ₂ A rfl
      rw [← headMode_lift Γ₁ Γ₂ A f] at h1
      exact .app h1 (iha Γ₁ Γ₂ A rfl)
  | @letE Γ S S₁ S₂ A' v b m hv hb ihv ihb =>
      intro Γ₁ Γ₂ A hΓ; subst hΓ
      have h2 := ihb (A' :: Γ₁) Γ₂ A rfl
      simp only [List.length_cons, List.cons_append] at h2
      rw [St.ins_push] at h2
      exact (Own.letE (ihv Γ₁ Γ₂ A rfl) h2).cast (St.ins_pop _ _)
  | consume _ ih => intro Γ₁ Γ₂ A hΓ; exact .consume (ih Γ₁ Γ₂ A hΓ)
  | read _ ih => intro Γ₁ Γ₂ A hΓ; exact .read (ih Γ₁ Γ₂ A hΓ)
  | @iter Γ S S₁ S₂ S₃ n z k C b m hn hz hs hd ihn ihz ihs =>
      intro Γ₁ Γ₂ A hΓ; subst hΓ
      have h3 := ihs Γ₁ Γ₂ A rfl
      simp only [lift] at h3 ⊢
      have hd' : dem (C :: (Γ₁ ++ A :: Γ₂)) 1 (lift (Γ₁.length + 1) b) .consume ≤ Mode.mutate.rank := by
        have := dem_lift A b (C :: Γ₁) Γ₂ 1 1 .consume (.inl ⟨by simp, rfl⟩)
        simp only [List.length_cons, List.cons_append] at this
        rw [this]; exact hd
      exact .iter (ihn Γ₁ Γ₂ A rfl) (ihz Γ₁ Γ₂ A rfl) h3 hd'

/-! ### T2 in general -/

/-- The wrapper `λ^{k'} x:A. (↑t) x` the elaborator builds around a non-λ
    term `t`. -/
def eta (k' : Kind) (A : Ty) (t : Term) : Term := .lam k' A (.app (lift 0 t) (.var 0))

theorem eta_var (k' : Kind) (A : Ty) (i : Nat) : eta k' A (.var i) = etaVar k' A i := by
  simp [eta, etaVar, lift]

/-- The required kind of the wrapper is the kind demanded by evaluating `t`
    as a function head. -/
theorem eta_reqKind (Γ : Ctx) (k' : Kind) (A : Ty) (t : Term) :
    reqKind Γ (eta k' A t) = kindOfRank (dem Γ 0 t (headMode Γ t)) := by
  have e := dem_lift A t [] Γ 0 1 (headMode Γ t) (.inr ⟨by simp, rfl⟩)
  have hh := headMode_lift [] Γ A t
  simp only [List.nil_append, List.length_nil] at e hh
  simp only [eta, reqKind, dem, hh, e]
  simp

/-- **(T2, general form) Coercion by η-expansion.**  If `t : A →[k] B` is
    well-owned when evaluated as a function head, then for every `k'` the
    wrapper `λ^{k'} x. (↑t) x` is well-typed at `A →[k'] B`, its required kind
    is the kind demanded by evaluating `t`, and it is well-owned — leaving the
    state that evaluating `t` leaves — as soon as that kind is `⊑ k'`. -/
theorem eta_coercion_general {Γ S S₁ t k k' A B m}
    (ht : Typed Γ t (.arr k A B)) (ho : Own Γ S t (headMode Γ t) S₁) :
    Typed Γ (eta k' A t) (.arr k' A B) ∧
    reqKind Γ (eta k' A t) = kindOfRank (dem Γ 0 t (headMode Γ t)) ∧
    (reqKind Γ (eta k' A t) ≤ k' → Own Γ S (eta k' A t) m S₁) := by
  refine ⟨.lam (.app (typed_lift ht [] Γ A rfl) (.var rfl)), eta_reqKind Γ k' A t, fun hk => ?_⟩
  have h1 := own_lift ho [] Γ A rfl
  simp only [List.nil_append, List.length_nil, St.ins_zero] at h1
  have hh := headMode_lift [] Γ A t
  simp only [List.nil_append, List.length_nil] at hh
  rw [← hh] at h1
  have h2 : Own (A :: Γ) S₁.push (.var 0) .consume
      (if A.copy = false then S₁.push.moveV 0 else S₁.push) :=
    (Own.var (A := A) rfl (fun _ => rfl)).cast (by simp)
  have hd : dem (A :: Γ) 1 (.app (lift 0 t) (.var 0)) .consume ≤ (capmode k').rank := by
    have := (sideCondition_iff Γ k' A (.app (lift 0 t) (.var 0))).2 hk
    exact this
  refine (Own.lam (k := k') (m := m) (Own.app h1 h2) hd).cast ?_
  apply St.ext
  · funext i; cases A.copy <;> simp [St.pop]
  · funext l; cases A.copy <;> simp [St.pop]

/-- For a variable the required kind of the wrapper is exactly its kind. -/
theorem eta_var_reqKind {Γ i k A B} (hl : lookup Γ i = some (.arr k A B)) (k' : Kind) :
    reqKind Γ (eta k' A (.var i)) = k := by
  rw [eta_reqKind]
  simp only [dem, Nat.not_lt_zero, ite_false, headMode, hl, effRank, Ty.copy,
    Bool.false_eq_true, false_and]
  rw [callmode_eq_capmode, kindOfRank_capmode]

/-- For a closed, well-owned λ value of kind `k` the required kind of the
    wrapper is at most `k`. -/
theorem eta_value_reqKind_le {Γ k k' A B b U U'}
    (ht : Typed [] (.lam k A b) (.arr k A B)) (ho : Own [] U (.lam k A b) .consume U') :
    reqKind Γ (eta k' A (.lam k A b)) ≤ k := by
  rw [eta_reqKind]
  cases ht with
  | lam hb =>
      cases ho with
      | lam _ hd =>
          have e := dem_ctx hb Γ [] 1 1 .consume (by simp) (by simp)
          simp only [List.cons_append, List.nil_append] at e
          simp only [dem, Nat.zero_add, e]
          exact (kindOfRank_le_iff (dem_le_three _ _ _ _) k).2 hd

/-- A compound term can need more than its own kind: wrapping `g y`, with
    `g : res →[fn] (unit →[fn] unit)` and `y : res`, requires `fnOnce`, because
    each call of the wrapper re-evaluates `g y` and so consumes `y`. -/
theorem eta_compound_needs_fnOnce :
    let Γ : Ctx := [.res, .arr .fn .res (.arr .fn .unit .unit)]
    let t : Term := .app (.var 1) (.var 0)
    Typed Γ t (.arr .fn .unit .unit) ∧ reqKind Γ (eta .fnMut .unit t) = .fnOnce ∧
      ∀ S m S', ¬ Own Γ S (eta .fnMut .unit t) m S' := by
  intro Γ t
  have hreq : reqKind Γ (eta .fnMut .unit t) = .fnOnce := by
    rw [eta_reqKind]
    simp [Γ, t, dem, headMode, lookup, effRank, Ty.copy, callmode, Mode.rank, kindOfRank]
  refine ⟨.app (.var rfl) (.var rfl), hreq, fun S m S' h => ?_⟩
  have := own_lam_reqKind (by simpa [eta] using h)
  simp only [eta] at hreq
  rw [hreq] at this
  simp [Kind.le_def, Kind.rank] at this

end LRL.Affine
