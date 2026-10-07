import LRL.Affine.Syntax
import LRL.Affine.Typing

/-!
# Affine core with function kinds — the ownership judgment

`Own Γ S t m S'` is the ownership judgment of the kernel as usage-state
threading (`docs/spec/ownership_model.md` §6.2 describes the kernel walk it
models): the state `S` records which variables (`S.v`) and which resource
locations (`S.l`) have been moved; `t` is checked in usage mode `m` and leaves
the state `S'`.

* A variable used in mode `erased` has no effect, even after a move; in
  `read`/`mutate`/`consume` it must not have been moved; in `consume` it
  becomes moved unless its type is Copy.
* The head of an application is used in `callmode k` when it is a variable of
  type `A →[k] B`, and is evaluated (`consume`) otherwise; the argument is
  consumed.  `read t` uses `t` in `read` mode, `consume t`, `let` values and
  the components of `iter` in `consume` mode; `ghost t` is an erased position
  (no effect and no requirement at all).
* `λ^k x:A. b`: `b` is checked with `x` fresh; uses of outer variables and of
  locations count for the outer state; side condition `required(λ) ⊑ k`,
  where the required kind is computed by `dem` (the strongest mode in which a
  captured variable or a location is used, a consumed Copy variable counting
  as a read) — see `reqKind` and `sideCondition_iff`.
* `iter n z s` (the recursor): the step function runs once per predecessor,
  so it must be a λ (kernel: `RepeatedMinorNotLambda`) whose body moves
  nothing bound outside it — its required kind is at most `fnMut`, whatever
  kind it is annotated with (kernel: `ConsumedInRepeatedScope`).  This is the
  *repetition barrier*.  The base value `z` is used once and may consume.

The kernel's walk also downgrades a captured use to `min(m, capmode k)`.  On
every derivation that satisfies the side condition that downgrade has no
effect on the state: the side condition says that every captured use of a
non-Copy variable or of a location has a mode `≤ capmode k`, and uses of Copy
variables never change the state.  `Own` therefore states captured uses
undowngraded.

Resource locations (`loc l`) are runtime values.  For them only `consume`
has a requirement (the location is live) and an effect (it becomes dead); a
`read` of a location is not tracked.  This is the runtime extension of the
judgment needed for preservation: a closure that only reads a captured
resource does not move it, so the resource may be consumed before the
closure runs (`Affine/Examples.lean`).  Ruling such reads out is the job of
the borrow checker (MIR), not of the kernel judgment modelled here.
-/

namespace LRL.Affine

/-! ### Modes of occurrences -/

/-- Mode in which the head of an application is used: `callmode k` for a
    variable of type `A →[k] B`, `consume` (evaluation) for any other head. -/
def headMode (Γ : Ctx) : Term → Mode
  | .var i =>
      match lookup Γ i with
      | some (.arr k _ _) => callmode k
      | _ => .consume
  | _ => .consume

theorem headMode_nonvar {Γ : Ctx} {f : Term} (h : ∀ i, f ≠ .var i) :
    headMode Γ f = .consume := by
  cases f <;> simp_all [headMode]

theorem headMode_var_arr {Γ : Ctx} {i : Nat} {k : Kind} {A B : Ty}
    (h : lookup Γ i = some (.arr k A B)) : headMode Γ (.var i) = callmode k := by
  simp [headMode, h]

@[simp] theorem headMode_nil (f : Term) : headMode [] f = .consume := by
  cases f <;> simp [headMode, lookup]

/-- Rank contributed to the required kind by a captured variable of type
    `A` used in mode `m`: a consumed Copy variable counts as a read. -/
def effRank : Option Ty → Mode → Nat
  | some A, m => if A.copy = true ∧ m = .consume then 1 else m.rank
  | none, m => m.rank

/-- `dem Γ d t m`: the rank of the strongest mode in which `t`, used in mode
    `m`, uses a variable with index `≥ d` (i.e. one bound outside the
    innermost `d` binders) or a resource location.  Under a binder the
    threshold `d` grows by one.  Erased positions contribute nothing. -/
def dem (Γ : Ctx) (d : Nat) : Term → Mode → Nat
  | .var i, m => if i < d then 0 else effRank (lookup Γ i) m
  | .unit, _ => 0
  | .lit _, _ => 0
  | .loc _, m => m.rank
  | .lam _ A b, _ => dem (A :: Γ) (d + 1) b .consume
  | .app f a, _ => max (dem Γ d f (headMode Γ f)) (dem Γ d a .consume)
  | .letE A v b, _ => max (dem Γ d v .consume) (dem (A :: Γ) (d + 1) b .consume)
  | .consume t, _ => dem Γ d t .consume
  | .read t, _ => dem Γ d t .read
  | .iter n z s, _ => max (dem Γ d n .consume) (max (dem Γ d z .consume) (dem Γ d s .consume))
  | .ghost _, _ => 0

/-- The required kind of a λ: the least kind whose capture mode admits every
    captured use (`required(λ)` of the design notes). -/
def reqKind (Γ : Ctx) : Term → Kind
  | .lam _ A b => kindOfRank (dem (A :: Γ) 1 b .consume)
  | _ => .fn

/-- `1` for a consuming use, `0` otherwise. -/
def useC (m : Mode) : Nat := if m = .consume then 1 else 0

/-- Number of consuming occurrences of resource location `l` in `t` used in
    mode `m` (outside erased positions). -/
def cl (l : Nat) : Term → Mode → Nat
  | .var _, _ => 0
  | .unit, _ => 0
  | .lit _, _ => 0
  | .loc l', m => if l' = l then useC m else 0
  | .lam _ _ b, _ => cl l b .consume
  | .app f a, _ => cl l f .consume + cl l a .consume
  | .letE _ v b, _ => cl l v .consume + cl l b .consume
  | .consume t, _ => cl l t .consume
  | .read t, _ => cl l t .read
  | .iter n z s, _ => cl l n .consume + cl l z .consume + cl l s .consume
  | .ghost _, _ => 0

/-! ### Required kind and the side condition -/

theorem effRank_le_three (A : Option Ty) (m : Mode) : effRank A m ≤ 3 := by
  cases A <;> cases m <;> simp [effRank, Mode.rank] <;> split <;> simp

theorem dem_le_three (Γ : Ctx) (d : Nat) (t : Term) (m : Mode) : dem Γ d t m ≤ 3 := by
  induction t generalizing Γ d m with
  | var i =>
      simp only [dem]; split
      · omega
      · exact effRank_le_three _ _
  | loc r => cases m <;> simp [dem, Mode.rank]
  | unit | lit | ghost => simp [dem]
  | lam k A b ih => simp only [dem]; exact ih _ _ _
  | app f a ihf iha =>
      simp only [dem]; have := ihf Γ d (headMode Γ f); have := iha Γ d .consume; omega
  | letE A v b ihv ihb =>
      simp only [dem]; have := ihv Γ d .consume; have := ihb (A :: Γ) (d + 1) .consume; omega
  | consume t ih => simp only [dem]; exact ih _ _ _
  | read t ih => simp only [dem]; exact ih _ _ _
  | iter n z s ihn ihz ihs =>
      simp only [dem]
      have := ihn Γ d .consume; have := ihz Γ d .consume; have := ihs Γ d .consume; omega

/-- The side condition used in `Own.lam` is exactly `required(λ) ⊑ k`. -/
theorem sideCondition_iff (Γ : Ctx) (k : Kind) (A : Ty) (b : Term) :
    dem (A :: Γ) 1 b .consume ≤ (capmode k).rank ↔ reqKind Γ (.lam k A b) ≤ k := by
  simp only [reqKind]
  exact (kindOfRank_le_iff (dem_le_three _ _ _ _) k).symm

theorem kindOfRank_capmode (k : Kind) : kindOfRank (capmode k).rank = k := by
  cases k <;> rfl

/-- The repetition barrier `dem ≤ rank MUT` says `required(λ) ⊑ fnMut`. -/
theorem barrier_iff (Γ : Ctx) (k : Kind) (A : Ty) (b : Term) :
    dem (A :: Γ) 1 b .consume ≤ Mode.mutate.rank ↔ reqKind Γ (.lam k A b) ≤ .fnMut := by
  have := kindOfRank_le_iff (dem_le_three (A :: Γ) 1 b .consume) .fnMut
  simp only [reqKind]
  exact this.symm

/-! ### Basic facts about consumption counts -/

theorem useC_le_one (m : Mode) : useC m ≤ 1 := by
  cases m <;> simp [useC]

theorem cl_mode_le (l : Nat) (t : Term) (m : Mode) : cl l t m ≤ cl l t .consume := by
  cases t <;> simp only [cl] <;> try exact Nat.le_refl _
  split
  · simp [useC]; split <;> omega
  · omega

theorem cl_headMode (l : Nat) (Γ : Ctx) (f : Term) :
    cl l f (headMode Γ f) = cl l f .consume := by
  cases f <;> simp [headMode, cl]

/-- A consuming occurrence of a location forces the demand to CONSUME. -/
theorem cl_pos_dem {l : Nat} :
    ∀ (t : Term) (Γ : Ctx) (d : Nat) (m : Mode), 0 < cl l t m → 3 ≤ dem Γ d t m := by
  intro t
  induction t with
  | var i => intro Γ d m h; simp [cl] at h
  | unit => intro Γ d m h; simp [cl] at h
  | lit n => intro Γ d m h; simp [cl] at h
  | ghost t _ => intro Γ d m h; simp [cl] at h
  | loc r =>
      intro Γ d m h
      simp only [cl] at h
      split at h
      · cases m <;> simp_all [useC, dem, Mode.rank]
      · omega
  | lam k A b ih => intro Γ d m h; simp only [cl, dem] at h ⊢; exact ih _ _ _ h
  | app f a ihf iha =>
      intro Γ d m h
      simp only [cl, dem] at h ⊢
      by_cases hf : 0 < cl l f .consume
      · by_cases hv : ∃ i, f = .var i
        · obtain ⟨i, rfl⟩ := hv; simp [cl] at hf
        · rw [headMode_nonvar (fun i hi => hv ⟨i, hi⟩)]
          have := ihf Γ d .consume hf; omega
      · have := iha Γ d .consume (by omega); omega
  | letE A v b ihv ihb =>
      intro Γ d m h
      simp only [cl, dem] at h ⊢
      by_cases hv : 0 < cl l v .consume
      · have := ihv Γ d .consume hv; omega
      · have := ihb (A :: Γ) (d + 1) .consume (by omega); omega
  | consume t ih => intro Γ d m h; simp only [cl, dem] at h ⊢; exact ih _ _ _ h
  | read t ih => intro Γ d m h; simp only [cl, dem] at h ⊢; exact ih _ _ _ h
  | iter n z s ihn ihz ihs =>
      intro Γ d m h
      simp only [cl, dem] at h ⊢
      by_cases hn : 0 < cl l n .consume
      · have := ihn Γ d .consume hn; omega
      · by_cases hz : 0 < cl l z .consume
        · have := ihz Γ d .consume hz; omega
        · have := ihs Γ d .consume (by omega); omega

/-- A λ whose demand is at most MUT consumes no location. -/
theorem cl_lam_of_dem {Γ : Ctx} {k : Kind} {A : Ty} {b : Term}
    (hd : dem (A :: Γ) 1 b .consume ≤ 2) (l : Nat) (m : Mode) :
    cl l (.lam k A b) m = 0 := by
  simp only [cl]
  by_cases h : 0 < cl l b .consume
  · have := cl_pos_dem b (A :: Γ) 1 .consume h; omega
  · omega

/-- `pos n = true` iff `0 < n` (a `Bool` test without a decidability
    instance, so that `simp` can rewrite under it). -/
def pos : Nat → Bool
  | 0 => false
  | _ + 1 => true

@[simp] theorem pos_zero : pos 0 = false := rfl

@[simp] theorem pos_eq_true (n : Nat) : pos n = true ↔ 0 < n := by
  cases n <;> simp [pos]

@[simp] theorem pos_eq_false (n : Nat) : pos n = false ↔ n = 0 := by
  cases n <;> simp [pos]

theorem pos_add (a b : Nat) : pos (a + b) = (pos a || pos b) := by
  cases a <;> cases b <;> simp [pos] <;> omega

/-! ### Usage states -/

/-- Usage state: `v i = true` iff variable `i` has been moved; `l r = true`
    iff resource location `r` has been moved. -/
@[ext] structure St where
  v : Nat → Bool
  l : Nat → Bool

/-- The initial state: nothing moved. -/
def St.empty : St := ⟨fun _ => false, fun _ => false⟩

/-- Enter a binder: the new variable (index 0) is fresh. -/
def St.push (S : St) : St :=
  ⟨fun i => match i with
    | 0 => false
    | i + 1 => S.v i, S.l⟩

/-- Leave a binder: forget index 0. -/
def St.pop (S : St) : St := ⟨fun i => S.v (i + 1), S.l⟩

/-- Mark variable `x` moved. -/
def St.moveV (S : St) (x : Nat) : St := ⟨fun i => if i = x then true else S.v i, S.l⟩

/-- Mark location `r` moved. -/
def St.moveL (S : St) (r : Nat) : St := ⟨S.v, fun i => if i = r then true else S.l i⟩

@[simp] theorem St.push_v_zero (S : St) : S.push.v 0 = false := rfl
@[simp] theorem St.push_v_succ (S : St) (i : Nat) : S.push.v (i + 1) = S.v i := rfl
@[simp] theorem St.push_l (S : St) : S.push.l = S.l := rfl
@[simp] theorem St.pop_v (S : St) (i : Nat) : S.pop.v i = S.v (i + 1) := rfl
@[simp] theorem St.pop_l (S : St) : S.pop.l = S.l := rfl
@[simp] theorem St.moveV_v (S : St) (x i : Nat) :
    (S.moveV x).v i = if i = x then true else S.v i := rfl
@[simp] theorem St.moveV_l (S : St) (x : Nat) : (S.moveV x).l = S.l := rfl
@[simp] theorem St.moveL_v (S : St) (r : Nat) : (S.moveL r).v = S.v := rfl
@[simp] theorem St.moveL_l (S : St) (r i : Nat) :
    (S.moveL r).l i = if i = r then true else S.l i := rfl

/-- Pointwise order: `S ≤ T` when everything moved in `S` is moved in `T`. -/
instance : LE St :=
  ⟨fun S T => (∀ i, S.v i = true → T.v i = true) ∧ (∀ l, S.l l = true → T.l l = true)⟩

theorem St.le_def {S T : St} :
    S ≤ T ↔ (∀ i, S.v i = true → T.v i = true) ∧ (∀ l, S.l l = true → T.l l = true) :=
  Iff.rfl

theorem St.le_refl (S : St) : S ≤ S := ⟨fun _ h => h, fun _ h => h⟩

theorem St.le_trans {S T U : St} (h₁ : S ≤ T) (h₂ : T ≤ U) : S ≤ U :=
  ⟨fun i h => h₂.1 i (h₁.1 i h), fun l h => h₂.2 l (h₁.2 l h)⟩

theorem St.push_le {S T : St} (h : S ≤ T) : S.push ≤ T.push := by
  refine ⟨fun i hi => ?_, fun l hl => h.2 l hl⟩
  cases i with
  | zero => simp at hi
  | succ i => exact h.1 i hi

theorem St.pop_le {S T : St} (h : S ≤ T) : S.pop ≤ T.pop :=
  ⟨fun i hi => h.1 (i + 1) hi, fun l hl => h.2 l hl⟩

theorem St.moveV_le {S T : St} (h : S ≤ T) (x : Nat) : S.moveV x ≤ T.moveV x := by
  refine ⟨fun i hi => ?_, fun l hl => h.2 l hl⟩
  simp only [St.moveV_v] at hi ⊢
  split at hi
  · simp_all
  · simp_all [h.1 i hi]

theorem St.moveL_le {S T : St} (h : S ≤ T) (r : Nat) : S.moveL r ≤ T.moveL r := by
  refine ⟨fun i hi => h.1 i hi, fun l hl => ?_⟩
  simp only [St.moveL_l] at hl ⊢
  split at hl
  · simp_all
  · simp_all [h.2 l hl]

theorem St.le_moveV (S : St) (x : Nat) : S ≤ S.moveV x := by
  refine ⟨fun i hi => ?_, fun l hl => hl⟩
  simp only [St.moveV_v]; split <;> simp_all

theorem St.le_moveL (S : St) (r : Nat) : S ≤ S.moveL r := by
  refine ⟨fun i hi => hi, fun l hl => ?_⟩
  simp only [St.moveL_l]; split <;> simp_all

/-! ### The static judgment -/

/-- The ownership judgment `Γ; S ⊢ t : m ⊣ S'`. -/
inductive Own : Ctx → St → Term → Mode → St → Prop where
  | var {Γ S i A m} :
      lookup Γ i = some A → (m ≠ .erased → S.v i = false) →
      Own Γ S (.var i) m (if m = .consume ∧ A.copy = false then S.moveV i else S)
  | loc {Γ S r m} :
      (m = .consume → S.l r = false) →
      Own Γ S (.loc r) m (if m = .consume then S.moveL r else S)
  | unit {Γ S m} : Own Γ S .unit m S
  | lit {Γ S n m} : Own Γ S (.lit n) m S
  | lam {Γ S S' k A b m} :
      Own (A :: Γ) S.push b .consume S' →
      dem (A :: Γ) 1 b .consume ≤ (capmode k).rank →
      Own Γ S (.lam k A b) m S'.pop
  | app {Γ S S₁ S₂ f a m} :
      Own Γ S f (headMode Γ f) S₁ → Own Γ S₁ a .consume S₂ →
      Own Γ S (.app f a) m S₂
  | letE {Γ S S₁ S₂ A v b m} :
      Own Γ S v .consume S₁ → Own (A :: Γ) S₁.push b .consume S₂ →
      Own Γ S (.letE A v b) m S₂.pop
  | consume {Γ S S' t m} : Own Γ S t .consume S' → Own Γ S (.consume t) m S'
  | read {Γ S S' t m} : Own Γ S t .read S' → Own Γ S (.read t) m S'
  | iter {Γ S S₁ S₂ S₃ n z k C b m} :
      Own Γ S n .consume S₁ → Own Γ S₁ z .consume S₂ →
      Own Γ S₂ (.lam k C b) .consume S₃ →
      dem (C :: Γ) 1 b .consume ≤ Mode.mutate.rank →
      Own Γ S (.iter n z (.lam k C b)) m S₃
  | ghost {Γ S t m} : Own Γ S (.ghost t) m S

theorem Own.cast {Γ S t m S' S''} (h : Own Γ S t m S') (e : S' = S'') : Own Γ S t m S'' :=
  e ▸ h

/-! ### Structural properties of `Own` -/

/-- The judgment for a λ does not depend on the mode it is used in. -/
theorem own_lam_mode {Γ S k A b m S'} (h : Own Γ S (.lam k A b) m S') (m' : Mode) :
    Own Γ S (.lam k A b) m' S' := by
  cases h with
  | lam hb hd => exact .lam hb hd

/-- The locations moved by a well-owned term are exactly those it consumes. -/
theorem own_l {Γ S t m S'} (h : Own Γ S t m S') :
    ∀ l, S'.l l = (S.l l || pos (cl l t m)) := by
  induction h with
  | var _ _ => intro l; split <;> simp [cl]
  | @loc Γ S r m _ =>
      intro l
      by_cases hm : m = .consume <;> by_cases hr : r = l
      · subst hm hr; simp [cl, useC]
      · subst hm; simp [cl, hr, Ne.symm hr]
      · subst hr; simp [cl, useC, hm]
      · simp [cl, hm, hr]
  | unit | lit | ghost => intro l; simp [cl]
  | lam _ _ ih => intro l; simp [cl, ih]
  | app _ _ ihf iha =>
      intro l; rw [iha, ihf]; simp [cl, cl_headMode, pos_add, Bool.or_assoc]
  | letE _ _ ihv ihb =>
      intro l; simp only [St.pop_l]; rw [ihb]; simp [ihv, cl, pos_add, Bool.or_assoc]
  | consume _ ih => intro l; simp [cl, ih]
  | read _ ih => intro l; simp [cl, ih]
  | iter _ _ _ _ ihn ihz ihs =>
      intro l; rw [ihs, ihz, ihn]; simp [cl, pos_add, Bool.or_assoc]

/-- A location consumed by a well-owned term is live before it. -/
theorem own_cl_req {Γ S t m S'} (h : Own Γ S t m S') :
    ∀ l, 0 < cl l t m → S.l l = false := by
  induction h with
  | var _ _ => intro l h; simp [cl] at h
  | @loc Γ S r m hr =>
      intro l h
      simp only [cl] at h
      split at h
      · subst_vars
        cases m <;> simp_all [useC]
      · omega
  | unit | lit | ghost => intro l h; simp [cl] at h
  | lam _ _ ih => intro l h; simp only [cl] at h; simpa using ih l h
  | @app Γ S S₁ S₂ f a m hf ha ihf iha =>
      intro l h
      simp only [cl] at h
      by_cases h1 : 0 < cl l f .consume
      · exact ihf l (by rw [cl_headMode]; exact h1)
      · have h2 := iha l (by omega)
        rw [own_l hf] at h2
        simp at h2; exact h2.1
  | @letE Γ S S₁ S₂ A v b m hv hb ihv ihb =>
      intro l h
      simp only [cl] at h
      by_cases h1 : 0 < cl l v .consume
      · exact ihv l h1
      · have h2 := ihb l (by omega)
        simp only [St.push_l] at h2
        rw [own_l hv] at h2
        simp at h2; exact h2.1
  | consume _ ih => intro l h; exact ih l h
  | read _ ih => intro l h; exact ih l h
  | @iter Γ S S₁ S₂ S₃ n z k C b m hn hz hs _ ihn ihz ihs =>
      intro l h
      simp only [cl] at h
      by_cases h1 : 0 < cl l n .consume
      · exact ihn l h1
      · by_cases h2 : 0 < cl l z .consume
        · have h3 := ihz l h2
          rw [own_l hn] at h3; simp at h3; exact h3.1
        · have h3 := ihs l (by simp only [cl] at h ⊢; omega)
          rw [own_l hz, own_l hn] at h3; simp at h3; exact h3.1.1

theorem own_var_lt {Γ S i m S'} (h : Own Γ S (.var i) m S') : i < Γ.length := by
  cases h with
  | var hl _ => exact lookup_lt hl

/-- Variables outside the context are untouched. -/
theorem own_v_out {Γ S t m S'} (h : Own Γ S t m S') :
    ∀ i, Γ.length ≤ i → S'.v i = S.v i := by
  induction h with
  | @var Γ S i' A m hl _ =>
      intro i hi
      have := lookup_lt hl
      split
      · simp; omega
      · rfl
  | loc _ => intro i _; split <;> simp
  | unit | lit | ghost => intro i _; rfl
  | lam _ _ ih => intro i hi; simp only [St.pop_v]; rw [ih (i + 1) (by simp; omega)]; rfl
  | app _ _ ihf iha => intro i hi; rw [iha i hi, ihf i hi]
  | letE _ _ ihv ihb =>
      intro i hi; simp only [St.pop_v]; rw [ihb (i + 1) (by simp; omega)]; simp [ihv i hi]
  | consume _ ih => exact ih
  | read _ ih => exact ih
  | iter _ _ _ _ ihn ihz ihs => intro i hi; rw [ihs i hi, ihz i hi, ihn i hi]

/-- The state only grows. -/
theorem own_ge {Γ S t m S'} (h : Own Γ S t m S') : S ≤ S' := by
  induction h with
  | var _ _ => split; exact St.le_moveV _ _; exact St.le_refl _
  | loc _ => split; exact St.le_moveL _ _; exact St.le_refl _
  | unit | lit | ghost => exact St.le_refl _
  | lam _ _ ih =>
      exact ⟨fun i hi => ih.1 (i + 1) (by simpa using hi), fun l hl => ih.2 l (by simpa using hl)⟩
  | app _ _ ihf iha => exact St.le_trans ihf iha
  | letE _ _ ihv ihb =>
      refine St.le_trans ihv ⟨fun i hi => ihb.1 (i + 1) (by simpa using hi), fun l hl => ihb.2 l (by simpa using hl)⟩
  | consume _ ih => exact ih
  | read _ ih => exact ih
  | iter _ _ _ _ ihn ihz ihs => exact St.le_trans ihn (St.le_trans ihz ihs)

/-- Monotonicity: a well-owned term stays well-owned from a smaller state
    (fewer things moved), and leaves a smaller state. -/
theorem own_mono {Γ S t m S'} (h : Own Γ S t m S') :
    ∀ U, U ≤ S → ∃ U', Own Γ U t m U' ∧ U' ≤ S' := by
  induction h with
  | @var Γ S i A m hl hreq =>
      intro U hU
      refine ⟨_, .var hl (fun hm => ?_), ?_⟩
      · have := hreq hm
        cases hu : U.v i
        · rfl
        · simp_all [hU.1 i hu]
      · split
        · exact St.moveV_le hU i
        · exact hU
  | @loc Γ S r m hreq =>
      intro U hU
      refine ⟨_, .loc (fun hm => ?_), ?_⟩
      · have := hreq hm
        cases hu : U.l r
        · rfl
        · simp_all [hU.2 r hu]
      · split
        · exact St.moveL_le hU r
        · exact hU
  | unit => intro U hU; exact ⟨U, .unit, hU⟩
  | lit => intro U hU; exact ⟨U, .lit, hU⟩
  | ghost => intro U hU; exact ⟨U, .ghost, hU⟩
  | lam _ hd ih =>
      intro U hU
      obtain ⟨U'', h'', hle⟩ := ih _ (St.push_le hU)
      exact ⟨_, .lam h'' hd, St.pop_le hle⟩
  | app _ _ ihf iha =>
      intro U hU
      obtain ⟨U₁, h₁, hle₁⟩ := ihf U hU
      obtain ⟨U₂, h₂, hle₂⟩ := iha U₁ hle₁
      exact ⟨U₂, .app h₁ h₂, hle₂⟩
  | letE _ _ ihv ihb =>
      intro U hU
      obtain ⟨U₁, h₁, hle₁⟩ := ihv U hU
      obtain ⟨U₂, h₂, hle₂⟩ := ihb _ (St.push_le hle₁)
      exact ⟨_, .letE h₁ h₂, St.pop_le hle₂⟩
  | consume _ ih =>
      intro U hU
      obtain ⟨U', h', hle⟩ := ih U hU
      exact ⟨U', .consume h', hle⟩
  | read _ ih =>
      intro U hU
      obtain ⟨U', h', hle⟩ := ih U hU
      exact ⟨U', .read h', hle⟩
  | iter _ _ _ hd ihn ihz ihs =>
      intro U hU
      obtain ⟨U₁, h₁, hle₁⟩ := ihn U hU
      obtain ⟨U₂, h₂, hle₂⟩ := ihz U₁ hle₁
      obtain ⟨U₃, h₃, hle₃⟩ := ihs U₂ hle₂
      exact ⟨U₃, .iter h₁ h₂ h₃ hd, hle₃⟩

/-- A term checked in mode CONSUME can be used in any mode, leaving a smaller
    state. -/
theorem own_mode {Γ S t S'} (h : Own Γ S t .consume S') (m : Mode) :
    ∃ S'', Own Γ S t m S'' ∧ S'' ≤ S' := by
  cases h with
  | @var _ _ i A _ hl hreq =>
      refine ⟨_, .var hl (fun _ => hreq (by simp)), ?_⟩
      split
      · simp_all
        exact St.le_refl _
      · split
        · exact St.le_moveV _ _
        · exact St.le_refl _
  | @loc _ _ r _ hreq =>
      refine ⟨_, .loc (fun _ => hreq rfl), ?_⟩
      split
      · subst_vars; exact St.le_refl _
      · simp only [ite_true]; exact St.le_moveL _ _
  | unit => exact ⟨_, .unit, St.le_refl _⟩
  | lit => exact ⟨_, .lit, St.le_refl _⟩
  | ghost => exact ⟨_, .ghost, St.le_refl _⟩
  | lam hb hd => exact ⟨_, .lam hb hd, St.le_refl _⟩
  | app hf ha => exact ⟨_, .app hf ha, St.le_refl _⟩
  | letE hv hb => exact ⟨_, .letE hv hb, St.le_refl _⟩
  | consume ht => exact ⟨_, .consume ht, St.le_refl _⟩
  | read ht => exact ⟨_, .read ht, St.le_refl _⟩
  | iter hn hz hs hd => exact ⟨_, .iter hn hz hs hd, St.le_refl _⟩

/-- A variable bound outside the threshold `d` that a well-owned term moves
    forces the demand to CONSUME. -/
theorem own_v_dem {Γ S t m S'} (h : Own Γ S t m S') :
    ∀ d i, d ≤ i → S'.v i = true → S.v i = false → 3 ≤ dem Γ d t m := by
  induction h with
  | @var Γ S i' A m hl _ =>
      intro d i hdi h1 h2
      split at h1
      · rename_i hc
        simp only [St.moveV_v] at h1
        split at h1
        · subst_vars
          have hnd : ¬ (i < d) := by omega
          simp [dem, hl, effRank, hnd, hc.1, hc.2, Mode.rank]
        · simp_all
      · simp_all
  | loc _ => intro d i _ h1 h2; split at h1 <;> simp_all
  | unit | lit | ghost => intro d i _ h1 h2; simp_all
  | lam _ _ ih =>
      intro d i hdi h1 h2
      simp only [dem]
      exact ih (d + 1) (i + 1) (by omega) h1 (by simpa using h2)
  | @app Γ S S₁ S₂ f a m _ _ ihf iha =>
      intro d i hdi h1 h2
      simp only [dem]
      cases h3 : S₁.v i
      · have := iha d i hdi h1 h3; omega
      · have := ihf d i hdi h3 h2; omega
  | @letE Γ S S₁ S₂ A v b m _ _ ihv ihb =>
      intro d i hdi h1 h2
      simp only [dem]
      cases h3 : S₁.v i
      · have := ihb (d + 1) (i + 1) (by omega) (by simpa using h1) (by simpa using h3); omega
      · have := ihv d i hdi h3 h2; omega
  | consume _ ih => intro d i hdi h1 h2; simp only [dem]; exact ih d i hdi h1 h2
  | read _ ih => intro d i hdi h1 h2; simp only [dem]; exact ih d i hdi h1 h2
  | @iter Γ S S₁ S₂ S₃ n z k C b m _ _ _ _ ihn ihz ihs =>
      intro d i hdi h1 h2
      simp only [dem]
      cases h3 : S₁.v i
      · cases h4 : S₂.v i
        · have := ihs d i hdi h1 h4; simp only [dem] at this; omega
        · have := ihz d i hdi h4 h3; omega
      · have := ihn d i hdi h3 h2; omega

/-- **Repetition barrier.**  A λ whose body moves nothing bound outside it
    (demand at most MUT) leaves the state unchanged. -/
theorem own_lam_noeff {Γ S k A b m S'} (h : Own Γ S (.lam k A b) m S')
    (hd : dem (A :: Γ) 1 b .consume ≤ 2) : S' = S := by
  cases h with
  | @lam _ _ S'' _ _ _ _ hb _ =>
      apply St.ext
      · funext i
        simp only [St.pop_v]
        cases hs : S.v i
        · cases h1 : S''.v (i + 1)
          · rfl
          · have := own_v_dem hb 1 (i + 1) (by omega) h1 (by simpa using hs); omega
        · exact (own_ge hb).1 (i + 1) (by simpa using hs)
      · funext l
        simp only [St.pop_l]
        rw [own_l hb]
        have : cl l b .consume = 0 := by
          by_cases hc : 0 < cl l b .consume
          · have := cl_pos_dem b (A :: Γ) 1 .consume hc; omega
          · omega
        simp [this]

/-! ### Context extension and framing -/

theorem headMode_append_of_lt (Γ Δ : Ctx) (f : Term)
    (h : ∀ i, f = .var i → i < Γ.length) : headMode (Γ ++ Δ) f = headMode Γ f := by
  cases f with
  | var i => simp only [headMode, lookup_append_lt _ _ _ (h i rfl)]
  | _ => rfl

theorem headMode_append_own {Γ S f m S'} (h : Own Γ S f m S') (Δ : Ctx) :
    headMode (Γ ++ Δ) f = headMode Γ f :=
  headMode_append_of_lt Γ Δ f (fun i hi => by subst hi; exact own_var_lt h)

/-- The demand of a well-owned term does not depend on bindings beyond its
    context. -/
theorem dem_append_own {Γ S t m S'} (h : Own Γ S t m S') :
    ∀ Δ d, dem (Γ ++ Δ) d t m = dem Γ d t m := by
  induction h with
  | var hl _ => intro Δ d; simp only [dem, lookup_append_lt _ _ _ (lookup_lt hl)]
  | loc _ | unit | lit | ghost => intro Δ d; simp [dem]
  | lam _ _ ih => intro Δ d; simp only [dem]; exact ih Δ (d + 1)
  | app hf _ ihf iha =>
      intro Δ d; simp only [dem]; rw [headMode_append_own hf Δ, ihf, iha]
  | letE _ _ ihv ihb => intro Δ d; simp only [dem]; rw [ihv]; exact congrArg _ (ihb Δ (d + 1))
  | consume _ ih => intro Δ d; simp only [dem]; exact ih Δ d
  | read _ ih => intro Δ d; simp only [dem]; exact ih Δ d
  | iter _ _ _ _ ihn ihz ihs =>
      intro Δ d; have := ihs Δ d; simp only [dem] at this ⊢; rw [ihn, ihz, this]

/-- The state left by re-running a derivation `Γ; S ⊢ t : m ⊣ S'` from the
    state `W` in an extended context: the variables of `Γ` end as in `S'`,
    the others as in `W`, and `t`'s consumed locations are added to `W`. -/
def St.frame (n : Nat) (S' W : St) (t : Term) (m : Mode) : St :=
  ⟨fun i => if i < n then S'.v i else W.v i, fun l => W.l l || pos (cl l t m)⟩

/-- **Frame lemma.**  A derivation can be replayed in an extended context
    from any state that agrees on the variables of the context and in which
    the locations consumed by the term are live. -/
theorem own_frame {Γ S t m S'} (h : Own Γ S t m S') :
    ∀ Δ W, (∀ i, i < Γ.length → W.v i = S.v i) → (∀ l, 0 < cl l t m → W.l l = false) →
      Own (Γ ++ Δ) W t m (St.frame Γ.length S' W t m) := by
  induction h with
  | @var Γ S i A m hl hreq =>
      intro Δ W hv _
      have hi := lookup_lt hl
      refine (Own.var (lookup_append_lt _ _ _ hi ▸ hl) (fun hm => by rw [hv i hi]; exact hreq hm)).cast ?_
      apply St.ext
      · funext j
        simp only [St.frame]
        by_cases hc : m = .consume ∧ A.copy = false
        · simp only [hc, and_self, ite_true, St.moveV_v]
          by_cases hj : j = i
          · subst hj; simp [hi]
          · simp only [hj, ite_false]
            split
            · exact hv j ‹_›
            · rfl
        · simp only [hc, ite_false]
          split
          · exact hv j ‹_›
          · rfl
      · funext l
        simp only [St.frame, cl, pos_zero, Bool.or_false]
        split <;> rfl
  | @loc Γ S r m hreq =>
      intro Δ W hv hl
      refine (Own.loc (fun hm => hl r (by subst hm; simp [cl, useC]))).cast ?_
      apply St.ext
      · funext j
        simp only [St.frame]
        by_cases hj : j < Γ.length
        · simp only [hj, ite_true]; split <;> simp [hv j hj]
        · simp only [hj, ite_false]; split <;> simp
      · funext l
        simp only [St.frame, cl]
        by_cases hm : m = .consume <;> by_cases hr : r = l
        · subst hm hr; simp [useC]
        · subst hm; simp [hr, Ne.symm hr]
        · subst hr; simp [useC, hm]
        · simp [hm, hr]
  | unit | lit | ghost =>
      intro Δ W hv _
      first
        | refine (Own.unit).cast ?_
        | refine (Own.lit).cast ?_
        | refine (Own.ghost).cast ?_
      all_goals
        apply St.ext
        · funext j; simp only [St.frame]; split
          · exact hv j ‹_›
          · rfl
        · funext l; simp [St.frame, cl]
  | @lam Γ S S' k A b m hb hd ih =>
      intro Δ W hv hl
      have hb' := ih Δ W.push
        (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => simp only [St.push_v_succ]; exact hv i (by simp at hi; omega))
        (fun l hcl => by simpa using hl l (by simpa [cl] using hcl))
      have hd' : dem (A :: (Γ ++ Δ)) 1 b .consume ≤ (capmode k).rank := by
        have := dem_append_own hb Δ 1
        simp only [List.cons_append] at this
        rw [this]; exact hd
      refine (Own.lam hb' hd').cast ?_
      apply St.ext
      · funext j
        simp only [St.frame, St.pop_v, List.length_cons]
        by_cases hj : j < Γ.length
        · simp [hj]
        · simp [hj]
      · funext l; simp [St.frame, cl]
  | @app Γ S S₁ S₂ f a m hf ha ihf iha =>
      intro Δ W hv hl
      have hf' := ihf Δ W hv (fun l h => hl l (by simp only [cl]; rw [cl_headMode] at h; omega))
      rw [← headMode_append_own hf Δ] at hf'
      have ha' := iha Δ (St.frame Γ.length S₁ W f (headMode (Γ ++ Δ) f))
        (fun i hi => by simp [St.frame, hi])
        (fun l h => by
          have h1 := own_cl_req ha l h
          rw [own_l hf] at h1
          simp only [Bool.or_eq_false_iff, cl_headMode] at h1
          simp only [St.frame, Bool.or_eq_false_iff, cl_headMode]
          exact ⟨hl l (by simp only [cl]; omega), h1.2⟩)
      refine (Own.app hf' ha').cast ?_
      apply St.ext
      · funext j; simp only [St.frame]; split <;> simp_all
      · funext l; simp [St.frame, cl, cl_headMode, pos_add, Bool.or_assoc]
  | @letE Γ S S₁ S₂ A v b m hv hb ihv ihb =>
      intro Δ W hW hl
      have hv' := ihv Δ W hW (fun l h => hl l (by simp only [cl]; omega))
      have hb' := ihb Δ (St.frame Γ.length S₁ W v .consume).push
        (fun i hi => by
          cases i with
          | zero => rfl
          | succ i =>
              simp only [St.push_v_succ, St.frame]
              simp at hi
              simp [show i < Γ.length by omega])
        (fun l h => by
          have h1 := own_cl_req hb l h
          simp only [St.push_l] at h1
          rw [own_l hv] at h1
          simp only [Bool.or_eq_false_iff] at h1
          simp only [St.push_l, St.frame, Bool.or_eq_false_iff]
          exact ⟨hl l (by simp only [cl]; omega), h1.2⟩)
      refine (Own.letE hv' hb').cast ?_
      apply St.ext
      · funext j
        simp only [St.frame, St.pop_v, List.length_cons, St.push_v_succ]
        by_cases hj : j < Γ.length
        · simp [hj]
        · simp [hj]
      · funext l; simp [St.frame, cl, pos_add, Bool.or_assoc]
  | @consume Γ S S' t m ht ih =>
      intro Δ W hv hl
      exact (Own.consume (ih Δ W hv (fun l h => hl l (by simpa [cl] using h)))).cast
        (by simp [St.frame, cl])
  | @read Γ S S' t m ht ih =>
      intro Δ W hv hl
      exact (Own.read (ih Δ W hv (fun l h => hl l (by simpa [cl] using h)))).cast
        (by simp [St.frame, cl])
  | @iter Γ S S₁ S₂ S₃ n z k C b m hn hz hs hd ihn ihz ihs =>
      intro Δ W hW hl
      have hn' := ihn Δ W hW (fun l h => hl l (by simp only [cl]; omega))
      have hz' := ihz Δ (St.frame Γ.length S₁ W n .consume) (fun i hi => by simp [St.frame, hi])
        (fun l h => by
          have h1 := own_cl_req hz l h
          rw [own_l hn] at h1
          simp only [Bool.or_eq_false_iff] at h1
          simp only [St.frame, Bool.or_eq_false_iff]
          exact ⟨hl l (by simp only [cl] at h ⊢; omega), h1.2⟩)
      have hs' := ihs Δ (St.frame Γ.length S₂ (St.frame Γ.length S₁ W n .consume) z .consume)
        (fun i hi => by simp [St.frame, hi])
        (fun l h => by
          have h1 := own_cl_req hs l h
          rw [own_l hz, own_l hn] at h1
          simp only [Bool.or_eq_false_iff] at h1
          simp only [St.frame, Bool.or_eq_false_iff]
          exact ⟨⟨hl l (by simp only [cl] at h ⊢; omega), h1.1.2⟩, h1.2⟩)
      have hd' : dem (C :: (Γ ++ Δ)) 1 b .consume ≤ Mode.mutate.rank := by
        have := dem_append_own hs Δ 0
        simp only [dem] at this
        rw [this]; exact hd
      refine (Own.iter hn' hz' hs' hd').cast ?_
      apply St.ext
      · funext j; simp only [St.frame]; split <;> simp_all
      · funext l; simp [St.frame, cl, pos_add, Bool.or_assoc]

/-- A closed value can be used in any context, from any state in which the
    locations it consumes are live; it adds exactly those locations. -/
theorem own_value {v U U'} (hval : Value v) (hvo : Own [] U v .consume U') :
    ∀ Γ W m, (∀ l, 0 < cl l v m → W.l l = false) →
      Own Γ W v m ⟨W.v, fun l => W.l l || pos (cl l v m)⟩ := by
  intro Γ W m hl
  cases hval with
  | unit => exact (Own.unit).cast (by apply St.ext <;> funext _ <;> simp [cl])
  | lit n => exact (Own.lit).cast (by apply St.ext <;> funext _ <;> simp [cl])
  | loc r =>
      refine (Own.loc (fun hm => hl r (by subst hm; simp [cl, useC]))).cast ?_
      apply St.ext
      · split <;> rfl
      · funext l
        simp only [cl]
        by_cases hm : m = .consume <;> by_cases hr : r = l
        · subst hm hr; simp [useC]
        · subst hm; simp [hr, Ne.symm hr]
        · subst hr; simp [useC, hm]
        · simp [hm, hr]
  | lam k A b =>
      have := own_frame (own_lam_mode hvo m) Γ W (fun i hi => by simp at hi) hl
      exact this.cast (by apply St.ext <;> funext _ <;> simp [St.frame])

/-! ### T1: kind widening -/

/-- **(T1) Kind widening.**  If `λ^k x:A. b` is well-typed and well-owned
    and `k ⊑ k'`, then `λ^{k'} x:A. b` is well-typed at `A →[k'] B` and
    leaves the same usage state. -/
theorem kind_widening {Γ S S' k k' A B b m}
    (ht : Typed Γ (.lam k A b) (.arr k A B)) (ho : Own Γ S (.lam k A b) m S') (hk : k ≤ k') :
    Typed Γ (.lam k' A b) (.arr k' A B) ∧ Own Γ S (.lam k' A b) m S' := by
  cases ht with
  | lam hb =>
      cases ho with
      | lam hob hd => exact ⟨.lam hb, .lam hob (Nat.le_trans hd (capmode_rank_mono hk))⟩

/-- A well-owned λ satisfies `required(λ) ⊑ k`. -/
theorem own_lam_reqKind {Γ S k A b m S'} (h : Own Γ S (.lam k A b) m S') :
    reqKind Γ (.lam k A b) ≤ k := by
  cases h with
  | lam _ hd => exact (sideCondition_iff Γ k A b).1 hd

/-! ### T2: the elaborator's coercion (η-expansion) -/

/-- The η-expansion `λ^{k'} y:A. x y` of a variable `x` (de Bruijn index `i`
    outside the new binder). -/
def etaVar (k' : Kind) (A : Ty) (i : Nat) : Term :=
  .lam k' A (.app (.var (i + 1)) (.var 0))

/-- **(T2) Coercion.**  For a variable `x : A →[k] B` and `k ⊑ k'`, the
    η-expansion `λ^{k'} y. x y` is well-typed at `A →[k'] B`, its required
    kind is exactly `k`, and it is well-owned whenever `x` is not moved: it
    moves `x` iff `k = fnOnce` (calling an `FnOnce` value consumes it). -/
theorem eta_coercion {Γ i k k' A B} (hl : lookup Γ i = some (.arr k A B)) (hk : k ≤ k') :
    Typed Γ (etaVar k' A i) (.arr k' A B) ∧
    reqKind Γ (etaVar k' A i) = k ∧
    ∀ S m, S.v i = false →
      Own Γ S (etaVar k' A i) m (if k = .fnOnce then S.moveV i else S) := by
  have hl' : lookup (A :: Γ) (i + 1) = some (.arr k A B) := hl
  have hdem : dem (A :: Γ) 1 (.app (.var (i + 1)) (.var 0)) .consume = (capmode k).rank := by
    simp only [dem, headMode, hl', effRank]
    cases k <;> simp [callmode, capmode, Ty.copy, Mode.rank]
  refine ⟨.lam (.app (.var hl') (.var rfl)), ?_, ?_⟩
  · simp only [etaVar, reqKind, hdem, kindOfRank_capmode]
  · intro S m hS
    have hhead : headMode (A :: Γ) (.var (i + 1)) = callmode k := headMode_var_arr hl'
    have h1 : Own (A :: Γ) S.push (.var (i + 1)) (headMode (A :: Γ) (.var (i + 1)))
        (if k = .fnOnce then S.push.moveV (i + 1) else S.push) := by
      rw [hhead]
      refine (Own.var hl' (fun _ => by simpa using hS)).cast ?_
      cases k <;> simp [callmode, Ty.copy]
    have h2 : ∀ T : St, T.v 0 = false →
        Own (A :: Γ) T (.var 0) .consume (if A.copy = false then T.moveV 0 else T) := by
      intro T hT
      exact (Own.var (A := A) rfl (fun _ => hT)).cast (by simp)
    have h3 := Own.app (m := .consume) h1 (h2 _ (by split <;> simp))
    have h4 := Own.lam (k := k') (m := m) h3 (by rw [hdem]; exact capmode_rank_mono hk)
    refine h4.cast ?_
    apply St.ext
    · funext j
      cases k <;> cases A.copy <;> simp [St.pop]
    · funext l
      cases k <;> cases A.copy <;> simp [St.pop]

/-- Conversely, the η-expansion is well-owned only at kinds `k' ⊒ k`: its
    required kind is exactly the kind of the coerced variable. -/
theorem eta_coercion_needs {Γ i k k' A B S m S'} (hl : lookup Γ i = some (.arr k A B))
    (h : Own Γ S (etaVar k' A i) m S') : k ≤ k' := by
  have hreq := own_lam_reqKind h
  have hk : reqKind Γ (etaVar k' A i) = k := by
    have hl' : lookup (A :: Γ) (i + 1) = some (.arr k A B) := hl
    simp only [etaVar, reqKind, dem, headMode, hl', effRank]
    cases k <;> simp [callmode, Ty.copy, Mode.rank, kindOfRank]
  simp only [etaVar] at hreq hk
  rw [hk] at hreq
  exact hreq

end LRL.Affine
