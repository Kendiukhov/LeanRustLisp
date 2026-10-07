import LRL.Affine.Syntax
import LRL.Affine.Typing
import LRL.Affine.Ownership
import LRL.Affine.Substitution
import LRL.Affine.Semantics

/-!
# Affine core with function kinds — examples

Small closed programs that delimit the theorems:

* `barrier_needed`: without the repetition barrier, an iterator whose step
  function consumes a captured resource is well-typed and reaches a
  configuration that consumes a dead resource; `Own` rejects it.
* `subst_nonvalue_breaks_side_condition`: substitution of a non-value breaks
  the kind side condition (why T3 is stated for values).
* `read_after_consume`: a well-owned program can read a resource after it was
  consumed, through a closure that captured it by READ.  The judgment (like
  the kernel's) only rules out double consumption; the semantics therefore
  does not make reads of dead resources stuck.
* `reads_then_consumes`: a non-trivial well-owned program (an iterator whose
  step function reads a captured resource, followed by one consumption).
* `double_use_rejected`, `fnOnce_called_twice_rejected`: an owned argument
  used twice, and an `FnOnce` function value called twice, are rejected.
-/

namespace LRL.Affine

/-- A step function that consumes the captured resource `loc 0`. -/
def consumingStep : Term := .lam .fnOnce .unit (.consume (.loc 0))

/-- `iter 2 () consumingStep`. -/
def iterConsuming : Term := .iter (.lit 2) .unit consumingStep

theorem barrier_needed :
    Typed [] iterConsuming .unit ∧
    (∀ S m S', ¬ Own [] S iterConsuming m S') ∧
    ∃ tr σ t, Steps (fun _ => true) iterConsuming tr σ t ∧ ConsumesDead σ t := by
  have hs : Typed [] consumingStep (.arr .fnOnce .unit .unit) := .lam (.consume .loc)
  refine ⟨.iter .lit .unit hs, ?_, ?_⟩
  · intro S m S' h
    cases h with
    | iter _ _ _ hd => simp [dem, Mode.rank] at hd
  · let s := consumingStep
    have vs : Value s := .lam _ _ _
    refine ⟨[0], Store.kill (fun _ => true) 0, .consume (.loc 0), ?_, .here (by simp [Store.kill])⟩
    -- iter 2 () s ⟶ s (iter 1 () s) ⟶ s (s (iter 0 () s)) ⟶ s (s ()) ⟶ s (consume (loc 0))
    --   ⟶[0] s () ⟶ consume (loc 0)        (location 0 is now dead)
    have e1 : Step (fun _ => true) iterConsuming none (fun _ => true)
        (.app s (.iter (.lit 1) .unit s)) := .iterSucc .unit vs
    have e2 : Step (fun _ => true) (.app s (.iter (.lit 1) .unit s)) none (fun _ => true)
        (.app s (.app s (.iter (.lit 0) .unit s))) := .appR vs (.iterSucc .unit vs)
    have e3 : Step (fun _ => true) (.app s (.app s (.iter (.lit 0) .unit s))) none (fun _ => true)
        (.app s (.app s .unit)) := .appR vs (.appR vs (.iter0 .unit vs))
    have e4 : Step (fun _ => true) (.app s (.app s .unit)) none (fun _ => true)
        (.app s (.consume (.loc 0))) := .appR vs (.beta .unit)
    have e5 : Step (fun _ => true) (.app s (.consume (.loc 0))) (some 0)
        (Store.kill (fun _ => true) 0) (.app s .unit) := .appR vs (.consumeL rfl)
    have e6 : Step (Store.kill (fun _ => true) 0) (.app s .unit) none
        (Store.kill (fun _ => true) 0) (.consume (.loc 0)) := .beta .unit
    exact .step e1 (.step e2 (.step e3 (.step e4 (.step e5 (.step e6 .refl)))))

/-- Substituting the non-value `consume (loc 0)` for a Copy variable captured
    by an `fn` closure yields a closure that violates its side condition. -/
theorem subst_nonvalue_breaks_side_condition :
    (∃ S', Own [.unit] St.empty (.lam .fn .unit (.var 1)) .consume S') ∧
    Typed [] (.consume (.loc 0)) .unit ∧
    subst 0 (.consume (.loc 0)) (.lam .fn .unit (.var 1)) = .lam .fn .unit (.consume (.loc 0)) ∧
    ∀ S m S', ¬ Own [] S (.lam .fn .unit (.consume (.loc 0))) m S' := by
  refine ⟨⟨_, .lam (.var (A := .unit) rfl (fun _ => rfl)) ?_⟩, .consume .loc, rfl, ?_⟩
  · simp [dem, lookup, effRank, Ty.copy, capmode, Mode.rank]
  · intro S m S' h
    cases h with
    | lam _ hd => simp [dem, capmode, Mode.rank] at hd

/-- `(λ^{fnOnce} x:res. let _ = consume x in read (loc 0)) (loc 0)`. -/
def readAfterConsume : Term :=
  .app (.lam .fnOnce .res (.letE .unit (.consume (.var 0)) (.read (.loc 0)))) (.loc 0)

theorem read_after_consume :
    Typed [] readAfterConsume .nat ∧
    (∃ S', Own [] St.empty readAfterConsume .consume S') ∧
    Steps (fun _ => true) readAfterConsume [0] (Store.kill (fun _ => true) 0) (.read (.loc 0)) := by
  refine ⟨.app (.lam (.letE (.consume (.var rfl)) (.read .loc))) .loc, ?_, ?_⟩
  · refine ⟨_, .app (.lam (.letE (.consume (.var (A := .res) rfl (fun _ => rfl)))
      (.read (.loc (fun h => by cases h)))) ?_) (.loc (fun _ => ?_))⟩
    · simp [dem, Mode.rank, capmode]
    · rfl
  · have e1 : Step (fun _ => true) readAfterConsume none (fun _ => true)
        (.letE .unit (.consume (.loc 0)) (.read (.loc 0))) := .beta (.loc 0)
    have e2 : Step (fun _ => true) (.letE .unit (.consume (.loc 0)) (.read (.loc 0))) (some 0)
        (Store.kill (fun _ => true) 0) (.letE .unit .unit (.read (.loc 0))) := .letV (.consumeL rfl)
    have e3 : Step (Store.kill (fun _ => true) 0) (.letE .unit .unit (.read (.loc 0))) none
        (Store.kill (fun _ => true) 0) (.read (.loc 0)) := .letB .unit
    exact .step e1 (.step e2 (.step e3 .refl))

/-- `let x = loc 0 in let _ = iter 3 0 (λ^{fn} acc:nat. read x) in consume x`. -/
def readsThenConsumes : Term :=
  .letE .res (.loc 0)
    (.letE .nat (.iter (.lit 3) (.lit 0) (.lam .fn .nat (.read (.var 1))))
      (.consume (.var 1)))

theorem reads_then_consumes :
    Typed [] readsThenConsumes .unit ∧ ∃ S', Own [] St.empty readsThenConsumes .consume S' := by
  refine ⟨.letE .loc (.letE (.iter .lit .lit (.lam (.read (.var rfl)))) (.consume (.var rfl))), ?_⟩
  refine ⟨_, .letE (.loc (fun _ => rfl)) (.letE (.iter .lit .lit
    (.lam (.read (.var (A := .res) rfl (fun _ => rfl))) ?_) ?_)
    (.consume (.var (A := .res) rfl (fun _ => rfl))))⟩
  · simp [dem, lookup, effRank, Ty.copy, capmode, Mode.rank]
  · simp [dem, lookup, effRank, Ty.copy, Mode.rank]

/-- `λ^{fnOnce} x:res. let _ = consume x in consume x` is rejected: the
    second use of `x` is a use after move. -/
theorem double_use_rejected :
    ∀ S m S', ¬ Own [] S (.lam .fnOnce .res (.letE .unit (.consume (.var 0)) (.consume (.var 1)))) m S' := by
  intro S m S' h
  cases h with
  | lam hb _ =>
      cases hb with
      | letE hv hb' =>
          cases hv with
          | consume hv' =>
              cases hv' with
              | var hl _ =>
                  cases hb' with
                  | consume hc =>
                      cases hc with
                      | var _ hreq =>
                          have := hreq (by simp)
                          simp [lookup] at hl
                          subst hl
                          simp [Ty.copy] at this

/-- Calling a variable `f : unit →[fnOnce] unit` twice is rejected: an
    `FnOnce` call consumes the function value. -/
theorem fnOnce_called_twice_rejected :
    ∀ S m S', ¬ Own [] S
      (.lam .fnOnce (.arr .fnOnce .unit .unit) (.app (.var 0) (.app (.var 0) .unit))) m S' := by
  intro S m S' h
  cases h with
  | lam hb _ =>
      cases hb with
      | app hf ha =>
          simp only [headMode, lookup, callmode] at hf
          cases hf with
          | var hl _ =>
              cases ha with
              | app hf' _ =>
                  simp only [headMode, lookup, callmode] at hf'
                  cases hf' with
                  | var _ hreq =>
                      have := hreq (by simp)
                      simp [lookup] at hl
                      subst hl
                      simp [Ty.copy] at this

end LRL.Affine
