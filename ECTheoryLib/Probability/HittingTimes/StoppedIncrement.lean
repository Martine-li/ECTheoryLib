import ECTheoryLib.Probability.HittingTimes.StoppedHitting
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Active and stopped increments

The hitting step is retained. Later increments vanish in the stopped process.
Conditional observations need integrability only on the active region.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*}

/-- After the first hit, the stopped state itself remains unchanged. -/
theorem StopAtFirstHitFrozenStep {State : Type*} (Goal : State → Prop) (X : ℕ → Ω → State)
    (t : ℕ) (ω : Ω) (Reached : Goal (StopAtFirstHit Goal X t ω)) :
    StopAtFirstHit Goal X (t+1) ω=StopAtFirstHit Goal X t ω := by
  have Hit := (StopAtFirstHitGoalIff Goal X t ω).mp Reached
  have Next := Hit.trans (WithTop.coe_le_coe.mpr (Nat.le_succ t))
  change hittingAfter X {x | Goal x} 0 ω≤(t : WithTop ℕ) at Hit
  change hittingAfter X {x | Goal x} 0 ω≤((t+1 : ℕ) : WithTop ℕ) at Next
  change stoppedProcess X (hittingAfter X {x | Goal x} 0) (t+1) ω =
    stoppedProcess X (hittingAfter X {x | Goal x} 0) t ω
  rw [stoppedProcess_eq_of_ge (u := X) (i := t+1) Next,
    stoppedProcess_eq_of_ge (u := X) (i := t) Hit]

/-- The stopped increment is the original increment on the past-measurable
event of not having hit yet, and zero on its complement. -/
theorem StopAtFirstHitIncrement (X : ℕ → Ω → ℝ) (a : ℝ) (t : ℕ) (ω : Ω) :
    StopAtFirstHit (fun s : ℝ => s≤a) X (t+1) ω-StopAtFirstHit (fun s : ℝ => s≤a) X t ω =
      if a<StopAtFirstHit (fun s : ℝ => s≤a) X t ω then X (t+1) ω-X t ω else 0 := by
  by_cases Before : a<StopAtFirstHit (fun s : ℝ => s≤a) X t ω
  · rw [if_pos Before]
    have Equal := StopAtFirstHitStepBefore (fun s : ℝ => s≤a) X t ω (not_le_of_gt Before)
    rw [Equal.1,Equal.2]
  · rw [if_neg Before,StopAtFirstHitFrozenStep (fun s : ℝ => s≤a) X t ω (le_of_not_gt Before),sub_self]

/-- Ignore increments taken from the target region. The event selecting
active increments is measurable from the past; the increment itself need not be. -/
def ActiveIncrement (X : ℕ → Ω → ℝ) (a : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if a<X t ω then X (t+1) ω-X t ω else 0

theorem StopAtFirstHitIncrementActive (X : ℕ → Ω → ℝ) (a : ℝ) (t : ℕ) (ω : Ω) :
    StopAtFirstHit (fun s : ℝ => s≤a) X (t+1) ω-StopAtFirstHit (fun s : ℝ => s≤a) X t ω =
      if a<StopAtFirstHit (fun s : ℝ => s≤a) X t ω then ActiveIncrement X a t ω else 0 := by
  rw [StopAtFirstHitIncrement]
  by_cases Before : a<StopAtFirstHit (fun s : ℝ => s≤a) X t ω
  · rw [if_pos Before,if_pos Before]
    have Equal := StopAtFirstHitStepBefore (fun s : ℝ => s≤a) X t ω (not_le_of_gt Before)
    have Above : a<X t ω := by rwa [← Equal.1]
    rw [ActiveIncrement,if_pos Above]
  · simp only [if_neg Before]

/-- Conditional observations of stopped increments are obtained by a
past-measurable indicator. Integrability is needed only for active increments. -/
theorem StoppedIncrementConditional [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (AdaptedX : Adapted F X)
    (a : ℝ) (t : ℕ) (f : ℝ → ℝ)
    (IntegrableActive : Integrable (fun ω => f (ActiveIncrement X a t ω)) μ) :
    Integrable (fun ω => f (StopAtFirstHit (fun s : ℝ => s≤a) X (t+1) ω-
      StopAtFirstHit (fun s : ℝ => s≤a) X t ω)) μ ∧
      (μ[fun ω => f (StopAtFirstHit (fun s : ℝ => s≤a) X (t+1) ω-
        StopAtFirstHit (fun s : ℝ => s≤a) X t ω) | F t]) =ᵐ[μ]
      (fun ω => if a<StopAtFirstHit (fun s : ℝ => s≤a) X t ω then
        (μ[fun u => f (ActiveIncrement X a t u) | F t]) ω else f 0) := by
  let Y := StopAtFirstHit (fun s : ℝ => s≤a) X
  let B := {ω | a<Y t ω}
  let g := fun ω => f (ActiveIncrement X a t ω)
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have EventF : MeasurableSet[F t] B := measurableSet_lt measurable_const (AdaptedY t)
  have Event : MeasurableSet B := F.le t _ EventF
  have Equal : (fun ω => f (Y (t+1) ω-Y t ω)) =
      B.indicator g+Bᶜ.indicator (fun _ => f 0) := by
    funext ω
    change f (Y (t+1) ω-Y t ω)=B.indicator g ω+Bᶜ.indicator (fun _ => f 0) ω
    rw [StopAtFirstHitIncrementActive]
    by_cases Before : ω∈B
    · have Above : a<Y t ω := Before
      rw [if_pos Above,Set.indicator_of_mem Before,Set.indicator_of_notMem (by simpa using Before),add_zero]
    · have NotAbove : ¬a<Y t ω := Before
      rw [if_neg NotAbove,Set.indicator_of_notMem Before,Set.indicator_of_mem Before,zero_add]
  have LeftIntegrable := IntegrableActive.indicator Event
  have RightIntegrable := (integrable_const (f 0) (μ := μ)).indicator Event.compl
  have TotalIntegrable : Integrable (fun ω => f (Y (t+1) ω-Y t ω)) μ := by
    rw [Equal]
    exact LeftIntegrable.add RightIntegrable
  refine ⟨TotalIntegrable,?_⟩
  change (μ[fun ω => f (Y (t+1) ω-Y t ω) | F t]) =ᵐ[μ] _
  rw [Equal]
  have Add := condExp_add LeftIntegrable RightIntegrable (F t)
  have Left := condExp_indicator IntegrableActive EventF
  have Right := condExp_indicator (integrable_const (f 0) (μ := μ)) EventF.compl
  filter_upwards [Add,Left,Right] with ω Add Left Right
  change (μ[B.indicator g+Bᶜ.indicator (fun _ => f 0) | F t]) ω = _
  rw [Add]
  change (μ[B.indicator g | F t]) ω+(μ[Bᶜ.indicator (fun _ => f 0) | F t]) ω = _
  rw [Left,Right,condExp_const (F.le t)]
  by_cases Before : ω∈B
  · have Above : a<Y t ω := Before
    rw [Set.indicator_of_mem Before,Set.indicator_of_notMem (by simpa using Before),add_zero,if_pos Above]
  · have NotAbove : ¬a<Y t ω := Before
    rw [Set.indicator_of_notMem Before,Set.indicator_of_mem Before,zero_add,if_neg NotAbove]

end
end ECTheoryLib.Probability
