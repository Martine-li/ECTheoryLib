import ECTheoryLib.Tools.Runtime.LocalDrift

/-!
# Two-phase runtime certificates

Before entering an invariant region, use a nonnegative unit-drift potential plus
a uniform budget for the second phase. Inside the region, switch to a second
unit-drift potential bounded by that budget. Crossing the boundary cannot create
an unpaid upward jump, so the combined potential has unit drift until the goal.

This is a composition rule for local progress certificates on the actual kernel.
It requires no restart assumption at a random time and does not assert a general
black-box theorem combining arbitrary stopping-time expectations. Both phases
can share the same evolving full state, with arbitrary valid initialization.
The final result uses the existing actual-path extended hitting-time semantics.
-/
namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {State : Type*} [MeasurableSpace State]

/-- Local certificates for reaching a persistent second-phase region and then
reaching the goal. The first potential need not vanish in the region: it is
discarded there. The second potential must characterize the goal globally.
Budget positivity ensures the combined potential cannot vanish outside the region. -/
structure TwoPhaseCertificate (Step : Transition State) (Goal Valid Region : State → Prop) where
  /-- Remaining-work potential used before the region is reached. -/
  First : State → ℝ
  /-- Remaining-work potential used after the region is reached. -/
  Second : State → ℝ
  /-- Uniform upper bound on Second inside the region. -/
  Budget : ℝ
  BudgetPositive : 0 < Budget
  FirstNonnegative : ∀ x, 0 ≤ First x
  SecondNonnegative : ∀ x, 0 ≤ Second x
  SecondZeroIffGoal : ∀ x, Second x = 0 ↔ Goal x
  GoalInRegion : ∀ x, Goal x → Region x
  SecondBound : ∀ x, Region x → Second x ≤ Budget
  PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y
  PreservesRegion : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Region x → Region y
  PreservesGoal : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Goal x → Goal y
  /-- Unit progress outside the region, including transitions crossing into it. -/
  FirstDrift : ∀ x, Valid x → ¬ Region x → 1 ≤ ∫ y, First x - First y ∂(Step x).toMeasure
  /-- Unit progress in the region until the final goal. -/
  SecondDrift : ∀ x, Valid x → Region x → ¬ Goal x →
    1 ≤ ∫ y, Second x - Second y ∂(Step x).toMeasure

namespace TwoPhaseCertificate
variable {Step : Transition State} {Goal Valid Region : State → Prop}

/-- Before entry, reserve the whole second-phase budget; after entry, charge
only the actual second-phase potential. -/
def Potential (C : TwoPhaseCertificate Step Goal Valid Region) (x : State) : ℝ := by
  classical
  exact if Region x then C.Second x else C.First x + C.Budget

/-- Both branches of the combined potential are nonnegative. -/
theorem PotentialNonnegative (C : TwoPhaseCertificate Step Goal Valid Region) (x : State) :
    0 ≤ C.Potential x := by
  classical
  unfold Potential
  split_ifs
  · exact C.SecondNonnegative x
  · exact add_nonneg (C.FirstNonnegative x) C.BudgetPositive.le

/-- The combined potential vanishes exactly at the final goal, not merely on
entry into the second-phase region. -/
theorem PotentialZeroIffGoal (C : TwoPhaseCertificate Step Goal Valid Region) (x : State) :
    C.Potential x = 0 ↔ Goal x := by
  classical
  unfold Potential
  by_cases Inside : Region x
  · rw [if_pos Inside]
    exact C.SecondZeroIffGoal x
  · rw [if_neg Inside]
    have Positive : 0 < C.First x + C.Budget :=
      add_pos_of_nonneg_of_pos (C.FirstNonnegative x) C.BudgetPositive
    constructor
    · intro Zero
      exact False.elim (Positive.ne' Zero)
    · intro AtGoal
      exact False.elim (Inside (C.GoalInRegion x AtGoal))

/-- The reserved budget covers every possible boundary crossing. -/
theorem PotentialLeBudget (C : TwoPhaseCertificate Step Goal Valid Region) (x : State) :
    C.Potential x ≤ C.First x + C.Budget := by
  classical
  unfold Potential
  split_ifs with Inside
  · exact (C.SecondBound x Inside).trans
      (le_add_of_nonneg_left (C.FirstNonnegative x))
  · exact le_rfl

variable [Fintype State] [MeasurableSingletonClass State]

/-- Local unit drift composes across the phase boundary. In the first phase,
the second-phase budget bounds the new potential; in the second, region
preservation identifies the successor potential with Second almost surely. -/
theorem LocalDrift (C : TwoPhaseCertificate Step Goal Valid Region)
    (x : State) (IsValid : Valid x) (Nonzero : C.Potential x ≠ 0) :
    1 ≤ ∫ y, C.Potential x - C.Potential y ∂(Step x).toMeasure := by
  classical
  by_cases Inside : Region x
  · have NotGoal : ¬ Goal x := fun AtGoal => Nonzero ((C.PotentialZeroIffGoal x).mpr AtGoal)
    have SameIntegral : (∫ y, C.Potential x - C.Potential y ∂(Step x).toMeasure) =
        ∫ y, C.Second x - C.Second y ∂(Step x).toMeasure := by
      apply integral_congr_ae
      filter_upwards [C.PreservesRegion x] with y Preserved
      simp only [Potential, if_pos Inside, if_pos (Preserved IsValid Inside)]
    rw [SameIntegral]
    exact C.SecondDrift x IsValid Inside NotGoal
  · apply (C.FirstDrift x IsValid Inside).trans
    apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
    intro y
    have SuccessorBound := C.PotentialLeBudget y
    have Current : C.Potential x = C.First x + C.Budget := by
      simp only [Potential, if_neg Inside]
    rw [Current]
    linarith

/-- Expected iterations to the final goal are bounded by the initial mean of
the combined certificate. This covers arbitrary valid initialization, including
states already inside the second phase or already at the final goal. -/
theorem RuntimeUpperBound (C : TwoPhaseCertificate Step Goal Valid Region)
    (Initial : PMF State) (InitiallyValid : ∀ᵐ x ∂Initial.toMeasure, Valid x) :
    ExpectedHittingTime Step Goal Initial ≤ ENNReal.ofReal
      (∫ x, C.Potential x ∂Initial.toMeasure) := by
  have Bound := AdditiveRuntimeUpperBound Step Initial C.Potential Goal Valid
    C.PotentialNonnegative C.PotentialZeroIffGoal InitiallyValid C.PreservesValid
    (by
      intro x
      filter_upwards [C.PreservesGoal x] with y Preserves
      intro IsValid Zero
      exact (C.PotentialZeroIffGoal y).mpr (Preserves IsValid ((C.PotentialZeroIffGoal x).mp Zero)))
    1 (by norm_num) C.LocalDrift
  simpa only [div_one] using Bound

/-- If the first-phase potential is uniformly at most A, the expected total
time is at most A + Budget. Neither finiteness nor a random-time restart law
is assumed; the bound follows from the composed local certificate. -/
theorem RuntimeUniformBound (C : TwoPhaseCertificate Step Goal Valid Region)
    (Initial : PMF State) (InitiallyValid : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (A : ℝ) (FirstBound : ∀ x, C.First x ≤ A) :
    ExpectedHittingTime Step Goal Initial ≤ ENNReal.ofReal (A + C.Budget) := by
  apply (C.RuntimeUpperBound Initial InitiallyValid).trans
  apply ENNReal.ofReal_le_ofReal
  have Bound := integral_mono (μ := Initial.toMeasure)
    (Integrable.of_finite (f := C.Potential)) (integrable_const (A + C.Budget))
    (fun x => (C.PotentialLeBudget x).trans (add_le_add (FirstBound x) le_rfl))
  simpa only [integral_const, probReal_univ, one_smul] using Bound

end TwoPhaseCertificate
end
end ECTheoryLib.Tools.Runtime
