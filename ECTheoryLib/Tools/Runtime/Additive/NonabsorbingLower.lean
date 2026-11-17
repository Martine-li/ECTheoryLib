import ECTheoryLib.Tools.Drift.NonabsorbingAdditive
import ECTheoryLib.Probability.Processes.FinitePotentialHistory
import ECTheoryLib.Probability.Processes.PathDriftBounds

/-! Additive runtime lower bounds from the original countable-state kernel.
The finite nonnegative potential range and global goal equivalence are
separate from almost-sure legality. No absorption or finite mean is assumed. -/
namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- A local upper bound on decrease yields a first-hitting runtime lower bound.
Zero is inserted into the scalar range internally;the goal need not be reachable. -/
theorem AdditiveRuntimeLowerBoundOfFiniteRangeNonabsorbing
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Goal Valid : State → Prop)
    (S : Finset ℝ) (Nonnegative : ∀ s ∈ S, 0 ≤ s) (Values : ∀ x, V x ∈ S)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      (∫ y, V x - V y ∂(Step x).toMeasure) ≤ Delta) :
    ENNReal.ofReal ((∫ x, V x ∂Initial.toMeasure) / Delta) ≤
      ExpectedHittingTime Step Goal Initial := by
  classical
  let S0 := insert 0 S
  have Nonnegative0 : ∀ s ∈ S0, 0 ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | Old
    · rw [Zero]
    · exact Nonnegative s Old
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → State) → ℝ := fun t Path => V (Path t)
  have Legal := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid
  have Bound := AdditiveDriftLowerBoundNonabsorbing μ X
    (Filtration.piLE (X := fun _ : ℕ => State)) (CountablePathPotentialAdapted V)
    S0 Delta (Finset.mem_insert_self _ _) Nonnegative0
    (fun _ Path => Finset.mem_insert_of_mem (Values (Path _))) PositiveDelta (by
      intro t
      filter_upwards [PathMeasureFinitePotentialConditionalDrift Step Initial V S Values t,Legal t]
        with Path Equal IsLegal
      intro Nonzero
      rw [Equal]
      exact LocalDrift (Path t) IsLegal Nonzero)
  rw [ExpectedHittingTimeEqExpectedZero Step Initial V Goal ZeroIffGoal]
  unfold ExpectedValue at Bound
  rw [PathMeasureInitialIntegral Step Initial V] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime

