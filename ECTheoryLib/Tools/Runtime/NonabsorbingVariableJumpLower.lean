import ECTheoryLib.Tools.Drift.NonabsorbingVariableJumpLower
import ECTheoryLib.Probability.Processes.FinitePotentialHistory
import ECTheoryLib.Probability.Processes.PathDriftBounds

/-!
# Actual-kernel jump-floor runtime lower bound

Countable states, finite potential range and an almost-sure legal-state
invariant suffice. No goal-absorption premise is needed.
-/

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Actual-kernel jump-floor lower bound; the algorithm may leave the goal
after its first success. The potential still has a common finite range. -/
theorem VariableRuntimeLowerBoundOfJumpFloorNonabsorbing
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Goal Valid : State → Prop)
    (S : Finset ℝ) (smin : ℝ) (h ξ : ℝ → ℝ) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ x, V x∈S)
    (ZeroIffGoal : ∀ x, V x=0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (DriftPositive : ∀ x, 0≤x → 0<h x) (DriftMonotone : MonotoneOn h (Set.Ici 0))
    (FloorNonnegative : ∀ s∈S, s≠0 → 0≤ξ s)
    (Descent : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → V x≠0 → V y≤V x)
    (JumpFloor : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → V x≠0 → ξ (V x)≤V y)
    (LocalDrift : ∀ x, Valid x → V x≠0 → (∫ y, V x-V y ∂(Step x).toMeasure)≤h (ξ (V x))) :
    ENNReal.ofReal (∫ x, VariableDriftPotential smin h (V x) ∂Initial.toMeasure)≤
      ExpectedHittingTime Step Goal Initial := by
  have ValidOnPaths := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid
  have Bound := VariableDriftLowerBoundOfJumpFloorNonabsorbing (PathMeasure Step Initial)
    (fun t Path => V (Path t)) (Filtration.piLE (X := fun _ : ℕ => State))
    (CountablePathPotentialAdapted V) S smin h ξ MinimumPositive StateLowerBound
    (fun _ Path => Values (Path _)) (by
      intro t
      filter_upwards [PathMeasureFollowsTransition Step Initial
        (fun x y => Valid x → V x≠0 → V y≤V x) Descent t,ValidOnPaths t] with Path Desc Legal
      exact Desc Legal) DriftPositive DriftMonotone FloorNonnegative (by
      intro t
      filter_upwards [PathMeasureFollowsTransition Step Initial
        (fun x y => Valid x → V x≠0 → ξ (V x)≤V y) JumpFloor t,ValidOnPaths t] with Path Floor Legal
      exact Floor Legal) (by
      intro t
      filter_upwards [PathMeasureFinitePotentialConditionalDrift Step Initial V S Values t,ValidOnPaths t] with Path Equal Legal
      intro Nonzero
      rw [Equal]
      exact LocalDrift (Path t) Legal Nonzero)
  rw [ExpectedHittingTimeEqExpectedZero Step Initial V Goal ZeroIffGoal]
  unfold ExpectedValue at Bound
  rw [PathMeasureInitialIntegral Step Initial (fun x => VariableDriftPotential smin h (V x))] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime
