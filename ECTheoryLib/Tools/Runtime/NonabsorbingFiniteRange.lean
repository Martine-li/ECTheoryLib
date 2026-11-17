import ECTheoryLib.Tools.Drift.NonabsorbingMultiplicative
import ECTheoryLib.Probability.Processes.FinitePotentialHistory
import ECTheoryLib.Probability.Processes.PathDriftBounds

/-!
# Nonabsorbing runtime bounds from local drift on countable states

Finite potential range and an almost-sure legal-state invariant suffice.
The actual kernel and initialization are used throughout.
-/

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Variable drift on actual countable-state paths, with finite potential range
and an almost-sure legal-state invariant. No target-absorption premise is needed. -/
theorem VariableRuntimeUpperBoundOfFiniteRangeNonabsorbing
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Goal Valid : State → Prop)
    (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ) (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ x, V x∈S)
    (ZeroIffGoal : ∀ x, V x=0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (DriftPositive : ∀ x, smin≤x → 0<h x) (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (LocalDrift : ∀ x, Valid x → V x≠0 → h (V x)≤∫ y, V x-V y ∂(Step x).toMeasure) :
    ExpectedHittingTime Step Goal Initial ≤
      ENNReal.ofReal (∫ x, VariableDriftPotential smin h (V x) ∂Initial.toMeasure) := by
  have ValidOnPaths := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid
  have Bound := VariableDriftUpperBoundNonabsorbing (PathMeasure Step Initial) (fun t Path => V (Path t))
    (Filtration.piLE (X := fun _ : ℕ => State)) (CountablePathPotentialAdapted V)
    S smin h ZeroInS MinimumPositive StateLowerBound (fun _ Path => Values (Path _)) DriftPositive DriftMonotone (by
      intro t
      filter_upwards [PathMeasureFinitePotentialConditionalDrift Step Initial V S Values t,ValidOnPaths t] with Path Equal Legal
      intro Nonzero
      rw [Equal]
      exact LocalDrift (Path t) Legal Nonzero)
  rw [ExpectedHittingTimeEqExpectedZero Step Initial V Goal ZeroIffGoal]
  change ExpectedZeroHittingTime (PathMeasure Step Initial) (fun t Path => V (Path t)) ≤
    ENNReal.ofReal (∫ x, VariableDriftPotential smin h (V x) ∂Initial.toMeasure)
  unfold ExpectedValue at Bound
  rw [PathMeasureInitialIntegral Step Initial (fun x => VariableDriftPotential smin h (V x))] at Bound
  exact Bound

/-- The linear-drift specialization yields the usual zero-safe logarithmic bound. -/
theorem MultiplicativeRuntimeUpperBoundOfFiniteRangeNonabsorbing
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Goal Valid : State → Prop)
    (S : Finset ℝ) (smin Delta : ℝ) (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ x, V x∈S)
    (ZeroIffGoal : ∀ x, V x=0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (PositiveDelta : 0<Delta)
    (LocalDrift : ∀ x, Valid x → V x≠0 → Delta*V x≤∫ y, V x-V y ∂(Step x).toMeasure) :
    ExpectedHittingTime Step Goal Initial ≤
      ENNReal.ofReal (∫ x, MultiplicativeDriftPotential smin Delta (V x) ∂Initial.toMeasure) := by
  have Bound := VariableRuntimeUpperBoundOfFiniteRangeNonabsorbing Step Initial V Goal Valid S smin (fun s => Delta*s)
    ZeroInS MinimumPositive StateLowerBound Values ZeroIffGoal Initially PreservesValid
    (fun x Lower => mul_pos PositiveDelta (MinimumPositive.trans_le Lower))
    (fun _ _ _ _ Before => mul_le_mul_of_nonneg_left Before PositiveDelta.le) LocalDrift
  have Equal : (fun x => VariableDriftPotential smin (fun s => Delta*s) (V x)) =
      (fun x => MultiplicativeDriftPotential smin Delta (V x)) := by
    funext x
    exact LinearVariableDriftPotential smin Delta _ MinimumPositive PositiveDelta (StateLowerBound _ (Values x))
  rwa [Equal] at Bound

end
end ECTheoryLib.Tools.Runtime
