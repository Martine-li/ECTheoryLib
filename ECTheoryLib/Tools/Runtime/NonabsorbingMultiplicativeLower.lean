import ECTheoryLib.Tools.Drift.NonabsorbingMultiplicativeLower
import ECTheoryLib.Probability.Processes.FinitePotentialHistory
import ECTheoryLib.Probability.Processes.PathDriftBounds

/-!
# Rare-large-jump lower runtime bounds on countable state spaces

Actual transition probabilities, finite potential range and an almost-sure
legal-state invariant imply the complete-history premises.
-/

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Verify the complete-history rare-jump theorem from the actual kernel.
Only the potential range is finite; legal states need hold almost surely. -/
theorem MultiplicativeRuntimeLowerBoundOfFiniteRangeNonabsorbing
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Goal Valid : State → Prop)
    (S : Finset ℝ) (smin β δ : ℝ) (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ x, V x∈S)
    (ZeroIffGoal : ∀ x, V x=0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (BetaNonnegative : 0≤β) (BetaAtMostOne : β≤1) (DeltaPositive : 0<δ)
    (Descent : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → V x≠0 → V y≤V x)
    (LocalDrift : ∀ x, Valid x → V x≠0 → (∫ y, V x-V y ∂(Step x).toMeasure)≤δ*V x)
    (LocalLargeJump : ∀ x, Valid x → V x≠0 →
      (Step x).toMeasure.real {y | β*V x≤V x-V y}≤β*δ/(1+Real.log (V x/smin))) :
    ENNReal.ofReal (((1-β)/(1+β))*((∫ x, MultiplicativeDriftPotential smin 1 (V x) ∂Initial.toMeasure)/δ))≤
      ExpectedHittingTime Step Goal Initial := by
  classical
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → State) → ℝ := fun t Path => V (Path t)
  have AdaptedX : Adapted (Filtration.piLE (X := fun _ : ℕ => State)) X := CountablePathPotentialAdapted V
  have ValidOnPaths := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid
  have Bound := MultiplicativeDriftLowerBoundNonabsorbing μ X
    (Filtration.piLE (X := fun _ : ℕ => State)) AdaptedX S smin β δ
    ZeroInS MinimumPositive BetaNonnegative BetaAtMostOne DeltaPositive StateLowerBound
    (fun _ Path => Values (Path _)) (by
      intro t
      filter_upwards [PathMeasureFollowsTransition Step Initial
        (fun x y => Valid x → V x≠0 → V y≤V x) Descent t,ValidOnPaths t] with Path Desc Legal
      exact Desc Legal) (by
      intro t
      filter_upwards [PathMeasureFinitePotentialConditionalDrift Step Initial V S Values t,ValidOnPaths t] with Path Equal Legal
      intro Nonzero
      rw [Equal]
      exact LocalDrift (Path t) Legal Nonzero) (by
      intro t
      let f := fun x y => if β*V x≤V x-V y then (1 : ℝ) else 0
      have Formula : (RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ))=
          (fun Path => f (Path t) (Path (t+1))) := by
        funext Path
        simp [RelativeDecreaseEvent,Set.indicator_apply,f,X]
      have ObservationIntegrable : Integrable (fun Path => f (Path t) (Path (t+1))) μ := by
        rw [← Formula]
        exact (integrable_const 1).indicator (RelativeDecreaseEventMeasurable X β t (fun _ => AdaptedX.measurable))
      have Conditional := PathMeasureStateConditionalExpectationOfIntegrable Step Initial t f ObservationIntegrable
      rw [Formula]
      filter_upwards [Conditional,ValidOnPaths t] with Path Equal Legal
      intro Active
      rw [Equal]
      have Integral : (∫ y, f (Path t) y ∂(Step (Path t)).toMeasure)=
          (Step (Path t)).toMeasure.real {y | β*V (Path t)≤V (Path t)-V y} := by
        change (∫ y, ({y | β*V (Path t)≤V (Path t)-V y}).indicator (fun _ => (1 : ℝ)) y
          ∂(Step (Path t)).toMeasure)=_
        rw [integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
      rw [Integral]
      exact LocalLargeJump (Path t) Legal Active)
  rw [ExpectedHittingTimeEqExpectedZero Step Initial V Goal ZeroIffGoal]
  unfold ExpectedValue at Bound
  rw [PathMeasureInitialIntegral Step Initial (fun x => MultiplicativeDriftPotential smin 1 (V x))] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime
