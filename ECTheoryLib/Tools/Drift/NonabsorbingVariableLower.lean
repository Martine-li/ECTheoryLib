import ECTheoryLib.Tools.Drift.VariableLower
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative

/-!
# Full-history variable lower drift before the first hit

Source counterpart: Lengler Theorem 2.4.1, printed page 113.
Descent is only required at a nonzero potential. Stopping preserves the
active-step ratio, initial potential and first hitting time.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Variable lower drift with descent required only before hitting zero.
The drift-ratio condition is retained on every active step, and the upper
drift premise is conditioned on the complete history. -/
theorem VariableDriftLowerBoundNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ) (c : ℝ)
    (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ t ω, X t ω∈S)
    (Descent : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → X (t+1) ω≤X t ω)
    (DriftPositive : ∀ x, smin≤x → 0<h x) (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (ConstantAtLeastOne : 1≤c)
    (DriftRatio : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → 1/c≤h (max (X (t+1) ω) smin)/h (X t ω))
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      (μ[fun u => X t u-X (t+1) u | F t]) ω≤h (X t ω)) :
    ENNReal.ofReal (ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω))/c)≤
      ExpectedZeroHittingTime μ X := by
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ j ω, 0≤X j ω := fun j ω => Nonnegative _ (Values j ω)
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Bound := VariableDriftLowerBound μ Y S smin h c (fun _ => AdaptedY.measurable)
    ZeroInS MinimumPositive StateLowerBound YValues (StopAtNonpositiveNonincreasing μ X Pointwise Descent)
    DriftPositive DriftMonotone ConstantAtLeastOne
    (StopAtNonpositiveActiveRelation μ X Pointwise (fun s r => 1/c≤h (max r smin)/h s) DriftRatio) (by
      intro j s _ Nonzero Positive
      exact StoppedStateDriftUpperBoundOfCondExp μ X F AdaptedX S Nonnegative Values h Drift j s Nonzero Positive)
  have Times : ExpectedZeroHittingTime μ Y=ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have Initial : Y 0=X 0 := funext (StopAtFirstHitInitial _ X)
  rwa [Times,Initial] at Bound

end
end ECTheoryLib.Tools.Drift
