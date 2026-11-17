import ECTheoryLib.Tools.Drift.MultiplicativeLower
import ECTheoryLib.Probability.HittingTimes.StoppedObservations

/-!
# Full-history multiplicative lower drift without absorption

Source counterpart: Lengler Theorem 2.4.3, printed pages 114-115.
Retain mean drift, closed large-jump probability and descent at positive
states. The initial potential is zero-safe; no finite runtime is assumed.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Multiplicative lower drift with full-history mean and large-jump bounds.
Descent is only needed at positive states; post-success restarts are allowed. -/
theorem MultiplicativeDriftLowerBoundNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin β δ : ℝ)
    (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (BetaNonnegative : 0≤β) (BetaAtMostOne : β≤1) (DeltaPositive : 0<δ)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ t ω, X t ω∈S)
    (Descent : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → X (t+1) ω≤X t ω)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      (μ[fun u => X t u-X (t+1) u | F t]) ω≤δ*X t ω)
    (LargeJump : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      (μ[(RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)) | F t]) ω≤
        β*δ/(1+Real.log (X t ω/smin))) :
    ENNReal.ofReal (((1-β)/(1+β))*(ExpectedValue μ
      (fun ω => MultiplicativeDriftPotential smin 1 (X 0 ω))/δ))≤ExpectedZeroHittingTime μ X := by
  classical
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ t ω, 0≤X t ω := fun t ω => Nonnegative _ (Values t ω)
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ t ω, Y t ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Bound := MultiplicativeDriftLowerBound μ Y S smin β δ (fun _ => AdaptedY.measurable)
    ZeroInS MinimumPositive BetaNonnegative BetaAtMostOne DeltaPositive StateLowerBound YValues
    (StopAtNonpositiveNonincreasing μ X Pointwise Descent) (by
      intro t s _ Nonzero Positive
      exact StoppedStateDriftUpperBoundOfCondExp μ X F AdaptedX S Nonnegative Values
        (fun s => δ*s) Drift t s Nonzero Positive) (by
      intro t s _ Nonzero Positive
      have IndicatorIntegrable : Integrable ((RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ))) μ :=
        (integrable_const 1).indicator (RelativeDecreaseEventMeasurable X β t (fun _ => AdaptedX.measurable))
      have Formula (Z : ℕ → Ω → ℝ) : (RelativeDecreaseEvent Z β t).indicator (fun _ => (1 : ℝ))=
          (fun ω => if β*Z t ω≤Z t ω-Z (t+1) ω then 1 else 0) := by
        funext ω
        simp [RelativeDecreaseEvent,Set.indicator_apply]
      have Large := LargeJump t
      rw [Formula] at IndicatorIntegrable Large
      have Transfer := StoppedStateObservationUpperBoundOfCondExp μ X F AdaptedX Pointwise
        (fun s r => if β*s≤s-r then 1 else 0) (fun s => β*δ/(1+Real.log (s/smin))) t
        IndicatorIntegrable Large s Nonzero Positive
      rw [Formula]
      exact Transfer)
  have Times : ExpectedZeroHittingTime μ Y=ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have Initial : Y 0=X 0 := funext (StopAtFirstHitInitial _ X)
  rwa [Times,Initial] at Bound

end
end ECTheoryLib.Tools.Drift
