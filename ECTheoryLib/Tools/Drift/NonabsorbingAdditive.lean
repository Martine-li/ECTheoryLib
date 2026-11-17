import ECTheoryLib.Tools.Drift.Additive
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative

/-!
# Additive bounds without original zero absorption

Complete-history drift and survival-and-current-level event averages give
upper and lower bounds by the established stopped-process theorems.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Safe nonabsorbing additive drift: the lower bound is conditioned on
the complete filtration. Finite nonnegative range is retained. -/
theorem AdditiveDriftUpperBoundNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (Delta : ℝ)
    (ZeroInS : 0∈S) (Nonnegative : ∀ s∈S, 0≤s) (Values : ∀ t ω, X t ω∈S)
    (PositiveDelta : 0<Delta)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      Delta≤(μ[fun u => X t u-X (t+1) u | F t]) ω) :
    ExpectedZeroHittingTime μ X≤ENNReal.ofReal (ExpectedValue μ (X 0)/Delta) := by
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have Pointwise : ∀ t ω, 0≤X t ω := fun t ω => Nonnegative _ (Values t ω)
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ t ω, Y t ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Bound := AdditiveDriftUpperBound μ Y S Delta (fun _ => AdaptedY.measurable)
    ZeroInS Nonnegative YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise) PositiveDelta (by
      intro t s _ Nonzero Positive
      exact StoppedStateDriftLowerBoundOfCondExp μ X F AdaptedX S Nonnegative Values
        (fun _ => Delta) Drift t s Nonzero Positive)
  have TimeEqual : ExpectedZeroHittingTime μ Y=ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have InitialEqual : ExpectedValue μ (Y 0)=ExpectedValue μ (X 0) := by
    apply integral_congr_ae
    exact ae_of_all _ (StopAtFirstHitInitial _ X)
  rwa [TimeEqual,InitialEqual] at Bound

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The nonabsorbing additive lower bound uses a complete-history drift
upper bound and a common finite nonnegative range. Infinite expectation is
allowed and is never assumed away. -/
theorem AdditiveDriftLowerBoundNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (Delta : ℝ)
    (ZeroInS : 0∈S) (Nonnegative : ∀ s∈S, 0≤s) (Values : ∀ t ω, X t ω∈S)
    (PositiveDelta : 0<Delta)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      (μ[fun u => X t u-X (t+1) u | F t]) ω≤Delta) :
    ENNReal.ofReal (ExpectedValue μ (X 0)/Delta)≤ExpectedZeroHittingTime μ X := by
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have Pointwise : ∀ t ω, 0≤X t ω := fun t ω => Nonnegative _ (Values t ω)
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ t ω, Y t ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Bound := AdditiveDriftLowerBound μ Y S Delta (fun _ => AdaptedY.measurable)
    ZeroInS Nonnegative YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise) PositiveDelta (by
      intro t s _ Nonzero Positive
      exact StoppedStateDriftUpperBoundOfCondExp μ X F AdaptedX S Nonnegative Values
        (fun _ => Delta) Drift t s Nonzero Positive)
  have TimeEqual : ExpectedZeroHittingTime μ Y=ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have InitialEqual : ExpectedValue μ (Y 0)=ExpectedValue μ (X 0) := by
    apply integral_congr_ae
    exact ae_of_all _ (StopAtFirstHitInitial _ X)
  rwa [TimeEqual,InitialEqual] at Bound

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Additive upper bound using only survival-and-current-level conditional
decrease. The original process may leave zero; initialization may be random. -/
theorem AdditiveDriftUpperBoundOfSurvivingStateDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S) (Nonnegative : ∀ s ∈ S, 0 ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (PositiveDelta : 0 < Delta)
    (SurvivingStateDrift : ∀ (t : ℕ) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} →
      Delta ≤ EventConditionalExpectation μ (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s}) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal (ExpectedValue μ (X 0) / Delta) := by
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ 0) X
  have Pointwise : ∀ t ω, 0 ≤ X t ω := fun t ω => Nonnegative _ (Values t ω)
  have AdaptedX : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) X := by
    intro t
    change Measurable (X t)
    exact CoordinatesMeasurable t
  have AdaptedY : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) Y :=
    StopAtFirstHitAdapted X _ AdaptedX _ measurableSet_Iic
  have YValues : ∀ t ω, Y t ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have StoppedDrift : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent Y t s) → Delta ≤ StateDrift μ Y t s := by
    intro t s InS Nonzero Positive
    have Event := StoppedNonzeroStateEventEqSurviving X Pointwise t s Nonzero
    change StateEvent Y t s = _ at Event
    rw [Event] at Positive
    rw [show StateDrift μ Y t s = _ from
      StoppedStateDriftEqSurvivingEventExpectation μ X CoordinatesMeasurable Pointwise t s Nonzero]
    exact SurvivingStateDrift t s InS Nonzero Positive
  have Bound := AdditiveDriftUpperBound μ Y S Delta (fun _ => AdaptedY.measurable)
    ZeroInS Nonnegative YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise) PositiveDelta StoppedDrift
  have Times : ExpectedZeroHittingTime μ Y = ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have Initial : ExpectedValue μ (Y 0) = ExpectedValue μ (X 0) :=
    integral_congr_ae (ae_of_all _ (StopAtFirstHitInitial _ X))
  rwa [Times, Initial] at Bound

/-- Additive lower bound with a ceiling on survival-and-current-level drift.
No finite expected time or original zero absorption is assumed. -/
theorem AdditiveDriftLowerBoundOfSurvivingStateDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S) (Nonnegative : ∀ s ∈ S, 0 ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (PositiveDelta : 0 < Delta)
    (SurvivingStateDrift : ∀ (t : ℕ) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} →
      EventConditionalExpectation μ (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} ≤ Delta) :
    ENNReal.ofReal (ExpectedValue μ (X 0) / Delta) ≤ ExpectedZeroHittingTime μ X := by
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ 0) X
  have Pointwise : ∀ t ω, 0 ≤ X t ω := fun t ω => Nonnegative _ (Values t ω)
  have AdaptedX : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) X := by
    intro t
    change Measurable (X t)
    exact CoordinatesMeasurable t
  have AdaptedY : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) Y :=
    StopAtFirstHitAdapted X _ AdaptedX _ measurableSet_Iic
  have YValues : ∀ t ω, Y t ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have StoppedDrift : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent Y t s) → StateDrift μ Y t s ≤ Delta := by
    intro t s InS Nonzero Positive
    have Event := StoppedNonzeroStateEventEqSurviving X Pointwise t s Nonzero
    change StateEvent Y t s = _ at Event
    rw [Event] at Positive
    rw [show StateDrift μ Y t s = _ from
      StoppedStateDriftEqSurvivingEventExpectation μ X CoordinatesMeasurable Pointwise t s Nonzero]
    exact SurvivingStateDrift t s InS Nonzero Positive
  have Bound := AdditiveDriftLowerBound μ Y S Delta (fun _ => AdaptedY.measurable)
    ZeroInS Nonnegative YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise) PositiveDelta StoppedDrift
  have Times : ExpectedZeroHittingTime μ Y = ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have Initial : ExpectedValue μ (Y 0) = ExpectedValue μ (X 0) :=
    integral_congr_ae (ae_of_all _ (StopAtFirstHitInitial _ X))
  rwa [Times, Initial] at Bound

end
end ECTheoryLib.Tools.Drift
