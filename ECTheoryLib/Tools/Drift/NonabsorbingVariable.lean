import ECTheoryLib.Tools.Drift.Variable
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative

/-!
# Variable drift without original zero absorption

Source counterpart: Lengler Theorem 2.3.3, printed page 100.
Complete-history and surviving-level conditioning are explicit.
The common finite potential range remains; the displayed integral form
requires positive initialization.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Variable drift with full-history conditioning and no absorption premise.
The zero-safe initial potential permits already successful initialization. -/
theorem VariableDriftUpperBoundNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ)
    (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ t ω, X t ω∈S)
    (DriftPositive : ∀ x, smin≤x → 0<h x) (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      h (X t ω)≤(μ[fun u => X t u-X (t+1) u | F t]) ω) :
    ExpectedZeroHittingTime μ X ≤
      ENNReal.ofReal (ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω))) := by
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ j ω, 0≤X j ω := fun j ω => Nonnegative _ (Values j ω)
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Bound := VariableDriftUpperBound μ Y S smin h (fun _ => AdaptedY.measurable)
    ZeroInS MinimumPositive StateLowerBound YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise)
    DriftPositive DriftMonotone (by
      intro j s _ Nonzero Positive
      exact StoppedStateDriftLowerBoundOfCondExp μ X F AdaptedX S Nonnegative Values h Drift j s Nonzero Positive)
  have Times : ExpectedZeroHittingTime μ Y=ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have Initial : Y 0=X 0 := funext (StopAtFirstHitInitial _ X)
  rwa [Times,Initial] at Bound

/-- The book's integral expression is used only for positive initialization. -/
theorem VariableDriftUpperBoundNonabsorbingOfPositiveInitial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ)
    (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ t ω, X t ω∈S)
    (DriftPositive : ∀ x, smin≤x → 0<h x) (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      h (X t ω)≤(μ[fun u => X t u-X (t+1) u | F t]) ω)
    (InitialNonzero : ∀ᵐ ω ∂μ, X 0 ω≠0) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      (smin/h smin+ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1/h x)) := by
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ j ω, 0≤X j ω := fun j ω => Nonnegative _ (Values j ω)
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Initial : Y 0=X 0 := funext (StopAtFirstHitInitial _ X)
  have Bound := VariableDriftUpperBoundOfPositiveInitial μ Y S smin h (fun _ => AdaptedY.measurable)
    ZeroInS MinimumPositive StateLowerBound YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise)
    DriftPositive DriftMonotone (by
      intro j s _ Nonzero Positive
      exact StoppedStateDriftLowerBoundOfCondExp μ X F AdaptedX S Nonnegative Values h Drift j s Nonzero Positive)
    (by rwa [Initial])
  have Times : ExpectedZeroHittingTime μ Y=ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  rwa [Times,Initial] at Bound

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Zero-safe variable drift using the original surviving-level event.
No original absorption or complete-history drift premise is required. -/
theorem VariableDriftUpperBoundOfSurvivingStateDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (SurvivingStateDrift : ∀ (t : ℕ) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} →
      h s ≤ EventConditionalExpectation μ (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s}) :
    ExpectedZeroHittingTime μ X ≤
      ENNReal.ofReal (ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω))) := by
  have Nonnegative : ∀ s ∈ S, 0 ≤ s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ t ω, 0 ≤ X t ω := fun t ω => Nonnegative _ (Values t ω)
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ 0) X
  have AdaptedX : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) X := by
    intro t
    change Measurable (X t)
    exact CoordinatesMeasurable t
  have AdaptedY : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) Y :=
    StopAtFirstHitAdapted X _ AdaptedX _ measurableSet_Iic
  have YValues : ∀ t ω, Y t ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have StoppedDrift : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent Y t s) → h s ≤ StateDrift μ Y t s := by
    intro t s InS Nonzero Positive
    have Event := StoppedNonzeroStateEventEqSurviving X Pointwise t s Nonzero
    change StateEvent Y t s = _ at Event
    rw [Event] at Positive
    rw [show StateDrift μ Y t s = _ from
      StoppedStateDriftEqSurvivingEventExpectation μ X CoordinatesMeasurable Pointwise t s Nonzero]
    exact SurvivingStateDrift t s InS Nonzero Positive
  have Bound := VariableDriftUpperBound μ Y S smin h (fun _ => AdaptedY.measurable)
    ZeroInS MinimumPositive StateLowerBound YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise)
    DriftPositive DriftMonotone StoppedDrift
  have Times : ExpectedZeroHittingTime μ Y = ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have Initial : Y 0 = X 0 := funext (StopAtFirstHitInitial _ X)
  rwa [Times, Initial] at Bound

/-- The displayed integral bound needs positive initialization; the drift
premise still conditions only on survival and the current original level. -/
theorem VariableDriftUpperBoundOfSurvivingStateDriftOfPositiveInitial
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (SurvivingStateDrift : ∀ (t : ℕ) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} →
      h s ≤ EventConditionalExpectation μ (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s})
    (InitialNonzero : ∀ᵐ ω ∂μ, X 0 ω ≠ 0) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      (smin / h smin + ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1 / h x)) := by
  have Nonnegative : ∀ s ∈ S, 0 ≤ s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ t ω, 0 ≤ X t ω := fun t ω => Nonnegative _ (Values t ω)
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ 0) X
  have AdaptedX : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) X := by
    intro t
    change Measurable (X t)
    exact CoordinatesMeasurable t
  have AdaptedY : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) Y :=
    StopAtFirstHitAdapted X _ AdaptedX _ measurableSet_Iic
  have YValues : ∀ t ω, Y t ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have StoppedDrift : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent Y t s) → h s ≤ StateDrift μ Y t s := by
    intro t s InS Nonzero Positive
    have Event := StoppedNonzeroStateEventEqSurviving X Pointwise t s Nonzero
    change StateEvent Y t s = _ at Event
    rw [Event] at Positive
    rw [show StateDrift μ Y t s = _ from
      StoppedStateDriftEqSurvivingEventExpectation μ X CoordinatesMeasurable Pointwise t s Nonzero]
    exact SurvivingStateDrift t s InS Nonzero Positive
  have Initial : Y 0 = X 0 := funext (StopAtFirstHitInitial _ X)
  have Bound := VariableDriftUpperBoundOfPositiveInitial μ Y S smin h
    (fun _ => AdaptedY.measurable) ZeroInS MinimumPositive StateLowerBound YValues
    (StopAtNonpositiveZeroAbsorbing μ X Pointwise) DriftPositive DriftMonotone StoppedDrift
    (by rwa [Initial])
  have Times : ExpectedZeroHittingTime μ Y = ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  rwa [Times, Initial] at Bound

end
end ECTheoryLib.Tools.Drift
