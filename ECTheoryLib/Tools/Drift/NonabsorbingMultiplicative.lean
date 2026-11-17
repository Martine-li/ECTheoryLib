import ECTheoryLib.Tools.Drift.NonabsorbingVariable
import ECTheoryLib.Tools.Drift.Multiplicative

/-!
# Multiplicative expectation without original absorption

Source counterpart: Lengler Theorem 2.3.11, printed page 110.
Full-history and surviving-level premises are explicit. Both reuse the
existing linear variable-drift potential identity. The positive-initial
logarithmic and zero-safe versions stay distinct.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Nonabsorbing multiplicative expectation bound, derived from variable drift. -/
theorem MultiplicativeDriftUpperBoundNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin Delta : ℝ)
    (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ t ω, X t ω∈S)
    (PositiveDelta : 0<Delta)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      Delta*X t ω≤(μ[fun u => X t u-X (t+1) u | F t]) ω) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      (ExpectedValue μ (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω))) := by
  have Bound := VariableDriftUpperBoundNonabsorbing μ X F AdaptedX S smin (fun s => Delta*s)
    ZeroInS MinimumPositive StateLowerBound Values
    (fun x Lower => mul_pos PositiveDelta (MinimumPositive.trans_le Lower))
    (fun _ _ _ _ Before => mul_le_mul_of_nonneg_left Before PositiveDelta.le) Drift
  have Potentials : (fun ω => VariableDriftPotential smin (fun s => Delta*s) (X 0 ω)) =
      (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) := by
    funext ω
    exact LinearVariableDriftPotential smin Delta _ MinimumPositive PositiveDelta (StateLowerBound _ (Values 0 ω))
  rwa [Potentials] at Bound

/-- The displayed logarithmic formula retains a positive-initialization premise. -/
theorem MultiplicativeDriftUpperBoundNonabsorbingOfPositiveInitial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin Delta : ℝ)
    (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ t ω, X t ω∈S)
    (PositiveDelta : 0<Delta)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      Delta*X t ω≤(μ[fun u => X t u-X (t+1) u | F t]) ω)
    (InitialNonzero : ∀ᵐ ω ∂μ, X 0 ω≠0) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      ((1+ExpectedValue μ (fun ω => Real.log (X 0 ω/smin)))/Delta) := by
  have Bound := MultiplicativeDriftUpperBoundNonabsorbing μ X F AdaptedX S smin Delta ZeroInS
    MinimumPositive StateLowerBound Values PositiveDelta Drift
  have LogIntegrable : Integrable (fun ω => Real.log (X 0 ω/smin)) μ :=
    FiniteStateCompositionIntegrable μ (X 0) S (fun s => Real.log (s/smin)) AdaptedX.measurable (Values 0)
  have Formula : (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) =ᵐ[μ]
      (fun ω => (1+Real.log (X 0 ω/smin))/Delta) := by
    filter_upwards [InitialNonzero] with ω Nonzero
    exact if_neg Nonzero
  have Means : ExpectedValue μ (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) =
      (1+ExpectedValue μ (fun ω => Real.log (X 0 ω/smin)))/Delta := by
    unfold ExpectedValue
    rw [integral_congr_ae Formula,integral_div,integral_add (integrable_const 1) LogIntegrable,
      integral_const,probReal_univ,one_smul]
  rwa [Means] at Bound

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Multiplicative expected-time bound conditional on original survival and
the current level. The zero-safe potential retains initial success mass. -/
theorem MultiplicativeDriftUpperBoundOfSurvivingStateDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (PositiveDelta : 0 < Delta)
    (SurvivingStateDrift : ∀ (t : ℕ) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} →
      Delta * s ≤ EventConditionalExpectation μ (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s}) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      (ExpectedValue μ (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω))) := by
  have Bound := VariableDriftUpperBoundOfSurvivingStateDrift μ X S smin
    (fun s => Delta * s) CoordinatesMeasurable ZeroInS MinimumPositive StateLowerBound Values
    (fun x Lower => mul_pos PositiveDelta (MinimumPositive.trans_le Lower))
    (fun _ _ _ _ Before => mul_le_mul_of_nonneg_left Before PositiveDelta.le) SurvivingStateDrift
  have Potentials : (fun ω => VariableDriftPotential smin (fun s => Delta * s) (X 0 ω)) =
      (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) := by
    funext ω
    exact LinearVariableDriftPotential smin Delta _ MinimumPositive PositiveDelta
      (StateLowerBound _ (Values 0 ω))
  rwa [Potentials] at Bound

/-- The displayed logarithmic expectation separately requires almost sure
positive initialization; no complete-history drift premise is inserted. -/
theorem MultiplicativeDriftUpperBoundOfSurvivingStateDriftOfPositiveInitial
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (PositiveDelta : 0 < Delta)
    (SurvivingStateDrift : ∀ (t : ℕ) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} →
      Delta * s ≤ EventConditionalExpectation μ (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s})
    (InitialNonzero : ∀ᵐ ω ∂μ, X 0 ω ≠ 0) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      ((1 + ExpectedValue μ (fun ω => Real.log (X 0 ω / smin))) / Delta) := by
  have Bound := MultiplicativeDriftUpperBoundOfSurvivingStateDrift μ X S smin Delta
    CoordinatesMeasurable ZeroInS MinimumPositive StateLowerBound Values PositiveDelta SurvivingStateDrift
  have LogIntegrable : Integrable (fun ω => Real.log (X 0 ω / smin)) μ :=
    FiniteStateCompositionIntegrable μ (X 0) S (fun s => Real.log (s / smin))
      (CoordinatesMeasurable 0) (Values 0)
  have Formula : (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) =ᵐ[μ]
      (fun ω => (1 + Real.log (X 0 ω / smin)) / Delta) := by
    filter_upwards [InitialNonzero] with ω Nonzero
    exact if_neg Nonzero
  have Means : ExpectedValue μ (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) =
      (1 + ExpectedValue μ (fun ω => Real.log (X 0 ω / smin))) / Delta := by
    unfold ExpectedValue
    rw [integral_congr_ae Formula, integral_div, integral_add (integrable_const 1) LogIntegrable,
      integral_const, probReal_univ, one_smul]
  rwa [Means] at Bound

end
end ECTheoryLib.Tools.Drift
