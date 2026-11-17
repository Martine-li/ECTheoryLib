import ECTheoryLib.Probability.StochasticOrder.StochasticDomination
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Expectations under stochastic domination

Doerr, Corollary 1.8.3 (p. 26), in *Theory of Evolutionary Computation*.
The proof reuses Mathlib's layer-cake formula. Positive-part expectations retain
infinity. Signed Bochner expectations explicitly require integrability, so the
default value of an undefined integral is never used as an expectation.
-/

namespace ECTheoryLib.Probability

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Negation reverses stochastic order of real probability laws. -/
theorem StochasticDominatedNeg (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν) :
    StochasticDominated (ν.map (fun x => -x)) (μ.map (fun x => -x)) := by
  intro a
  rw [Measure.map_apply measurable_neg measurableSet_Iic,
    Measure.map_apply measurable_neg measurableSet_Iic]
  have NegativePreimage : (fun x : ℝ => -x) ⁻¹' Iic a = Ici (-a) := by
    ext x
    change -x ≤ a ↔ -a ≤ x
    constructor
    · intro Bound
      linarith
    · intro Bound
      linarith
  rw [NegativePreimage]
  exact (StochasticDominatedIffClosedTail μ ν).mp Dominated (-a)

/-- Positive-part expectations are ordered, even when one or both are infinite.
For nonnegative variables these are their full extended expectations. -/
theorem StochasticDominatedPositivePartLIntegralLE (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν) :
    (∫⁻ x, ENNReal.ofReal x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal x ∂ν := by
  have PositivePartFormula (ρ : Measure ℝ) :
      (∫⁻ x, ENNReal.ofReal x ∂ρ) = ∫⁻ t in Ioi (0 : ℝ), ρ (Ioi t) := by
    have Nonnegative : 0 ≤ᵐ[ρ] (fun x : ℝ => max x 0) := by
      exact ae_of_all _ (fun x => le_max_right x 0)
    have MeasurablePart : Measurable (fun x : ℝ => max x 0) :=
      measurable_id.max measurable_const
    calc
      (∫⁻ x, ENNReal.ofReal x ∂ρ) = ∫⁻ x, ENNReal.ofReal (max x 0) ∂ρ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
        exact (max_eq_left (show (0 : ENNReal) ≤ ENNReal.ofReal x from bot_le)).symm
      _ = ∫⁻ t in Ioi (0 : ℝ), ρ {x | t < max x 0} :=
        lintegral_eq_lintegral_meas_lt ρ Nonnegative MeasurablePart.aemeasurable
      _ = ∫⁻ t in Ioi (0 : ℝ), ρ (Ioi t) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t PositiveThreshold
        have EventEq : {x : ℝ | t < max x 0} = Ioi t := by
          ext x
          change t < max x 0 ↔ t < x
          rw [lt_max_iff]
          exact or_iff_left (not_lt.mpr PositiveThreshold.le)
        change ρ {x : ℝ | t < max x 0} = ρ (Ioi t)
        rw [EventEq]
  rw [PositivePartFormula μ, PositivePartFormula ν]
  apply lintegral_mono
  intro t
  exact (StochasticDominatedIffStrictTail μ ν).mp Dominated t

/-- Positive-part expectations for variables on different spaces, without a
finite-expectation assumption. Nonnegative variables need no truncation. -/
theorem StochasticDominatedPositivePartExpectationLE {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (Y : Ω' → ℝ)
    (MeasurableX : AEMeasurable X P) (MeasurableY : AEMeasurable Y Q)
    (Dominated : StochasticDominated (P.map X) (Q.map Y)) :
    (∫⁻ ω, ENNReal.ofReal (X ω) ∂P) ≤ ∫⁻ ω, ENNReal.ofReal (Y ω) ∂Q := by
  have FirstProbability : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map MeasurableX
  have SecondProbability : IsProbabilityMeasure (Q.map Y) :=
    Measure.isProbabilityMeasure_map MeasurableY
  have PositivePartMeasurable : Measurable (fun x : ℝ => ENNReal.ofReal x) :=
    measurable_id.ennreal_ofReal
  have Bound := StochasticDominatedPositivePartLIntegralLE _ _ Dominated
  rw [lintegral_map' PositivePartMeasurable.aemeasurable MeasurableX,
    lintegral_map' PositivePartMeasurable.aemeasurable MeasurableY] at Bound
  exact Bound

/-- Corollary 1.8.3 for integrable real probability laws, including signed laws.
Integrability makes explicit the finite-expectation convention on book p. 16. -/
theorem StochasticDominatedIntegralLE (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν)
    (IntegrableFirst : Integrable (fun x : ℝ => x) μ)
    (IntegrableSecond : Integrable (fun x : ℝ => x) ν) :
    (∫ x, x ∂μ) ≤ ∫ x, x ∂ν := by
  have PositiveParts := StochasticDominatedPositivePartLIntegralLE μ ν Dominated
  have ProbabilityNeg (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
      IsProbabilityMeasure (ρ.map (fun x => -x)) := by
    exact Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  have NegativeParts := StochasticDominatedPositivePartLIntegralLE _ _
    (StochasticDominatedNeg μ ν Dominated)
  have MeasurablePositive : Measurable (fun x : ℝ => ENNReal.ofReal x) :=
    measurable_id.ennreal_ofReal
  have MeasurableNeg : Measurable (fun x : ℝ => -x) := measurable_neg
  rw [lintegral_map MeasurablePositive MeasurableNeg,
    lintegral_map MeasurablePositive MeasurableNeg] at NegativeParts
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part IntegrableFirst,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part IntegrableSecond]
  apply sub_le_sub
  · exact ENNReal.toReal_mono IntegrableSecond.lintegral_lt_top.ne PositiveParts
  · exact ENNReal.toReal_mono IntegrableFirst.neg.lintegral_lt_top.ne NegativeParts

/-- Different sample spaces are allowed. Integrability is supplied for the actual
variables, then transferred to their laws using Mathlib's map API. -/
theorem StochasticDominatedExpectationLE {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (Y : Ω' → ℝ)
    (IntegrableX : Integrable X P) (IntegrableY : Integrable Y Q)
    (Dominated : StochasticDominated (P.map X) (Q.map Y)) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂Q := by
  have FirstProbability : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map IntegrableX.aemeasurable
  have SecondProbability : IsProbabilityMeasure (Q.map Y) :=
    Measure.isProbabilityMeasure_map IntegrableY.aemeasurable
  have FirstIntegrable : Integrable (fun x : ℝ => x) (P.map X) := by
    exact (integrable_map_measure aestronglyMeasurable_id IntegrableX.aemeasurable).mpr
      IntegrableX
  have SecondIntegrable : Integrable (fun x : ℝ => x) (Q.map Y) := by
    exact (integrable_map_measure aestronglyMeasurable_id IntegrableY.aemeasurable).mpr
      IntegrableY
  have Bound := StochasticDominatedIntegralLE _ _ Dominated FirstIntegrable SecondIntegrable
  have FirstIdentityMeasurable : AEStronglyMeasurable (fun x : ℝ => x) (P.map X) :=
    aestronglyMeasurable_id
  have SecondIdentityMeasurable : AEStronglyMeasurable (fun x : ℝ => x) (Q.map Y) :=
    aestronglyMeasurable_id
  rw [integral_map IntegrableX.aemeasurable FirstIdentityMeasurable,
    integral_map IntegrableY.aemeasurable SecondIdentityMeasurable] at Bound
  exact Bound

end
end ECTheoryLib.Probability
