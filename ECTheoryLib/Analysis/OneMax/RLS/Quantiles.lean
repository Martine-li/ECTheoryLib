import ECTheoryLib.Analysis.OneMax.RLS.StochasticProgress
import ECTheoryLib.Probability.StochasticOrder.OrderedCoupling

/-!
# Quantiles of the actual RLS potential

The potential law comes from the actual RLS trajectory with arbitrary initial
PMF. Its quantiles give marginally faithful ordered couplings across times.
The quantile construction specifies marginal laws, not the original joint
temporal law of the algorithm. Levels lie strictly between zero and one.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Interior quantile of the actual zero-count potential at iteration t. -/
def PotentialQuantile {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n))
    (t : ℕ) (u : OpenUnitInterval) : ℝ :=
  RealQuantile ((PathMeasure (Step PositiveLength) Initial).map
    (fun Path => Potential (Path t))) u

/-- The uniform quantile construction has the full actual marginal potential law. -/
theorem PotentialQuantileHasLaw {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) :
    HasLaw (PotentialQuantile PositiveLength Initial t)
      ((PathMeasure (Step PositiveLength) Initial).map (fun Path => Potential (Path t)))
      OpenUnitUniform := by
  have MeasurablePotential : Measurable (fun Path : ℕ → Bits n => Potential (Path t)) :=
    (measurable_of_finite Potential).comp (measurable_pi_apply t)
  have ProbabilityLaw : IsProbabilityMeasure
      ((PathMeasure (Step PositiveLength) Initial).map (fun Path => Potential (Path t))) :=
    Measure.isProbabilityMeasure_map MeasurablePotential.aemeasurable
  exact QuantileHasLaw _

/-- Every interior percentile of the potential is nonincreasing over time. -/
theorem PotentialQuantileAntitone {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (s t : ℕ) (Earlier : s ≤ t) (u : OpenUnitInterval) :
    PotentialQuantile PositiveLength Initial t u ≤ PotentialQuantile PositiveLength Initial s u := by
  have ProbabilityLaw (k : ℕ) : IsProbabilityMeasure
      ((PathMeasure (Step PositiveLength) Initial).map (fun Path => Potential (Path k))) := by
    have MeasurablePotential : Measurable (fun Path : ℕ → Bits n => Potential (Path k)) :=
      (measurable_of_finite Potential).comp (measurable_pi_apply k)
    exact Measure.isProbabilityMeasure_map MeasurablePotential.aemeasurable
  exact StochasticDominatedQuantileLE _ _
    (PotentialLawStochasticAntitone PositiveLength Initial s t Earlier) u

/-- Connect a percentile bound directly to the actual event probability. -/
theorem PotentialQuantileLeIff {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) (u : OpenUnitInterval) (a : ℝ) :
    PotentialQuantile PositiveLength Initial t u ≤ a ↔
      (u : ℝ) ≤ (PathMeasure (Step PositiveLength) Initial).real
        {Path | Potential (Path t) ≤ a} := by
  have MeasurablePotential : Measurable (fun Path : ℕ → Bits n => Potential (Path t)) :=
    (measurable_of_finite Potential).comp (measurable_pi_apply t)
  have ProbabilityLaw : IsProbabilityMeasure
      ((PathMeasure (Step PositiveLength) Initial).map (fun Path => Potential (Path t))) :=
    Measure.isProbabilityMeasure_map MeasurablePotential.aemeasurable
  unfold PotentialQuantile
  rw [QuantileLeIffCDF, cdf_eq_real,
    map_measureReal_apply MeasurablePotential measurableSet_Iic]
  rfl

end
end ECTheoryLib.Analysis.RLSOnOneMax
