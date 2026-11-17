import ECTheoryLib.Analysis.LeadingOnes.OnePlusOneEA.FitnessLevels
import ECTheoryLib.Probability.StochasticOrder.ExtendedNatExpectation
import ECTheoryLib.Probability.Distributions.GeometricWaiting
import ECTheoryLib.Probability.HittingTimes.Expectation

/-!
# Standard (1+1) EA on LeadingOnes: fitness-level expected runtime

Integrate the original path-law comparison with its explicit geometric reference
sum. The expectation retains infinity until the finite upper bound is proved.
Initialization is time zero; the cost counts subsequent mutation rounds. The
bound holds for arbitrary initial PMFs and is not claimed to be an exact mean.
-/

namespace ECTheoryLib.Analysis.OnePlusOneEAOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- The original standard EA has mean runtime at most the sum of reciprocal level rates. -/
theorem RuntimeFitnessLevelExpectationBound {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) :
    ExpectedHittingTime (Step PositiveLength) (fun x => x = AllOnes n) Initial ≤
      ∑ i : Fin n, ENNReal.ofReal (1 / (FitnessLevelProbability PositiveLength i : ℝ)) := by
  let Reference := Measure.pi (fun i : Fin n =>
    geometricMeasure (FitnessLevelProbability PositiveLength i))
  let WaitingTime := fun z : Fin n → ℕ => ∑ i, ((z i + 1 : ℕ) : WithTop ℕ)
  have WaitingMeasurable : Measurable WaitingTime := measurable_of_countable _
  have : IsProbabilityMeasure (Reference.map WaitingTime) :=
    Measure.isProbabilityMeasure_map WaitingMeasurable.aemeasurable
  have Bound := StochasticDominatedExtendedNatExpectationLE
    (PathMeasure (Step PositiveLength) Initial) (FirstHittingTime (fun x => x = AllOnes n))
    (FirstHittingTimeMeasurable _) (Reference.map WaitingTime)
    (RuntimeFitnessLevelGeometricBound PositiveLength Initial)
  calc
    ExpectedHittingTime (Step PositiveLength) (fun x => x = AllOnes n) Initial ≤
        ∫⁻ t, ENat.toENNReal t ∂Reference.map WaitingTime := Bound
    _ = ∫⁻ z, ENat.toENNReal (WaitingTime z) ∂Reference :=
      lintegral_map (measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t))
        WaitingMeasurable
    _ = _ := GeometricWaitingProductSumExpectation
      (FitnessLevelProbability PositiveLength) (FitnessLevelProbabilityPositive PositiveLength)

/-- The fitness-level bound proves finite expected runtime without assuming termination. -/
theorem RuntimeFitnessLevelExpectationFinite {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) :
    ExpectedHittingTime (Step PositiveLength) (fun x => x = AllOnes n) Initial < ⊤ := by
  exact lt_of_le_of_lt (RuntimeFitnessLevelExpectationBound PositiveLength Initial)
    (ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top))

end
end ECTheoryLib.Analysis.OnePlusOneEAOnLeadingOnes
