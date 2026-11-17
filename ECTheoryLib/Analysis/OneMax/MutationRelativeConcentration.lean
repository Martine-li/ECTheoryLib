import ECTheoryLib.Probability.Concentration.TwoSidedChernoff
import ECTheoryLib.Analysis.OneMax.MutationVariance

/-!
# Relative concentration of the actual mutation OneMax score

The candidate coordinates are independent at every mutation rate in [0,1].
Their actual mean is np+(1-2p)OneMax(parent). This module applies the two-sided
relative Chernoff bound before survivor selection, including empty strings.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- Closed two-sided relative deviation of the actual candidate score, with its
explicit mean and no restriction to mutation rates at most one half. -/
theorem MutationOneMaxTwoSidedChernoff {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | d * ((n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ)) ≤
        |(OneMax y : ℝ) -
          ((n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ))|} ≤
      2 * Real.exp (-(d ^ 2) *
        ((n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ)) / 3) := by
  have Bound := UnitIndependentSumTwoSidedChernoff
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure
    (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)
    (MutationOneCoordinatesIndependent p Parent)
    (fun _ => ae_of_all _ (fun y => by split <;> norm_num)) d InUnit
  have Sum (y : Bits n) : (∑ i : Fin n, if y i then (1 : ℝ) else 0) =
      (OneMax y : ℝ) := by
    simp only [OneMax, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simpa only [Sum, MutationOneMaxExpectation] using Bound

end
end ECTheoryLib.Analysis.OneMaxMutation

