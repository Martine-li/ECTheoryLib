import ECTheoryLib.Probability.Concentration.AdditiveChernoff
import ECTheoryLib.Analysis.OneMax.MutationVariance

/-!
# Additive concentration of the actual mutation OneMax score

The candidate coordinates are independent at every mutation rate in [0,1].
Their actual mean is np+(1-2p)OneMax(parent). The quadratic additive upper
bound includes zero mean and empty strings, before survivor selection.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- Closed additive upper tail of the actual mutation score, with its
explicit mean, every mutation rate in [0,1], and no positive-mean premise. -/
theorem MutationOneMaxAdditiveChernoffUpper {n : ℕ} (p : I) (Parent : Bits n)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ) + l ≤
        (OneMax y : ℝ)} ≤
      Real.exp (-(l ^ 2) / (2 *
        ((n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ)) + 2 * l / 3)) := by
  have Bound := UnitIndependentSumAdditiveChernoffUpperQuadratic
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure
    (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)
    (MutationOneCoordinatesIndependent p Parent)
    (fun _ => ae_of_all _ (fun y => by split <;> norm_num)) l Nonnegative
  have Sum (y : Bits n) : (∑ i : Fin n, if y i then (1 : ℝ) else 0) =
      (OneMax y : ℝ) := by
    simp only [OneMax, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simpa only [Sum, MutationOneMaxExpectation] using Bound

end
end ECTheoryLib.Analysis.OneMaxMutation

