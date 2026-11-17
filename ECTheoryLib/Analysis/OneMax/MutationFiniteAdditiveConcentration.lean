import ECTheoryLib.Probability.Concentration.FiniteAdditiveChernoff
import ECTheoryLib.Analysis.OneMax.MutationVariance

/-!
# Finite additive concentration of the mutation OneMax score

The finite-size expression retains the number of coordinates and its exact
maximum-threshold and beyond-maximum branches. The mean is the actual
mutation mean, for all mutation rates in [0,1], before survivor selection.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- The strongest additive Chernoff bound for actual mutation candidates,
including zero mean, empty strings and maximum/beyond-maximum thresholds. -/
theorem MutationOneMaxFiniteAdditiveChernoffUpper {n : ℕ} (p : I) (Parent : Bits n)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ) + l ≤
        (OneMax y : ℝ)} ≤
      FiniteAdditiveChernoffUpperBound n
        ((n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ)) l := by
  have Bound := UnitIndependentSumFiniteAdditiveChernoffUpper
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

