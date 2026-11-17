import ECTheoryLib.Probability.Concentration.ChernoffMeanUpper
import ECTheoryLib.Analysis.OneMax.MutationVariance

/-!
# Mean-estimated finite upper tails of the actual mutation OneMax score

The supplied estimate bounds the actual candidate mean; it replaces both
the threshold and the finite bound. The automatic score estimate uses np+k.
These interfaces concern mutation before survivor selection.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

theorem MutationOneMaxFiniteChernoffUpperOfMeanLe {n : ℕ} (p : I) (Parent : Bits n)
    (U : ℝ) (MeanUpper : (n : ℝ) * (p : ℝ) +
      (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (1 + d) * U ≤ (OneMax y : ℝ)} ≤ FiniteChernoffUpperBound n U d := by
  have Sum (y : Bits n) : (∑ i : Fin n, if y i then (1 : ℝ) else 0) =
      (OneMax y : ℝ) := by
    simp only [OneMax, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have Bound := UnitIndependentSumFiniteChernoffUpperOfMeanLe
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure
    (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)
    (MutationOneCoordinatesIndependent p Parent)
    (fun _ => ae_of_all _ (fun y => by split <;> norm_num)) U
    (by simpa only [Sum, MutationOneMaxExpectation] using MeanUpper) d Nonnegative
  simpa only [Sum] using Bound

/-- The coarse estimate np+k avoids needing the exact contribution -2pk.
It is valid for all rates in [0,1], even when the estimate exceeds n. -/
theorem MutationOneMaxFiniteChernoffUpperScoreEstimate {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (1 + d) * ((n : ℝ) * (p : ℝ) + (OneMax Parent : ℝ)) ≤
        (OneMax y : ℝ)} ≤
      FiniteChernoffUpperBound n ((n : ℝ) * (p : ℝ) + (OneMax Parent : ℝ)) d := by
  apply MutationOneMaxFiniteChernoffUpperOfMeanLe p Parent _ ?_ d Nonnegative
  nlinarith [mul_nonneg p.property.1 (Nat.cast_nonneg (OneMax Parent))]

end
end ECTheoryLib.Analysis.OneMaxMutation

