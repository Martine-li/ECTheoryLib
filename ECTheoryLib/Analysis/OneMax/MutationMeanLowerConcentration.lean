import ECTheoryLib.Probability.Concentration.ChernoffMeanLower
import ECTheoryLib.Analysis.OneMax.MutationVariance

/-!
# Mean-estimated finite lower tails of the actual mutation OneMax score

The supplied estimate is a lower bound on the actual candidate mean.
The automatic estimate n*min(p,1-p) is valid for every parent and rate.
These interfaces concern mutation before survivor selection.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

theorem MutationOneMaxFiniteChernoffLowerOfLeMean {n : ℕ} (p : I) (Parent : Bits n)
    (L : ℝ) (MeanLower : L ≤ (n : ℝ) * (p : ℝ) +
      (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ))
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (OneMax y : ℝ) ≤ (1 - d) * L} ≤ FiniteChernoffLowerBound n L d := by
  have Sum (y : Bits n) : (∑ i : Fin n, if y i then (1 : ℝ) else 0) =
      (OneMax y : ℝ) := by
    simp only [OneMax, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have Bound := UnitIndependentSumFiniteChernoffLowerOfLeMean
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure
    (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)
    (MutationOneCoordinatesIndependent p Parent)
    (fun _ => ae_of_all _ (fun y => by split <;> norm_num)) L
    (by simpa only [Sum, MutationOneMaxExpectation] using MeanLower) d InUnit
  simpa only [Sum] using Bound

/-- Each output bit has one-probability at least min(p,1-p), independently of
the parent. The estimate covers rates above one half and empty strings. -/
theorem MutationOneMaxFiniteChernoffLowerRateEstimate {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (OneMax y : ℝ) ≤ (1 - d) *
        ((n : ℝ) * min (p : ℝ) (1 - (p : ℝ)))} ≤
      FiniteChernoffLowerBound n ((n : ℝ) * min (p : ℝ) (1 - (p : ℝ))) d := by
  apply MutationOneMaxFiniteChernoffLowerOfLeMean p Parent _ ?_ d InUnit
  have ScoreNonnegative : (0 : ℝ) ≤ (OneMax Parent : ℝ) := Nat.cast_nonneg _
  have ScoreBound : (OneMax Parent : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr (Problems.OneMax.OneMaxLeN Parent)
  have Zeros := mul_le_mul_of_nonneg_left (min_le_left (p : ℝ) (1 - (p : ℝ)))
    (sub_nonneg.mpr ScoreBound)
  have Ones := mul_le_mul_of_nonneg_left (min_le_right (p : ℝ) (1 - (p : ℝ)))
    ScoreNonnegative
  nlinarith [Zeros, Ones]

end
end ECTheoryLib.Analysis.OneMaxMutation

