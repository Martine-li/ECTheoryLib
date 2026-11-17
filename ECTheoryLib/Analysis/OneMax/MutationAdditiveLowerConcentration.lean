import ECTheoryLib.Probability.Concentration.AdditiveChernoffLower
import ECTheoryLib.Analysis.OneMax.MutationVariance

/-!
# Additive lower concentration of the mutation OneMax score

Both interfaces use the actual mutation mean for arbitrary parents and rates
in [0,1], before survivor selection. The finite bound explicitly extends
negative thresholds by zero; the quadratic bound includes all deviations.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

theorem MutationOneMaxFiniteAdditiveChernoffLower {n : ℕ} (p : I) (Parent : Bits n)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (OneMax y : ℝ) ≤
        (n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ) - l} ≤
      FiniteAdditiveChernoffLowerBound n
        ((n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ)) l := by
  have Bound := UnitIndependentSumFiniteAdditiveChernoffLower
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

theorem MutationOneMaxAdditiveChernoffLowerQuadratic {n : ℕ} (p : I) (Parent : Bits n)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (OneMax y : ℝ) ≤
        (n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ) - l} ≤
      Real.exp (-(l ^ 2) /
        (2 * ((n : ℝ) * (p : ℝ) + (1 - 2 * (p : ℝ)) * (OneMax Parent : ℝ)))) := by
  have Bound := UnitIndependentSumAdditiveChernoffLowerQuadratic
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

