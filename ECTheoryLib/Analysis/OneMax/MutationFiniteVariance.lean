import ECTheoryLib.Probability.Concentration.VarianceFiniteChernoff
import ECTheoryLib.Analysis.OneMax.MutationVariance

/-!
# Finite-size variance tails of actual mutation candidates

Reuse the existing independent-bit PMF, actual candidate mean and variance
from MutationVariance. Both tails hold for all rates and empty strings.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- Variance-sensitive upper tail of the actual candidate OneMax value. -/
theorem MutationOneMaxFiniteVarianceUpper {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (n : ℝ)*(p : ℝ)+(1-2*(p : ℝ))*(OneMax Parent : ℝ)+d≤(OneMax y : ℝ)}≤
      VarianceFiniteUpperBound n ((n : ℝ)*(p : ℝ)*(1-(p : ℝ))) d := by
  have Bound := IndependentSumFiniteVarianceUpper _ (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
    (MutationOneCoordinateMemLp p Parent) (MutationOneCoordinatesIndependent p Parent)
    (fun i => (MutationOneCoordinateCenteredBounds p Parent i).mono (fun _ h => h.2)) d Nonnegative
  have Sum (y : Bits n) : (∑ i : Fin n, if y i then (1 : ℝ) else 0)=(OneMax y : ℝ) := by
    simp only [OneMax,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp only [Sum,MutationOneMaxExpectation,MutationOneMaxMarginalVariance] at Bound
  exact Bound

theorem MutationOneMaxFiniteVarianceLower {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (OneMax y : ℝ)≤(n : ℝ)*(p : ℝ)+(1-2*(p : ℝ))*(OneMax Parent : ℝ)-d}≤
      VarianceFiniteUpperBound n ((n : ℝ)*(p : ℝ)*(1-(p : ℝ))) d := by
  have Bound := IndependentSumFiniteVarianceLower _ (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
    (MutationOneCoordinateMemLp p Parent) (MutationOneCoordinatesIndependent p Parent)
    (fun i => (MutationOneCoordinateCenteredBounds p Parent i).mono (fun _ h => h.1)) d Nonnegative
  have Sum (y : Bits n) : (∑ i : Fin n, if y i then (1 : ℝ) else 0)=(OneMax y : ℝ) := by
    simp only [OneMax,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp only [Sum,MutationOneMaxExpectation,MutationOneMaxMarginalVariance] at Bound
  exact Bound


end
end ECTheoryLib.Analysis.OneMaxMutation
