import ECTheoryLib.Operators.Crossover.SinglePoint
import ECTheoryLib.Problems.TargetOneMax
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ECTheoryLib.Analysis.Crossover

open MeasureTheory ECTheoryLib.Problems.TargetOneMax

noncomputable section

/-- The additive score of the actual single-point offspring has mean parental score. -/
theorem SinglePointAdditiveExpectation {n : Nat} (Parent Other : Bits n)
    (Score : Fin n → Bool → ℝ) :
    (∫ Candidate, ∑ i : Fin n, Score i (Candidate i)
      ∂(SinglePointCrossover Parent Other).toMeasure) =
      ((∑ i : Fin n, Score i (Parent i)) + (∑ i : Fin n, Score i (Other i))) / 2 := by
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [SinglePointCoordinateIntegral]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- Book 1.6.6(c), arbitrary fixed target in the source's offspring-first order. -/
theorem SinglePointHammingExpectation {n : Nat} (Parent Other Target : Bits n) :
    (∫ Candidate, (Hamming Candidate Target : ℝ)
      ∂(SinglePointCrossover Parent Other).toMeasure) =
      ((Hamming Parent Target : ℝ) + (Hamming Other Target : ℝ)) / 2 := by
  simpa only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
    SinglePointAdditiveExpectation Parent Other
      (fun i b => if Target i = b then (0 : ℝ) else 1)

/-- Book 1.6.6(c), distance from the first parent, including coinciding parents. -/
theorem SinglePointParentDistanceExpectation {n : Nat} (Parent Other : Bits n) :
    (∫ Candidate, (Hamming Parent Candidate : ℝ)
      ∂(SinglePointCrossover Parent Other).toMeasure) = (Hamming Parent Other : ℝ) / 2 := by
  simpa only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one,
    ite_true, Finset.sum_const_zero, zero_add] using
    SinglePointAdditiveExpectation Parent Other
      (fun i b => if b = Parent i then (0 : ℝ) else 1)

/-- The actual OneMax score of the single-point crossover candidate before selection. -/
theorem SinglePointOneMaxExpectation {n : Nat} (Parent Other : Bits n) :
    (∫ Candidate, (OneMax Candidate : ℝ)
      ∂(SinglePointCrossover Parent Other).toMeasure) =
      ((OneMax Parent : ℝ) + (OneMax Other : ℝ)) / 2 := by
  simpa only [OneMax, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
    SinglePointAdditiveExpectation Parent Other
      (fun _ b => if b then (1 : ℝ) else 0)

end
end ECTheoryLib.Analysis.Crossover

