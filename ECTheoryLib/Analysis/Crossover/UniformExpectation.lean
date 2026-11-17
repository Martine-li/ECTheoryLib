import ECTheoryLib.Operators.Crossover.Uniform
import ECTheoryLib.Problems.TargetOneMax
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ECTheoryLib.Analysis.Crossover

open MeasureTheory ECTheoryLib.Problems.TargetOneMax

noncomputable section

/-- An additive score of the actual crossover candidate has the mean parental score. -/
theorem UniformCrossoverAdditiveExpectation {n : Nat} (Parent Other : Bits n)
    (Score : Fin n → Bool → ℝ) :
    (∫ Candidate, ∑ i : Fin n, Score i (Candidate i)
      ∂(UniformCrossover Parent Other).toMeasure) =
      ((∑ i : Fin n, Score i (Parent i)) + (∑ i : Fin n, Score i (Other i))) / 2 := by
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [UniformCrossoverCoordinateIntegral]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- Book 1.6.6(b), arbitrary fixed target. Hamming is written in the book's
offspring-first order; expanding the existing definition preserves that order. -/
theorem UniformCrossoverHammingExpectation {n : Nat} (Parent Other Target : Bits n) :
    (∫ Candidate, (Hamming Candidate Target : ℝ)
      ∂(UniformCrossover Parent Other).toMeasure) =
      ((Hamming Parent Target : ℝ) + (Hamming Other Target : ℝ)) / 2 := by
  simpa only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
    UniformCrossoverAdditiveExpectation Parent Other
      (fun i b => if Target i = b then (0 : ℝ) else 1)

/-- Book 1.6.6(b), distance from the first parent, with no distinct-parent assumption. -/
theorem UniformCrossoverParentDistanceExpectation {n : Nat} (Parent Other : Bits n) :
    (∫ Candidate, (Hamming Parent Candidate : ℝ)
      ∂(UniformCrossover Parent Other).toMeasure) = (Hamming Parent Other : ℝ) / 2 := by
  simpa only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one,
    ite_true, Finset.sum_const_zero, zero_add] using
    UniformCrossoverAdditiveExpectation Parent Other
      (fun i b => if b = Parent i then (0 : ℝ) else 1)

/-- The actual OneMax score of a crossover candidate before selection. -/
theorem UniformCrossoverOneMaxExpectation {n : Nat} (Parent Other : Bits n) :
    (∫ Candidate, (OneMax Candidate : ℝ)
      ∂(UniformCrossover Parent Other).toMeasure) =
      ((OneMax Parent : ℝ) + (OneMax Other : ℝ)) / 2 := by
  simpa only [OneMax, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
    UniformCrossoverAdditiveExpectation Parent Other
      (fun _ b => if b then (1 : ℝ) else 0)

end
end ECTheoryLib.Analysis.Crossover

