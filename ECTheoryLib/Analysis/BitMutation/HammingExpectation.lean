import ECTheoryLib.Analysis.BitMutation.CoordinateMoments
import ECTheoryLib.Problems.TargetOneMax
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace ECTheoryLib.Analysis.BitMutation

open MeasureTheory ECTheoryLib.Problems.TargetOneMax ECTheoryLib.Analysis.OneMaxMutation
open scoped unitInterval

noncomputable section

/-- The mismatch to an arbitrary target bit, under the existing actual mutation PMF. -/
theorem MutationTargetCoordinateExpectation {n : Nat} (p : I) (Parent Target : Bits n)
    (i : Fin n) :
    (∫ Candidate, (if Target i = Candidate i then (0 : ℝ) else 1)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure) =
      (p : ℝ) + (1 - 2 * (p : ℝ)) * (if Target i = Parent i then 0 else 1) := by
  cases TargetBit : Target i with
  | false =>
      have Indicator (Candidate : Bits n) :
          (if false = Candidate i then (0 : ℝ) else 1) =
            (if Candidate i then 1 else 0) := by
        cases Candidate i <;> norm_num
      simp_rw [Indicator]
      rw [MutationOneCoordinateExpectation]
      cases Parent i <;> simp only [MutationOneProbability, unitInterval.coe_symm_eq,
        ite_true, ite_false, Bool.false_eq_true] <;> ring
  | true =>
      have Indicator (Candidate : Bits n) :
          (if true = Candidate i then (0 : ℝ) else 1) =
            1 - (if Candidate i then 1 else 0) := by
        cases Candidate i <;> norm_num
      simp_rw [Indicator]
      rw [integral_sub (integrable_const _) Integrable.of_finite,
        integral_const, probReal_univ, one_smul, MutationOneCoordinateExpectation]
      cases Parent i <;> simp only [MutationOneProbability, unitInterval.coe_symm_eq,
        ite_true, ite_false, Bool.false_eq_true] <;> ring

/-- Book 1.6.6(a), with the offspring first as in the source and real subtraction.
All rates in [0,1], empty strings and arbitrary fixed targets are allowed. -/
theorem MutationTargetHammingExpectation {n : Nat} (p : I) (Parent Target : Bits n) :
    (∫ Candidate, (Hamming Candidate Target : ℝ)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure) =
      (Hamming Parent Target : ℝ) + (p : ℝ) * ((n : ℝ) - 2 * (Hamming Parent Target : ℝ)) := by
  simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [MutationTargetCoordinateExpectation]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The actual standard mutation used by the algorithms, before survivor selection. -/
theorem StandardMutationTargetHammingExpectation {n : Nat}
    (PositiveLength : 0 < n) (Parent Target : Bits n) :
    (∫ Candidate, (Hamming Candidate Target : ℝ)
      ∂(StandardBitMutation PositiveLength Parent).toMeasure) =
      (Hamming Parent Target : ℝ) + 1 - 2 * (Hamming Parent Target : ℝ) / (n : ℝ) := by
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1 / (n : ℝ), ⟨by positivity,
    (div_le_one PositiveN).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1 / (n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveN, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  have Bound := MutationTargetHammingExpectation p Parent Target
  simp only [Rate] at Bound
  change (∫ Candidate, (Hamming Candidate Target : ℝ)
    ∂(StandardBitMutation PositiveLength Parent).toMeasure) =
    (Hamming Parent Target : ℝ) + (1 / (n : ℝ)) *
      ((n : ℝ) - 2 * (Hamming Parent Target : ℝ)) at Bound
  rw [Bound]
  field_simp
  ring

end
end ECTheoryLib.Analysis.BitMutation

