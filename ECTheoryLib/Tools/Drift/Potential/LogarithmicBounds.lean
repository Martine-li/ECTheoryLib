import ECTheoryLib.Tools.Drift.Multiplicative
import Mathlib.Tactic

/-!
Finite-range comparisons for the existing zero-safe logarithmic drift potential.
The lower comparison follows from Mathlib's log inequality, without Jensen or tails.
-/
namespace ECTheoryLib.Tools.Drift
noncomputable section

private theorem UnitLogChord {s N : ℝ} (Lower : 1 ≤ s) (Upper : s ≤ N) :
    s * (1 + Real.log N) ≤ N * (1 + Real.log s) := by
  have PositiveS : 0 < s := lt_of_lt_of_le (by norm_num) Lower
  have PositiveN : 0 < N := PositiveS.trans_le Upper
  have Ratio := Real.log_le_sub_one_of_pos (div_pos PositiveN PositiveS)
  rw [Real.log_div PositiveN.ne' PositiveS.ne'] at Ratio
  have Scaled := mul_le_mul_of_nonneg_left Ratio PositiveS.le
  have Cancel : s * (N / s - 1) = N - s := by
    field_simp
  rw [Cancel] at Scaled
  have LogNonnegative : 0 ≤ Real.log s := Real.log_nonneg Lower
  have Compared := mul_le_mul_of_nonneg_right Upper LogNonnegative
  nlinarith

/-- A linear lower comparison on an entire zero-safe finite range. -/
theorem MultiplicativePotentialLowerChord (Delta N s : ℝ) (PositiveDelta : 0 < Delta)
    (PositiveRange : 1 ≤ N) (Gap : s = 0 ∨ 1 ≤ s) (Upper : s ≤ N) :
    (s / N) * ((1 + Real.log N) / Delta) ≤ MultiplicativeDriftPotential 1 Delta s := by
  rcases Gap with Zero | Lower
  · simp [Zero, MultiplicativeDriftPotential]
  · have PositiveS : 0 < s := lt_of_lt_of_le (by norm_num) Lower
    have PositiveN : 0 < N := lt_of_lt_of_le (by norm_num) PositiveRange
    have Linear : (s / N) * (1 + Real.log N) ≤ 1 + Real.log s := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ PositiveN).mpr
      nlinarith [UnitLogChord Lower Upper]
    simp only [MultiplicativeDriftPotential, if_neg PositiveS.ne', div_one]
    calc
      _ = ((s / N) * (1 + Real.log N)) / Delta := by ring
      _ ≤ (1 + Real.log s) / Delta := div_le_div_of_nonneg_right Linear PositiveDelta.le

/-- The upper comparison keeps the success branch exactly zero. -/
theorem MultiplicativePotentialUpperRange (Delta N s : ℝ) (PositiveDelta : 0 < Delta)
    (PositiveRange : 1 ≤ N) (Gap : s = 0 ∨ 1 ≤ s) (Upper : s ≤ N) :
    MultiplicativeDriftPotential 1 Delta s ≤
      if s = 0 then 0 else (1 + Real.log N) / Delta := by
  rcases Gap with Zero | Lower
  · simp [Zero, MultiplicativeDriftPotential]
  · have PositiveS : 0 < s := lt_of_lt_of_le (by norm_num) Lower
    have PositiveN : 0 < N := lt_of_lt_of_le (by norm_num) PositiveRange
    have LogUpper : Real.log s ≤ Real.log N := Real.log_le_log PositiveS Upper
    simp only [MultiplicativeDriftPotential, if_neg PositiveS.ne', div_one]
    exact div_le_div_of_nonneg_right (by linarith) PositiveDelta.le

end
end ECTheoryLib.Tools.Drift

