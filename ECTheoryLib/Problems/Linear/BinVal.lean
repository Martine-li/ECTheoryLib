import ECTheoryLib.Problems.Linear
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.NormNum

/-!
# Binary value in the source's left-to-right order

Example 2.3.7 of Lengler's chapter uses minimization and weights 2^(n-i)
with one-based indices. Fin n therefore uses 2^(n-1-i.val). These objective
facts include the empty string and do not depend on an algorithm.
-/
namespace ECTheoryLib.Problems.Linear.BinVal
open scoped BigOperators
noncomputable section

def Weights {n : ℕ} (i : Fin n) : ℝ := (2 : ℝ) ^ (n - 1 - i.val)

def Score {n : ℕ} (x : Bits n) : ℝ := Linear.Score Weights x

theorem WeightPositive {n : ℕ} (i : Fin n) : 0 < Weights i := by
  exact pow_pos (by norm_num) _

theorem OneLeWeight {n : ℕ} (i : Fin n) : 1 ≤ Weights i := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem FirstWeight (n : ℕ) : Weights (0 : Fin (n + 1)) = (2 : ℝ) ^ n := by
  simp [Weights]

theorem LastWeight (n : ℕ) : Weights (Fin.last n) = 1 := by
  simp [Weights]

theorem WeightsSum (n : ℕ) : (∑ i : Fin n, Weights i) = (2 : ℝ) ^ n - 1 := by
  unfold Weights
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (2 : ℝ) ^ (n - 1 - k)) n,
    Finset.sum_range_reflect]
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num

/-- Equality with the usual natural binary integer value, not a reversed encoding. -/
theorem ScoreEqNatSum {n : ℕ} (x : Bits n) :
    Score x = ((∑ i : Fin n, (2 : ℕ) ^ (n - 1 - i.val) *
      (if x i then 1 else 0)) : ℕ) := by
  unfold Score Linear.Score Weights
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp

theorem OneCountLeScore {n : ℕ} (x : Bits n) : (OneMax x : ℝ) ≤ Score x := by
  rw [← Linear.ScoreUnitWeights x]
  unfold Score Linear.Score
  apply Finset.sum_le_sum
  intro i _
  cases x i <;> simp [OneLeWeight i]

theorem ScoreLeMaximum {n : ℕ} (x : Bits n) : Score x ≤ (2 : ℝ) ^ n - 1 := by
  rw [← WeightsSum n]
  unfold Score Linear.Score
  apply Finset.sum_le_sum
  intro i _
  cases x i <;> simp [le_of_lt (WeightPositive i)]

theorem ScoreSingleOne {n : ℕ} (i : Fin n) :
    Score (fun j => decide (j = i)) = Weights i := by
  unfold Score Linear.Score
  simp

theorem OneCountSingleOne {n : ℕ} (i : Fin n) :
    OneMax (fun j => decide (j = i)) = 1 := by
  simp [OneMax]

theorem MinimumPositiveAttained {n : ℕ} (PositiveLength : 0 < n) :
    ∃ x : Bits n, Score x = 1 := by
  cases n with
  | zero => omega
  | succ k => exact ⟨fun j => decide (j = Fin.last k), by rw [ScoreSingleOne, LastWeight]⟩

end
end ECTheoryLib.Problems.Linear.BinVal

