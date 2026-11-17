import ECTheoryLib.Operators.Mutation.IndependentBitBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Specified multi-bit mutation events

The probability of a specified child depends only on the number of changed
coordinates. These are exact point probabilities, not probabilities of changing
an arbitrary set of that size. The formulas include the n=1 boundary.
-/
namespace ECTheoryLib
noncomputable section

/-- Number of coordinates at which the specified child differs from its parent. -/
def BitDifferenceCount {n : ℕ} (x y : Bits n) : ℕ :=
  (Finset.univ.filter (fun i => y i ≠ x i)).card

/-- A specified d-bit change has probability n^(-d)(1-1/n)^(n-d).
No combinatorial factor occurs because the child, and hence the changed set,
is fixed. -/
theorem StandardBitMutationPattern {n : ℕ} (hn : 0 < n) (x y : Bits n) :
    StandardBitMutation hn x y = (n : ENNReal)⁻¹ ^ BitDifferenceCount x y *
      (1 - (n : ENNReal)⁻¹) ^ (n - BitDifferenceCount x y) := by
  classical
  rw [StandardBitMutationProbability]
  have Counts := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin n => y i = x i)
  simp only [Finset.card_univ, Fintype.card_fin] at Counts
  change (Finset.univ.filter (fun i : Fin n => y i = x i)).card +
    (Finset.univ.filter (fun i : Fin n => y i ≠ x i)).card = n at Counts
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  unfold BitDifferenceCount
  have SameCount : (Finset.univ.filter (fun i : Fin n => y i = x i)).card =
      n - (Finset.univ.filter (fun i : Fin n => y i ≠ x i)).card := by omega
  rw [SameCount]
  exact mul_comm _ _

/-- Ordinary real form of the exact specified-pattern probability. -/
theorem StandardBitMutationPatternReal {n : ℕ} (hn : 0 < n) (x y : Bits n) :
    (StandardBitMutation hn x y).toReal = (1 / (n : ℝ)) ^ BitDifferenceCount x y *
      (1 - 1 / (n : ℝ)) ^ (n - BitDifferenceCount x y) := by
  rw [StandardBitMutationPattern, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le (StandardBitMutationRateBound n hn) ENNReal.one_ne_top]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one, one_div]

/-- Positive mass of a specified k-bit change for 1 ≤ k ≤ n.
At n=1 the unchanged-coordinate exponent is zero. -/
theorem StandardPatternProbabilityPositive {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    0 < (1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ (n - k) := by
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  by_cases One : n = 1
  · have KOne : k = 1 := by omega
    rw [One, KOne]
    norm_num
  · have NReal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have Positive : (0 : ℝ) < n := by exact_mod_cast hn
    exact mul_pos (pow_pos (one_div_pos.mpr Positive) _)
      (pow_pos (sub_pos.mpr ((div_lt_one Positive).mpr NReal)) _)

/-- The reciprocal probability of a specified k-bit change is at most e n^k
for 1 ≤ k ≤ n. Retaining only n-k unchanged bits is at least as likely as
retaining n-1, so the existing one-bit reciprocal estimate supplies the constant. -/
theorem StandardPatternProbabilityInverseBound {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    1 / ((1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ (n - k)) ≤
      Real.exp 1 * (n : ℝ) ^ k := by
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have NPositive : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have RateBound : 1 / (n : ℝ) ≤ 1 :=
    (div_le_one NPositive).mpr (by exact_mod_cast hn)
  have Exponent : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have Lower : (1 / (n : ℝ)) ^ (k - 1) * StandardOneBitProbability n ≤
      (1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ (n - k) := by
    have BaseBound := pow_le_pow_of_le_one (sub_nonneg.mpr RateBound)
      (show 1 - 1 / (n : ℝ) ≤ 1 by linarith [one_div_pos.mpr NPositive])
      (show n - k ≤ n - 1 by omega)
    have Product := mul_le_mul_of_nonneg_left BaseBound
      (show 0 ≤ (1 / (n : ℝ)) ^ k by positivity)
    have Factor : (1 / (n : ℝ)) ^ (k - 1) * StandardOneBitProbability n =
        (1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ (n - 1) := by
      unfold StandardOneBitProbability
      rw [← mul_assoc, ← pow_succ, Exponent]
    rw [Factor]
    exact Product
  have Positive : 0 < (1 / (n : ℝ)) ^ (k - 1) * StandardOneBitProbability n :=
    mul_pos (pow_pos (one_div_pos.mpr NPositive) _) (StandardOneBitProbabilityPositive hn)
  calc
    1 / ((1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ (n - k)) ≤
        1 / ((1 / (n : ℝ)) ^ (k - 1) * StandardOneBitProbability n) :=
      one_div_le_one_div_of_le Positive Lower
    _ = (1 / StandardOneBitProbability n) * (n : ℝ) ^ (k - 1) := by
      simp only [one_div, mul_inv_rev, ← inv_pow, inv_inv]
    _ ≤ (Real.exp 1 * (n : ℝ)) * (n : ℝ) ^ (k - 1) :=
      mul_le_mul_of_nonneg_right (StandardOneBitProbabilityInverseBound hn) (by positivity)
    _ = Real.exp 1 * (n : ℝ) ^ k := by
      rw [mul_assoc, mul_comm (n : ℝ), ← pow_succ, Exponent]

end
end ECTheoryLib
