import ECTheoryLib.Operators.Mutation.IndependentBit
import ECTheoryLib.Operators.Mutation.BitFlip
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact single-bit event probabilities for the existing independent mutation.
The scalar inverse bound reuses the argument in the user's OneMax/Constants.lean;
all probabilities here refer directly to the formal library's PMF. -/
namespace ECTheoryLib
noncomputable section

/-- Different flipped coordinates produce different offspring. -/
theorem OnebitMutationInjective {n : Nat} (x : Bits n) :
    Function.Injective (OnebitMutation x) := by
  intro i j EqualOffspring
  by_contra Different
  have EqualBit := congrFun EqualOffspring i
  rw [OnebitMutationAt, OnebitMutationAway x j i Different] at EqualBit
  cases Bit : x i with
  | false => simp only [Bit, Bool.not_false] at EqualBit; cases EqualBit
  | true => simp only [Bit, Bool.not_true] at EqualBit; cases EqualBit

/-- Probability of flipping one specified coordinate and leaving all others unchanged. -/
def StandardOneBitProbability (n : Nat) : ℝ :=
  (1 / (n : ℝ)) * (1 - 1 / (n : ℝ)) ^ (n - 1)

theorem StandardOneBitProbabilityPositive {n : Nat} (hn : 0 < n) :
    0 < StandardOneBitProbability n := by
  by_cases One : n = 1
  · subst n
    norm_num [StandardOneBitProbability]
  · have AtLeastTwo : 2 ≤ n := by omega
    have LargerThanOne : (1 : ℝ) < n := by exact_mod_cast AtLeastTwo
    have Positive : (0 : ℝ) < n := by exact_mod_cast hn
    exact mul_pos (one_div_pos.mpr Positive)
      (pow_pos (sub_pos.mpr ((div_lt_one Positive).mpr LargerThanOne)) _)

/-- The standard one-bit probability has reciprocal at most e n, including n=1. -/
theorem StandardOneBitProbabilityInverseBound {n : Nat} (hn : 0 < n) :
    1 / StandardOneBitProbability n ≤ Real.exp 1 * (n : ℝ) := by
  have InverseFormula : 1 / StandardOneBitProbability n =
      (n : ℝ) * (1 + ((n - 1 : Nat) : ℝ)⁻¹) ^ (n - 1) := by
    by_cases One : n = 1
    · subst n
      norm_num [StandardOneBitProbability]
    · have AtLeastTwo : 2 ≤ n := by omega
      have Positive : (0 : ℝ) < n := by exact_mod_cast hn
      have PositiveSub : (0 : ℝ) < (n : ℝ) - 1 := by
        have RealAtLeastTwo : (2 : ℝ) ≤ n := by exact_mod_cast AtLeastTwo
        linarith
      have Base : (1 - 1 / (n : ℝ))⁻¹ = 1 + ((n - 1 : Nat) : ℝ)⁻¹ := by
        rw [Nat.cast_sub hn, Nat.cast_one]
        have LengthNonzero := ne_of_gt Positive
        have SubNonzero := ne_of_gt PositiveSub
        field_simp
        ring
      simp only [StandardOneBitProbability, one_div, mul_inv_rev, inv_inv, ← inv_pow]
      simp only [one_div] at Base
      rw [Base]
      ring
  rw [InverseFormula]
  have PowerBound := Real.one_add_inv_pow_le_exp (n := n - 1)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left PowerBound (Nat.cast_nonneg n)

/-- Exact PMF mass of the existing one-coordinate flip. -/
theorem StandardBitMutationOneBit {n : Nat} (hn : 0 < n) (x : Bits n) (i : Fin n) :
    StandardBitMutation hn x (OnebitMutation x i) =
      (n : ENNReal)⁻¹ * (1 - (n : ENNReal)⁻¹) ^ (n - 1) := by
  rw [StandardBitMutationProbability,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have Changed : OnebitMutation x i i ≠ x i := by
    rw [OnebitMutationAt]
    cases x i with
    | false => decide
    | true => decide
  rw [if_neg Changed]
  congr 1
  calc
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      if OnebitMutation x i j = x j then 1 - (n : ENNReal)⁻¹ else (n : ENNReal)⁻¹) =
        ∏ _j ∈ (Finset.univ : Finset (Fin n)).erase i, (1 - (n : ENNReal)⁻¹) := by
      apply Finset.prod_congr rfl
      intro j InErase
      rw [OnebitMutationAway x i j (Finset.mem_erase.mp InErase).1, if_pos rfl]
    _ = (1 - (n : ENNReal)⁻¹) ^ (n - 1) := by simp

/-- The exact event mass expressed as an ordinary real probability. -/
theorem StandardBitMutationOneBitReal {n : Nat} (hn : 0 < n) (x : Bits n) (i : Fin n) :
    (StandardBitMutation hn x (OnebitMutation x i)).toReal = StandardOneBitProbability n := by
  rw [StandardBitMutationOneBit, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le (StandardBitMutationRateBound n hn) ENNReal.one_ne_top]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one,
    StandardOneBitProbability, one_div]

end
end ECTheoryLib
