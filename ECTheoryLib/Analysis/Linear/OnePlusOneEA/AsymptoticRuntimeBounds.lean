import ECTheoryLib.Analysis.Linear.OnePlusOneEA.RuntimeUpperBounds
import Mathlib.Analysis.Asymptotics.Defs

/- Actual original standard minimizing EA: finite-real and asymptotic consequences.
The family parameter k has actual dimension k+1. -/
noncomputable section
open Filter Asymptotics

namespace ECTheoryLib.Analysis.EALinearMinimization

/-- A common upper constant independent of weights, weight ratios and initialization. -/
def RankLogRuntimeConstant : ℝ :=
  4 * Real.exp 1 * (1 + (1 + Real.log 2) / Real.log 2)

theorem RankLogRuntimeConstantPositive : 0 < RankLogRuntimeConstant := by
  have LogTwoPositive : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold RankLogRuntimeConstant
  positivity

private theorem RankLogComparison {x : ℝ} (TwoLe : 2 ≤ x) :
    1 + Real.log (2 * x) ≤ (1 + (1 + Real.log 2) / Real.log 2) * Real.log x := by
  have LogTwoPositive : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have XPositive : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) TwoLe
  have LogTwoLe : Real.log (2 : ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) TwoLe
  have FactorNonnegative : 0 ≤ (1 + Real.log (2 : ℝ)) / Real.log 2 := by positivity
  have Lift := mul_le_mul_of_nonneg_left LogTwoLe FactorNonnegative
  have Cancel : ((1 + Real.log (2 : ℝ)) / Real.log 2) * Real.log 2 = 1 + Real.log 2 :=
    div_mul_cancel₀ _ (ne_of_gt LogTwoPositive)
  rw [Cancel] at Lift
  calc
    1 + Real.log (2 * x) = (1 + Real.log 2) + Real.log x := by
      rw [Real.log_mul (by norm_num) (ne_of_gt XPositive)]
      ring
    _ ≤ ((1 + Real.log 2) / Real.log 2) * Real.log x + Real.log x := by linarith
    _ = (1 + (1 + Real.log 2) / Real.log 2) * Real.log x := by ring

/-- The upper finite-real mean uses the existing finiteness theorem before toReal. -/
theorem RankLogRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) (AtLeastTwo : 2 ≤ n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Initial : PMF (Bits n)) :
    (ExpectedRuntime PositiveLength Weights Initial).toReal ≤
      RankLogRuntimeConstant * (n : ℝ) * Real.log (n : ℝ) := by
  have Finite : ExpectedRuntime PositiveLength Weights Initial ≠ ⊤ :=
    ne_of_lt (PositiveLinearExpectedRuntimeFinite PositiveLength Weights Positive Initial)
  have TwoN : (2 : ℝ) ≤ n := by exact_mod_cast AtLeastTwo
  have NNonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have LogNonnegative : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have BoundNonnegative : 0 ≤ (4 * Real.exp 1 * (n : ℝ)) * (1 + Real.log (2 * (n : ℝ))) := by
    positivity
  have Converted := (ENNReal.toReal_le_toReal Finite ENNReal.ofReal_ne_top).mpr
    (RankRuntimeUpperBound PositiveLength Weights Positive Initial)
  rw [ENNReal.toReal_ofReal BoundNonnegative] at Converted
  have LogBound := RankLogComparison TwoN
  calc
    _ ≤ (4 * Real.exp 1 * (n : ℝ)) * (1 + Real.log (2 * (n : ℝ))) := Converted
    _ ≤ (4 * Real.exp 1 * (n : ℝ)) *
        ((1 + (1 + Real.log 2) / Real.log 2) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left LogBound (by positivity)
    _ = RankLogRuntimeConstant * (n : ℝ) * Real.log (n : ℝ) := by
      unfold RankLogRuntimeConstant
      ring

/-- The matching real lower uses the original actual uniform initialization. -/
theorem UniformRankLogRuntimeLower {n : ℕ} (PositiveLength : 0 < n) (AtLeastTwo : 2 ≤ n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) :
    (n : ℝ) * Real.log (n : ℝ) / 96 ≤
      (ExpectedRuntime PositiveLength Weights (OnePlusOneEAInit n)).toReal := by
  have Finite : ExpectedRuntime PositiveLength Weights (OnePlusOneEAInit n) ≠ ⊤ :=
    ne_of_lt (PositiveLinearExpectedRuntimeFinite PositiveLength Weights Positive (OnePlusOneEAInit n))
  have TwoN : (2 : ℝ) ≤ n := by exact_mod_cast AtLeastTwo
  have NNonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have LogNonnegative : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have LowerNonnegative : 0 ≤ (n : ℝ) * (1 + Real.log (n : ℝ)) / 96 := by positivity
  have Converted := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top Finite).mpr
    (UniformRuntimeLower PositiveLength Weights Positive)
  rw [ENNReal.toReal_ofReal LowerNonnegative] at Converted
  calc
    _ ≤ (n : ℝ) * (1 + Real.log (n : ℝ)) / 96 := by nlinarith
    _ ≤ _ := Converted

/-- Explicit common constants retain the uniformity that familywise Theta alone omits. -/
theorem UniformRankLogRuntimeBounds {n : ℕ} (PositiveLength : 0 < n) (AtLeastTwo : 2 ≤ n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) :
    (n : ℝ) * Real.log (n : ℝ) / 96 ≤
        (ExpectedRuntime PositiveLength Weights (OnePlusOneEAInit n)).toReal ∧
      (ExpectedRuntime PositiveLength Weights (OnePlusOneEAInit n)).toReal ≤
        RankLogRuntimeConstant * (n : ℝ) * Real.log (n : ℝ) :=
  ⟨UniformRankLogRuntimeLower PositiveLength AtLeastTwo Weights Positive,
    RankLogRuntimeUpper PositiveLength AtLeastTwo Weights Positive (OnePlusOneEAInit n)⟩

/-- Arbitrary initial families have the upper asymptotic on the actual shifted dimensions. -/
theorem RankRuntimeFamilyIsBigO (Weights : (k : ℕ) → Fin (k + 1) → ℝ)
    (Positive : ∀ k i, 0 < Weights k i) (Initial : (k : ℕ) → PMF (Bits (k + 1))) :
    (fun k => (ExpectedRuntime (Nat.succ_pos k) (Weights k) (Initial k)).toReal) =O[atTop]
      (fun k => ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨RankLogRuntimeConstant, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k AtLeastOne
  have AtLeastTwo : 2 ≤ k + 1 := by omega
  have MeanNonnegative : 0 ≤ (ExpectedRuntime (Nat.succ_pos k) (Weights k) (Initial k)).toReal :=
    ENNReal.toReal_nonneg
  have ComparisonNonnegative : 0 ≤ ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.succ_pos k)))
  rw [Real.norm_eq_abs, abs_of_nonneg MeanNonnegative, Real.norm_eq_abs, abs_of_nonneg ComparisonNonnegative]
  simpa only [mul_assoc] using
    RankLogRuntimeUpper (Nat.succ_pos k) AtLeastTwo (Weights k) (Positive k) (Initial k)

/-- Matching lower and upper apply to the same actual uniform-initial EA family. -/
theorem UniformRankRuntimeFamilyIsTheta (Weights : (k : ℕ) → Fin (k + 1) → ℝ)
    (Positive : ∀ k i, 0 < Weights k i) :
    (fun k => (ExpectedRuntime (Nat.succ_pos k) (Weights k) (OnePlusOneEAInit (k + 1))).toReal) =Θ[atTop]
      (fun k => ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ)) := by
  refine (RankRuntimeFamilyIsBigO Weights Positive (fun k => OnePlusOneEAInit (k + 1))).antisymm ?_
  refine Asymptotics.isBigO_iff.mpr ⟨96, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k AtLeastOne
  have AtLeastTwo : 2 ≤ k + 1 := by omega
  have Lower := UniformRankLogRuntimeLower (Nat.succ_pos k) AtLeastTwo (Weights k) (Positive k)
  have MeanNonnegative : 0 ≤ (ExpectedRuntime (Nat.succ_pos k) (Weights k) (OnePlusOneEAInit (k + 1))).toReal :=
    ENNReal.toReal_nonneg
  have ComparisonNonnegative : 0 ≤ ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.succ_pos k)))
  rw [Real.norm_eq_abs, abs_of_nonneg ComparisonNonnegative, Real.norm_eq_abs, abs_of_nonneg MeanNonnegative]
  nlinarith

end ECTheoryLib.Analysis.EALinearMinimization

