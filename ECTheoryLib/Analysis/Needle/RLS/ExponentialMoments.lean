import ECTheoryLib.Analysis.Needle.RLS.Model
import ECTheoryLib.Analysis.OneMax.BitFlip
import ECTheoryLib.Probability.PMF.FinitePMF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual exponential moments for the Needle plateau

A uniform one-bit proposal decreases distance with probability V/n and
increases it otherwise. Exact moments verify separate interior and
entrance bounds for a barrier of width n/4.
-/

namespace ECTheoryLib.Analysis.RLSOnNeedle
open MeasureTheory ECTheoryLib.Probability
noncomputable section

theorem MutationPotentialIncrement {n : ℕ} (x : Bits n) (i : Fin n) :
    Potential (OnebitMutation x i) - Potential x = if x i then 1 else -1 := by
  unfold Potential
  rw [Problems.OneMax.ZeroCountAsRealDifference, Problems.OneMax.ZeroCountAsRealDifference]
  cases Bit : x i with
  | false =>
    rw [OneMax.OneMaxMutationAtZero x i Bit, Nat.cast_add, Nat.cast_one]
    change (n : ℝ)-((OneMax x : ℝ)+1)-((n : ℝ)-(OneMax x : ℝ)) = -1
    ring
  | true =>
    have Identity : (OneMax (OnebitMutation x i) : ℝ)+1=(OneMax x : ℝ) := by
      exact_mod_cast OneMax.OneMaxMutationAtOne x i Bit
    change (n : ℝ)-(OneMax (OnebitMutation x i) : ℝ)-((n : ℝ)-(OneMax x : ℝ))=1
    linarith

theorem UpdateJumpLowerBound {n : ℕ} (x : Bits n) (i : Fin n) :
    Potential x - 1 ≤ Potential (Update x i) := by
  by_cases Target : IsTarget x
  · rw [UpdateAtTarget x i Target]
    linarith
  · rw [UpdateAway x i Target]
    have Jump := MutationPotentialIncrement x i
    cases Bit : x i with
    | false => rw [Bit] at Jump; change Potential (OnebitMutation x i)-Potential x = -1 at Jump; linarith
    | true => rw [Bit] at Jump; change Potential (OnebitMutation x i)-Potential x = 1 at Jump; linarith

/-- Exact exponential moment on the plateau, including improving moves into the target. -/
theorem OneStepExponentialMoment {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Away : ¬ IsTarget x) (Lambda : ℝ) :
    (∫ y, Real.exp (-Lambda*(Potential y-Potential x)) ∂(Step PositiveLength x).toMeasure) =
      Real.exp (-Lambda)+(Real.exp Lambda-Real.exp (-Lambda))*Potential x/(n : ℝ) := by
  classical
  have Each (i : Fin n) : Real.exp (-Lambda*(Potential (Update x i)-Potential x)) =
      Real.exp (-Lambda)+(Real.exp Lambda-Real.exp (-Lambda))*(if x i then 0 else 1) := by
    rw [UpdateAway x i Away, MutationPotentialIncrement]
    cases x i with
    | false =>
      change Real.exp (-Lambda*(-1)) = Real.exp (-Lambda)+(Real.exp Lambda-Real.exp (-Lambda))*1
      rw [mul_neg_one, neg_neg, mul_one]
      ring
    | true =>
      change Real.exp (-Lambda*1) = Real.exp (-Lambda)+(Real.exp Lambda-Real.exp (-Lambda))*0
      rw [mul_one, mul_zero, add_zero]
  rw [Step, RLSStepEqUniformUpdate, PMFIntegralMap, PMF.integral_eq_sum]
  simp only [smul_eq_mul, UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  change (n : ℝ)⁻¹ * (∑ i : Fin n, Real.exp (-Lambda*(Potential (Update x i)-Potential x))) = _
  simp_rw [Each]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Problems.OneMax.ZeroBitCountAsReal,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have Nonzero : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr PositiveLength).ne'
  change (n : ℝ)⁻¹*((n : ℝ)*Real.exp (-Lambda)+
    (Real.exp Lambda-Real.exp (-Lambda))*Potential x)=_
  field_simp

/-- The interior of the barrier is n/4 wide; lambda = log 2 makes the
exponential moment at most 7/8, hence at most one. -/
theorem InteriorExponentialMoment {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Above : 0 < Potential x) (Below : Potential x < (n : ℝ)/4) :
    (∫ y, Real.exp (-Real.log 2*(Potential y-Potential x)) ∂(Step PositiveLength x).toMeasure) ≤ 1 := by
  have Away : ¬ IsTarget x := fun Target => by
    have Zero := (PotentialEqZeroIffTarget x).mpr Target
    linarith
  rw [OneStepExponentialMoment PositiveLength x Away, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ)<2)]
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have Form : ((2 : ℝ)⁻¹+(2-2⁻¹)*Potential x/(n : ℝ)) =
      ((n : ℝ)/2+(3/2)*Potential x)/(n : ℝ) := by field_simp; ring
  rw [Form]
  apply (div_le_one PositiveN).mpr
  nlinarith

theorem EntranceExponentialMoment {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Above : (n : ℝ)/4 ≤ Potential x) :
    (∫ y, Real.exp (-Real.log 2*(Potential y-(n : ℝ)/4)) ∂(Step PositiveLength x).toMeasure) ≤ 2 := by
  have LogNonnegative : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have UpdateBound (i : Fin n) :
      Real.exp (-Real.log 2*(Potential (Update x i)-(n : ℝ)/4)) ≤ 2 := by
    have Jump := UpdateJumpLowerBound x i
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ = 2 := Real.exp_log (by norm_num)
  rw [Step, RLSStepEqUniformUpdate, PMFIntegralMap]
  have Bound := integral_mono_ae (Integrable.of_finite
    (μ := (UniformBitIndex n PositiveLength).toMeasure)
    (f := fun i => Real.exp (-Real.log 2*(Potential (Update x i)-(n : ℝ)/4))))
    (integrable_const (2 : ℝ)) (ae_of_all _ UpdateBound)
  rw [integral_const, probReal_univ, one_smul] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnNeedle
