import ECTheoryLib.Probability.Concentration.FiniteAdditiveChernoff
import ECTheoryLib.Probability.Concentration.FiniteMGFCertificate

/-!
# Finite Chernoff upper tails with an estimated mean

Doerr Theorem 1.10.21(a), equation (1.10.41), and the logarithmic relaxation.
The estimate replaces both the event threshold and the bound parameter.
Existing MGF certificates and scalar optimization handle every boundary.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- A mean upper estimate preserves the finite MGF certificate at nonnegative tilts,
including an empty family. The estimate need not be at most n. -/
theorem UnitIndependentSumFiniteMGFOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (t : ℝ) (NonnegativeTilt : 0 ≤ t) :
    mgf (fun ω => ∑ i, X i ω) P t ≤
      (1 + (U / (n : ℝ)) * (Real.exp t - 1)) ^ n := by
  by_cases Empty : n = 0
  · subst n
    simp [mgf]
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  have ExpNonnegative : 0 ≤ Real.exp t - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr NonnegativeTilt)
  have BaseNonnegative : 0 ≤ 1 +
      ((∫ ω, ∑ i, X i ω ∂P) / (n : ℝ)) * (Real.exp t - 1) :=
    add_nonneg zero_le_one (mul_nonneg
      (div_nonneg MeanNonnegative (Nat.cast_nonneg n)) ExpNonnegative)
  exact (UnitIndependentSumFiniteMGFBound P (Nat.pos_of_ne_zero Empty) X
    MeasurableX Independent Bounded t).trans
    (pow_le_pow_left₀ BaseNonnegative
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right MeanUpper (Nat.cast_nonneg n)) ExpNonnegative)) n)

/-- Doerr (1.10.41): replace the mean in both the threshold and the finite expression.
The existing branches retain zero means, empty families, and estimates exceeding n. -/
theorem UnitIndependentSumFiniteChernoffUpperOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1 + d) * U ≤ ∑ i, X i ω} ≤ FiniteChernoffUpperBound n U d := by
  have SumFunction : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by
    funext ω
    exact Finset.sum_apply _ _ _
  have MeasurableSum : AEMeasurable (fun ω => ∑ i, X i ω) P := by
    rw [← SumFunction]
    exact Finset.aemeasurable_sum _ (fun i _ => MeasurableX i)
  have SumBounds : ∀ᵐ ω ∂P, (∑ i, X i ω) ∈ Icc 0 (n : ℝ) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    constructor
    · exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
    · calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _ = _ := by simp
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P :=
    integral_nonneg_of_ae (SumBounds.mono (fun _ Bound => Bound.1))
  have Endpoint : P.real {ω | (n : ℝ) ≤ ∑ i, X i ω} ≤ (U / (n : ℝ)) ^ n :=
    (UnitIndependentSumFiniteChernoffEndpoint P X MeasurableX Independent Bounded).trans
      (pow_le_pow_left₀ (div_nonneg MeanNonnegative (Nat.cast_nonneg n))
        (div_le_div_of_nonneg_right MeanUpper (Nat.cast_nonneg n)) n)
  exact FiniteMGFCertificateChernoffUpper P (fun ω => ∑ i, X i ω) n U
    MeasurableSum SumBounds
    (UnitIndependentSumFiniteMGFOfMeanLe P X MeasurableX Independent Bounded U MeanUpper)
    Endpoint (MeanNonnegative.trans MeanUpper) d Nonnegative

/-- The same mean estimate in the standard logarithmic-exponential upper bound. -/
theorem UnitIndependentSumChernoffUpperOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1 + d) * U ≤ ∑ i, X i ω} ≤
      Real.exp (-((1 + d) * Real.log (1 + d) - d) * U) := by
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  exact (UnitIndependentSumFiniteChernoffUpperOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper d Nonnegative).trans
    (FiniteChernoffUpperBoundLeExp n U d (MeanNonnegative.trans MeanUpper) Nonnegative)

end
end ECTheoryLib.Probability



/-! Power, quadratic and small-deviation consequences with a mean upper estimate. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Doerr (1.10.2) in power form with a mean upper estimate. -/
theorem UnitIndependentSumChernoffUpperPowerOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1 + d) * U ≤ ∑ i, X i ω} ≤
      (Real.exp d / (1 + d) ^ (1 + d)) ^ U := by
  rw [ChernoffPowerExpression d U Nonnegative]
  exact UnitIndependentSumChernoffUpperOfMeanLe P X MeasurableX Independent Bounded U MeanUpper d Nonnegative

/-- Doerr (1.10.3), with the exact denominator and an estimated mean. -/
theorem UnitIndependentSumChernoffUpperQuadraticOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1 + d) * U ≤ ∑ i, X i ω} ≤
      Real.exp (-(d ^ 2 * U) / (2 + 2 * d / 3)) := by
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  apply (UnitIndependentSumChernoffUpperOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper d Nonnegative).trans
  apply Real.exp_le_exp.mpr
  have ExponentBound := mul_le_mul_of_nonneg_right
    (ChernoffExponentQuadraticLower d Nonnegative) (MeanNonnegative.trans MeanUpper)
  rw [div_mul_eq_mul_div] at ExponentBound
  simpa only [neg_mul, neg_div] using neg_le_neg ExponentBound

/-- Doerr (1.10.4), covering small and large nonnegative deviations. -/
theorem UnitIndependentSumChernoffUpperMinOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1 + d) * U ≤ ∑ i, X i ω} ≤
      Real.exp (-(min (d ^ 2) d) * U / 3) := by
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  apply (UnitIndependentSumChernoffUpperQuadraticOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper d Nonnegative).trans
  apply Real.exp_le_exp.mpr
  have ExponentBound := mul_le_mul_of_nonneg_right
    (ChernoffQuadraticMinLower d Nonnegative) (MeanNonnegative.trans MeanUpper)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div] at ExponentBound
  simpa only [neg_mul, neg_div] using neg_le_neg ExponentBound

/-- Doerr (1.10.5) under 1.10.21(a), including both deviation endpoints. -/
theorem UnitIndependentSumChernoffUpperSmallOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    P.real {ω | (1 + d) * U ≤ ∑ i, X i ω} ≤ Real.exp (-(d ^ 2) * U / 3) := by
  have SquareLe : d ^ 2 ≤ d := by nlinarith [InUnit.1, InUnit.2]
  have Bound := UnitIndependentSumChernoffUpperMinOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper d InUnit.1
  rw [min_eq_left SquareLe] at Bound
  exact Bound

end
end ECTheoryLib.Probability



/-! Large-deviation powers and base-two tails with a mean upper estimate. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Equation (1.10.7) with the upper estimate in both threshold and bound. -/
theorem UnitIndependentSumChernoffUpperLargePowerOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1 + d) * U ≤ ∑ i, X i ω} ≤
      (Real.exp 1 / (1 + d)) ^ ((1 + d) * U) := by
  have EstimateNonnegative : 0 ≤ U := by
    apply le_trans (integral_nonneg_of_ae ?_) MeanUpper
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  have PositiveDenominator : 0 < 1 + d := by linarith
  apply (UnitIndependentSumChernoffUpperOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper d Nonnegative).trans
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos 1) PositiveDenominator),
    Real.log_div (Real.exp_pos 1).ne' PositiveDenominator.ne', Real.log_exp]
  apply Real.exp_le_exp.mpr
  calc
    -((1 + d) * Real.log (1 + d) - d) * U =
        (1 - Real.log (1 + d)) * ((1 + d) * U) - U := by ring
    _ ≤ _ := sub_le_self _ EstimateNonnegative

/-- Equation (1.10.8). At d=0 the totalized expression has exponent zero and
value one; no classical interpretation of division by zero is asserted. -/
theorem UnitIndependentSumChernoffUpperDeviationPowerOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1 + d) * U ≤ ∑ i, X i ω} ≤
      (Real.exp 1 / d) ^ (d * U) := by
  by_cases ZeroDeviation : d = 0
  · subst d
    simp only [zero_mul, Real.rpow_zero]
    exact measureReal_le_one
  have PositiveDeviation : 0 < d := lt_of_le_of_ne Nonnegative (Ne.symm ZeroDeviation)
  have EstimateNonnegative : 0 ≤ U := by
    apply le_trans (integral_nonneg_of_ae ?_) MeanUpper
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  have LogComparison : d * Real.log d ≤ (1 + d) * Real.log (1 + d) := by
    calc
      d * Real.log d ≤ d * Real.log (1 + d) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log PositiveDeviation (by linarith)) Nonnegative
      _ ≤ (1 + d) * Real.log (1 + d) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by linarith))
  have Weighted := mul_le_mul_of_nonneg_right LogComparison EstimateNonnegative
  apply (UnitIndependentSumChernoffUpperOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper d Nonnegative).trans
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos 1) PositiveDeviation),
    Real.log_div (Real.exp_pos 1).ne' PositiveDeviation.ne', Real.log_exp]
  apply Real.exp_le_exp.mpr
  nlinarith only [Weighted]

/-- Corollary 1.10.4 with a sufficient threshold computed from a mean estimate. -/
theorem UnitIndependentSumBaseTwoUpperTailOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (k : ℝ) (LargeThreshold : 2 * Real.exp 1 * U ≤ k) :
    P.real {ω | k ≤ ∑ i, X i ω} ≤ (2 : ℝ) ^ (-k) := by
  exact UnitIndependentSumBaseTwoUpperTail P X MeasurableX Independent Bounded k
    ((mul_le_mul_of_nonneg_left MeanUpper (by positivity)).trans LargeThreshold)

end
end ECTheoryLib.Probability



/-! Additive Chernoff upper tails with an estimate for the actual mean. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The estimated finite additive tail retains empty families, zero estimates
and estimates exceeding the dimension. -/
theorem UnitIndependentSumFiniteAdditiveChernoffUpperOfMeanLe {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | U + l ≤ ∑ i, X i ω} ≤ FiniteAdditiveChernoffUpperBound n U l := by
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  have EstimateNonnegative : 0 ≤ U := MeanNonnegative.trans MeanUpper
  by_cases ZeroEstimate : U = 0
  · subst U
    have ZeroMean : (∫ ω, ∑ i, X i ω ∂P) = 0 :=
      le_antisymm MeanUpper MeanNonnegative
    have Tail := UnitSumZeroMeanUpper P X MeasurableX Bounded ZeroMean l Nonnegative
    rw [ZeroMean, zero_add] at Tail
    rw [zero_add, Tail, FiniteAdditiveChernoffZeroMean n l Nonnegative]
  have PositiveEstimate : 0 < U := lt_of_le_of_ne EstimateNonnegative (Ne.symm ZeroEstimate)
  have Threshold : (1 + l / U) * U = U + l := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ PositiveEstimate.ne']
  have Bound := UnitIndependentSumFiniteChernoffUpperOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper (l / U) (div_nonneg Nonnegative EstimateNonnegative)
  rw [Threshold, ← FiniteAdditiveChernoffEqRelative n U l PositiveEstimate Nonnegative] at Bound
  exact Bound

/-- The source power form extends to U=0 using the existing zero-base convention. -/
theorem UnitIndependentSumAdditiveChernoffUpperPowerOfMeanLe {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | U + l ≤ ∑ i, X i ω} ≤ Real.exp l * (U / (U + l)) ^ (U + l) := by
  have EstimateNonnegative : 0 ≤ U := by
    apply le_trans (integral_nonneg_of_ae ?_) MeanUpper
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  exact (UnitIndependentSumFiniteAdditiveChernoffUpperOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper l Nonnegative).trans
    (FiniteAdditiveChernoffLePower n U l EstimateNonnegative Nonnegative)

/-- Only the estimate must be positive for the logarithmic identity; the true
mean may be zero. No logarithmic identity at U=0 is asserted. -/
theorem UnitIndependentSumAdditiveChernoffUpperOfMeanLe {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U) (PositiveEstimate : 0 < U)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | U + l ≤ ∑ i, X i ω} ≤ Real.exp (-(U + l) * Real.log (1 + l / U) + l) := by
  rw [← AdditiveChernoffPowerExpression U l PositiveEstimate Nonnegative]
  exact UnitIndependentSumAdditiveChernoffUpperPowerOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper l Nonnegative

/-- The exact quadratic denominator is 2U+2l/3, including zero estimates. -/
theorem UnitIndependentSumAdditiveChernoffUpperQuadraticOfMeanLe {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | U + l ≤ ∑ i, X i ω} ≤ Real.exp (-(l ^ 2) / (2 * U + 2 * l / 3)) := by
  have EstimateNonnegative : 0 ≤ U := by
    apply le_trans (integral_nonneg_of_ae ?_) MeanUpper
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  exact (UnitIndependentSumAdditiveChernoffUpperPowerOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper l Nonnegative).trans
    (AdditiveChernoffPowerLeQuadratic U l EstimateNonnegative Nonnegative)

/-- At U=0, total division gives the valid but potentially weaker minimum bound1. -/
theorem UnitIndependentSumAdditiveChernoffUpperMinOfMeanLe {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | U + l ≤ ∑ i, X i ω} ≤ Real.exp (-(min (l ^ 2 / U) l) / 3) := by
  have EstimateNonnegative : 0 ≤ U := by
    apply le_trans (integral_nonneg_of_ae ?_) MeanUpper
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  exact (UnitIndependentSumAdditiveChernoffUpperQuadraticOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper l Nonnegative).trans
    (AdditiveChernoffQuadraticLeMin U l EstimateNonnegative Nonnegative)

/-- The small-deviation restriction is l<=U, not the stronger l<=true mean. -/
theorem UnitIndependentSumAdditiveChernoffUpperSmallOfMeanLe {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (l : ℝ) (Nonnegative : 0 ≤ l) (Small : l ≤ U) :
    P.real {ω | U + l ≤ ∑ i, X i ω} ≤ Real.exp (-(l ^ 2) / (3 * U)) := by
  rw [← AdditiveChernoffMinEqSmall U l Nonnegative Small]
  exact UnitIndependentSumAdditiveChernoffUpperMinOfMeanLe P X MeasurableX Independent
    Bounded U MeanUpper l Nonnegative

end
end ECTheoryLib.Probability

