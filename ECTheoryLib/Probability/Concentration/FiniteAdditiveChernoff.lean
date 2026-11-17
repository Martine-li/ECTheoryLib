import ECTheoryLib.Probability.Concentration.FiniteChernoff
import ECTheoryLib.Probability.Concentration.AdditiveChernoff

/-!
# Finite additive Chernoff bounds and their scalar comparisons

Doerr Theorem 1.10.10, equations (1.10.17)-(1.10.21). The finite
expression uses the source's maximum-threshold and beyond-maximum branches.
The power-form comparison chain includes zero mean and empty families;
the raw logarithmic identity remains restricted to positive mean by
AdditiveChernoffPowerExpression. Total division makes the zero-mean min
bound one. No MGF or exponent estimate is reproved here.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Equation (1.10.17), including the two boundary conventions stated in
the source. The endpoint exponent is natural; in particular 0^0=1. -/
def FiniteAdditiveChernoffUpperBound (n : ℕ) (m l : ℝ) : ℝ :=
  if (n : ℝ) < m + l then 0
  else if m + l = (n : ℝ) then (m / (n : ℝ)) ^ n
  else (m / (m + l)) ^ (m + l) *
    (((n : ℝ) - m) / ((n : ℝ) - m - l)) ^ ((n : ℝ) - m - l)

/-- The finite expression has the exact zero-mean tail values, including
the intersection of the empty-family and zero-deviation endpoints. -/
theorem FiniteAdditiveChernoffZeroMean (n : ℕ) (l : ℝ) (Nonnegative : 0 ≤ l) :
    FiniteAdditiveChernoffUpperBound n 0 l = if l = 0 then 1 else 0 := by
  by_cases ZeroDeviation : l = 0
  · subst l
    by_cases Empty : n = 0
    · simp [FiniteAdditiveChernoffUpperBound, Empty]
    · have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero Empty)
      simp [FiniteAdditiveChernoffUpperBound, PositiveN.ne', Ne.symm PositiveN.ne',
        not_lt.mpr PositiveN.le]
  · simp only [FiniteAdditiveChernoffUpperBound, zero_add, zero_div, sub_zero,
      if_neg ZeroDeviation]
    split_ifs with Beyond Endpoint
    · rfl
    · have Nonempty : n ≠ 0 := by
        intro Empty
        simp only [Empty, Nat.cast_zero] at Endpoint
        exact ZeroDeviation Endpoint
      exact zero_pow Nonempty
    · rw [Real.zero_rpow ZeroDeviation, zero_mul]

/-- Positive mean permits the relative parameter l/m. This bridge keeps
the existing finite-size proof and all its endpoint cases unchanged. -/
theorem FiniteAdditiveChernoffEqRelative (n : ℕ) (m l : ℝ)
    (PositiveMean : 0 < m) (Nonnegative : 0 ≤ l) :
    FiniteAdditiveChernoffUpperBound n m l = FiniteChernoffUpperBound n m (l / m) := by
  have Threshold : (1 + l / m) * m = m + l := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
  have PositiveThreshold : 0 < m + l := add_pos_of_pos_of_nonneg PositiveMean Nonnegative
  have Ratio : m / (m + l) = 1 / (1 + l / m) := by field_simp
  simp only [FiniteAdditiveChernoffUpperBound, FiniteChernoffUpperBound, Threshold, Ratio,
    sub_add_eq_sub_sub]

/-- Equation (1.10.17) for the actual mean of independent [0,1] variables,
with no positive-mean, positive-length or interior-threshold premise. -/
theorem UnitIndependentSumFiniteAdditiveChernoffUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} ≤
      FiniteAdditiveChernoffUpperBound n (∫ w, ∑ i, X i w ∂P) l := by
  let m := ∫ w, ∑ i, X i w ∂P
  have MeanNonnegative : 0 ≤ m := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  by_cases ZeroMean : m = 0
  · rw [UnitSumZeroMeanUpper P X MeasurableX Bounded ZeroMean l Nonnegative]
    change _ ≤ FiniteAdditiveChernoffUpperBound n m l
    rw [ZeroMean, FiniteAdditiveChernoffZeroMean n l Nonnegative]
  · have PositiveMean : 0 < m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
    have Threshold : (1 + l / m) * m = m + l := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
    have Bound := UnitIndependentSumFiniteChernoffUpper P X MeasurableX Independent Bounded
      (l / m) (div_nonneg Nonnegative MeanNonnegative)
    change P.real {ω | (1 + l / m) * m ≤ ∑ i, X i ω} ≤ FiniteChernoffUpperBound n m (l / m) at Bound
    rw [Threshold, ← FiniteAdditiveChernoffEqRelative n m l PositiveMean Nonnegative] at Bound
    exact Bound

/-- The finite expression is bounded by the power expression (1.10.18).
At zero mean the two expressions agree exactly, so no raw log(1+l/m)
identity at zero is used. The scalar result also holds when m exceeds n,
where the finite expression is zero. -/
theorem FiniteAdditiveChernoffLePower (n : ℕ) (m l : ℝ)
    (NonnegativeMean : 0 ≤ m) (Nonnegative : 0 ≤ l) :
    FiniteAdditiveChernoffUpperBound n m l ≤ Real.exp l * (m / (m + l)) ^ (m + l) := by
  by_cases ZeroMean : m = 0
  · subst m
    rw [FiniteAdditiveChernoffZeroMean n l Nonnegative]
    by_cases ZeroDeviation : l = 0
    · simp [ZeroDeviation]
    · simp [ZeroDeviation, Real.zero_rpow ZeroDeviation]
  · have PositiveMean : 0 < m := lt_of_le_of_ne NonnegativeMean (Ne.symm ZeroMean)
    rw [FiniteAdditiveChernoffEqRelative n m l PositiveMean Nonnegative,
      AdditiveChernoffPowerExpression m l PositiveMean Nonnegative]
    have Bound := FiniteChernoffUpperBoundLeExp n m (l / m) NonnegativeMean
      (div_nonneg Nonnegative NonnegativeMean)
    have Threshold : (1 + l / m) * m = m + l := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
    have Exponent : -((1 + l / m) * Real.log (1 + l / m) - l / m) * m =
        -(m + l) * Real.log (1 + l / m) + l := by
      calc
        _ = -((1 + l / m) * m) * Real.log (1 + l / m) + (l / m) * m := by ring
        _ = _ := by rw [Threshold, div_mul_cancel₀ _ PositiveMean.ne']
    simpa only [Exponent] using Bound

/-- Scalar comparison (1.10.18) <= (1.10.19), using the power form to
include zero mean under the explicitly documented total-division convention. -/
theorem AdditiveChernoffPowerLeQuadratic (m l : ℝ)
    (NonnegativeMean : 0 ≤ m) (Nonnegative : 0 ≤ l) :
    Real.exp l * (m / (m + l)) ^ (m + l) ≤
      Real.exp (-(l ^ 2) / (2 * m + 2 * l / 3)) := by
  by_cases ZeroMean : m = 0
  · subst m
    by_cases ZeroDeviation : l = 0
    · simp [ZeroDeviation]
    · simp only [zero_add, zero_div, Real.zero_rpow ZeroDeviation, mul_zero]
      exact (Real.exp_pos _).le
  · have PositiveMean : 0 < m := lt_of_le_of_ne NonnegativeMean (Ne.symm ZeroMean)
    rw [AdditiveChernoffPowerExpression m l PositiveMean Nonnegative]
    apply Real.exp_le_exp.mpr
    have Bound := mul_le_mul_of_nonneg_right
      (ChernoffExponentQuadraticLower (l / m) (div_nonneg Nonnegative NonnegativeMean)) NonnegativeMean
    have Denominator : 0 < 2 * m + 2 * l / 3 := by positivity
    have Rational : (l / m) ^ 2 / (2 + 2 * (l / m) / 3) * m =
        l ^ 2 / (2 * m + 2 * l / 3) := by field_simp
    have Threshold : (1 + l / m) * m = m + l := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
    have Exponent : ((1 + l / m) * Real.log (1 + l / m) - l / m) * m =
        (m + l) * Real.log (1 + l / m) - l := by
      calc
        _ = ((1 + l / m) * m) * Real.log (1 + l / m) - (l / m) * m := by ring
        _ = _ := by rw [Threshold, div_mul_cancel₀ _ PositiveMean.ne']
    rw [Rational, Exponent] at Bound
    rw [neg_div]
    linarith

/-- Scalar comparison (1.10.19) <= (1.10.20). At zero mean total division
gives a right-hand side of one; the inequality still holds. -/
theorem AdditiveChernoffQuadraticLeMin (m l : ℝ)
    (NonnegativeMean : 0 ≤ m) (Nonnegative : 0 ≤ l) :
    Real.exp (-(l ^ 2) / (2 * m + 2 * l / 3)) ≤
      Real.exp (-(min (l ^ 2 / m) l) / 3) := by
  apply Real.exp_le_exp.mpr
  by_cases ZeroMean : m = 0
  · simp only [ZeroMean, mul_zero, zero_add, div_zero, min_eq_left Nonnegative, neg_zero, zero_div]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg l)) (by positivity)
  · have PositiveMean : 0 < m := lt_of_le_of_ne NonnegativeMean (Ne.symm ZeroMean)
    have Bound := mul_le_mul_of_nonneg_right
      (ChernoffQuadraticMinLower (l / m) (div_nonneg Nonnegative NonnegativeMean)) NonnegativeMean
    have Denominator : 0 < 2 * m + 2 * l / 3 := by positivity
    have Rational : (l / m) ^ 2 / (2 + 2 * (l / m) / 3) * m =
        l ^ 2 / (2 * m + 2 * l / 3) := by field_simp
    have Product : min ((l / m) ^ 2) (l / m) * m = min (l ^ 2 / m) l := by
      rw [min_mul_of_nonneg _ _ NonnegativeMean, div_mul_cancel₀ _ PositiveMean.ne']
      congr 1
      field_simp
    rw [Rational, div_mul_eq_mul_div, Product] at Bound
    simpa only [neg_div] using neg_le_neg Bound

/-- For l <= m the minimum bound is exactly the small-deviation expression
(1.10.21), including m=l=0. -/
theorem AdditiveChernoffMinEqSmall (m l : ℝ)
    (Nonnegative : 0 ≤ l) (SmallDeviation : l ≤ m) :
    Real.exp (-(min (l ^ 2 / m) l) / 3) = Real.exp (-(l ^ 2) / (3 * m)) := by
  have MeanNonnegative : 0 ≤ m := Nonnegative.trans SmallDeviation
  by_cases ZeroMean : m = 0
  · simp [ZeroMean, min_eq_left Nonnegative]
  · have PositiveMean : 0 < m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
    have SquareLe : l ^ 2 / m ≤ l := by
      apply (div_le_iff₀ PositiveMean).mpr
      nlinarith
    rw [min_eq_left SquareLe]
    congr 1
    field_simp

end
end ECTheoryLib.Probability

