import ECTheoryLib.Probability.Concentration.Chernoff
import Mathlib.Tactic.FieldSimp

/-!
# Additive Chernoff upper tails and zero means

Doerr Theorem 1.10.10, equations (1.10.18)-(1.10.21).
The logarithmic and power forms require positive mean. The quadratic, minimum
and small-deviation bounds include zero mean and empty families. All events
are closed. The finite-size expression (1.10.17) is provided by `FiniteAdditiveChernoff.lean`.
The proof reuses multiplicative bounds; it does not repeat MGF optimization.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- A nonnegative unit-interval sum with zero mean has an exact closed upper
tail: probability one at zero deviation, and zero at positive deviation.
Independence is not needed for this boundary statement. -/
theorem UnitSumZeroMeanUpper {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (ZeroMean : (∫ w, ∑ i, X i w ∂P) = 0) (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} =
      if l = 0 then 1 else 0 := by
  have IntegrableSum := integrable_finsetSum Finset.univ
    (fun i _ => Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i))
  have NonnegativeSum : 0 ≤ᵐ[P] (fun ω => ∑ i, X i ω) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  have ZeroSum := (integral_eq_zero_iff_of_nonneg_ae NonnegativeSum IntegrableSum).mp ZeroMean
  by_cases ZeroDeviation : l = 0
  · have Event : {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} =ᵐ[P] univ := by
      filter_upwards [ZeroSum] with ω Zero
      change (∑ i, X i ω) = 0 at Zero
      apply propext
      change ((∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω) ↔ True
      simp only [ZeroMean, ZeroDeviation, add_zero, Zero, le_refl]
    rw [Measure.real, measure_congr Event]
    simp [ZeroDeviation]
  · have PositiveDeviation : 0 < l := lt_of_le_of_ne Nonnegative (Ne.symm ZeroDeviation)
    have Null : P {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ZeroSum] with ω Zero
      change (∑ i, X i ω) = 0 at Zero
      simpa only [mem_ofPred_eq, ZeroMean, zero_add, Zero] using not_le.mpr PositiveDeviation
    rw [Measure.real, Null, ENNReal.toReal_zero, if_neg ZeroDeviation]

/-- The two expressions in Doerr (1.10.18) agree on their classical domain.
Positive mean is essential: mechanically using total division at zero does
not preserve the displayed logarithmic identity. -/
theorem AdditiveChernoffPowerExpression (m l : ℝ) (PositiveMean : 0 < m)
    (Nonnegative : 0 ≤ l) :
    Real.exp l * (m / (m + l)) ^ (m + l) =
      Real.exp (-(m + l) * Real.log (1 + l / m) + l) := by
  have PositiveThreshold : 0 < m + l := add_pos_of_pos_of_nonneg PositiveMean Nonnegative
  have PositiveBase : 0 < 1 + l / m := by positivity
  have Ratio : m / (m + l) = 1 / (1 + l / m) := by
    field_simp
  rw [Ratio, Real.rpow_def_of_pos (div_pos zero_lt_one PositiveBase),
    ← Real.exp_add, Real.log_div one_ne_zero PositiveBase.ne', Real.log_one]
  congr 1
  ring

/-- Doerr (1.10.18), logarithmic form for positive mean, by reparameterizing
the existing multiplicative upper bound. -/
theorem UnitIndependentSumAdditiveChernoffUpper {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (PositiveMean : 0 < ∫ w, ∑ i, X i w ∂P) (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} ≤
      Real.exp (-((∫ w, ∑ i, X i w ∂P) + l) *
        Real.log (1 + l / (∫ w, ∑ i, X i w ∂P)) + l) := by
  let m := ∫ w, ∑ i, X i w ∂P
  have Threshold : (1 + l / m) * m = m + l := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
  have Exponent : -((1 + l / m) * Real.log (1 + l / m) - l / m) * m =
      -(m + l) * Real.log (1 + l / m) + l := by
    calc
      _ = -((1 + l / m) * m) * Real.log (1 + l / m) + (l / m) * m := by ring
      _ = _ := by rw [Threshold, div_mul_cancel₀ _ PositiveMean.ne']
  have Bound := UnitIndependentSumChernoffUpper P X MeasurableX Independent Bounded
    (l / m) (div_nonneg Nonnegative PositiveMean.le)
  change P.real {ω | (1 + l / m) * m ≤ ∑ i, X i ω} ≤
    Real.exp (-((1 + l / m) * Real.log (1 + l / m) - l / m) * m) at Bound
  simpa only [Threshold, Exponent] using Bound

/-- Doerr (1.10.18), power form on the positive-mean domain of its identity. -/
theorem UnitIndependentSumAdditiveChernoffUpperPower {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (PositiveMean : 0 < ∫ w, ∑ i, X i w ∂P) (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} ≤
      Real.exp l * ((∫ w, ∑ i, X i w ∂P) /
        ((∫ w, ∑ i, X i w ∂P) + l)) ^ ((∫ w, ∑ i, X i w ∂P) + l) := by
  rw [AdditiveChernoffPowerExpression _ l PositiveMean Nonnegative]
  exact UnitIndependentSumAdditiveChernoffUpper P X MeasurableX Independent Bounded
    PositiveMean l Nonnegative

/-- Doerr (1.10.19), including zero mean, zero deviation and empty families. -/
theorem UnitIndependentSumAdditiveChernoffUpperQuadratic {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} ≤
      Real.exp (-(l ^ 2) / (2 * (∫ w, ∑ i, X i w ∂P) + 2 * l / 3)) := by
  let m := ∫ w, ∑ i, X i w ∂P
  have MeanNonnegative : 0 ≤ m := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  by_cases ZeroMean : m = 0
  · rw [UnitSumZeroMeanUpper P X MeasurableX Bounded ZeroMean l Nonnegative]
    by_cases ZeroDeviation : l = 0
    · simp [ZeroDeviation]
    · rw [if_neg ZeroDeviation]
      exact (Real.exp_pos _).le
  have PositiveMean : 0 < m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
  have Threshold : (1 + l / m) * m = m + l := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
  have Denominator : 0 < 2 * m + 2 * l / 3 := by positivity
  have Exponent : -((l / m) ^ 2 * m) / (2 + 2 * (l / m) / 3) =
      -(l ^ 2) / (2 * m + 2 * l / 3) := by
    field_simp
  have Bound := UnitIndependentSumChernoffUpperQuadratic P X MeasurableX Independent Bounded
    (l / m) (div_nonneg Nonnegative PositiveMean.le)
  change P.real {ω | (1 + l / m) * m ≤ ∑ i, X i ω} ≤
    Real.exp (-((l / m) ^ 2 * m) / (2 + 2 * (l / m) / 3)) at Bound
  simpa only [Threshold, Exponent] using Bound

/-- Doerr (1.10.20). At zero mean, Lean's total division gives the valid but
weaker bound one; the separate zero-mean theorem gives the exact probability. -/
theorem UnitIndependentSumAdditiveChernoffUpperMin {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} ≤
      Real.exp (-(min (l ^ 2 / (∫ w, ∑ i, X i w ∂P)) l) / 3) := by
  let m := ∫ w, ∑ i, X i w ∂P
  have MeanNonnegative : 0 ≤ m := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  by_cases ZeroMean : m = 0
  · change P.real _ ≤ Real.exp (-(min (l ^ 2 / m) l) / 3)
    rw [ZeroMean, div_zero, min_eq_left Nonnegative, neg_zero, zero_div, Real.exp_zero]
    exact measureReal_le_one
  have PositiveMean : 0 < m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
  have Threshold : (1 + l / m) * m = m + l := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
  have Product : min ((l / m) ^ 2) (l / m) * m = min (l ^ 2 / m) l := by
    rw [min_mul_of_nonneg _ _ PositiveMean.le, div_mul_cancel₀ _ PositiveMean.ne']
    congr 1
    field_simp
  have Bound := UnitIndependentSumChernoffUpperMin P X MeasurableX Independent Bounded
    (l / m) (div_nonneg Nonnegative PositiveMean.le)
  change P.real {ω | (1 + l / m) * m ≤ ∑ i, X i ω} ≤
    Real.exp (-(min ((l / m) ^ 2) (l / m)) * m / 3) at Bound
  simpa only [Threshold, neg_mul, Product] using Bound

/-- Doerr (1.10.21), with the required restriction 0 <= deviation <= mean. -/
theorem UnitIndependentSumAdditiveChernoffUpperSmall {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) (l : ℝ) (Nonnegative : 0 ≤ l)
    (SmallDeviation : l ≤ ∫ w, ∑ i, X i w ∂P) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P) + l ≤ ∑ i, X i ω} ≤
      Real.exp (-(l ^ 2) / (3 * (∫ w, ∑ i, X i w ∂P))) := by
  let m := ∫ w, ∑ i, X i w ∂P
  have MeanNonnegative : 0 ≤ m := Nonnegative.trans SmallDeviation
  by_cases ZeroMean : m = 0
  · change P.real _ ≤ Real.exp (-(l ^ 2) / (3 * m))
    simp only [ZeroMean, mul_zero, div_zero, Real.exp_zero]
    exact measureReal_le_one
  have PositiveMean : 0 < m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
  have QuadraticLe : l ^ 2 / m ≤ l := by
    apply (div_le_iff₀ PositiveMean).mpr
    nlinarith
  have Bound := UnitIndependentSumAdditiveChernoffUpperMin P X MeasurableX Independent Bounded
    l Nonnegative
  rw [min_eq_left QuadraticLe] at Bound
  convert Bound using 1
  congr 1
  change -(l ^ 2) / (3 * m) = -(l ^ 2 / m) / 3
  field_simp

end
end ECTheoryLib.Probability

