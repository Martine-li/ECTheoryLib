import ECTheoryLib.Probability.Concentration.LowerChernoff
import Mathlib.Tactic.FieldSimp

/-!
# Additive Chernoff lower tails and their domains

Doerr Theorem 1.10.11, equations (1.10.22)-(1.10.24).
The finite bound explicitly extends negative thresholds by zero. The raw
power expression and its comparison chain are restricted to 0 <= l <= m;
the source does not state this restriction. The quadratic probability bound
holds for every nonnegative deviation. Zero denominators use total division,
and 0^0=1. Existing relative lower tails supply all concentration estimates.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Finite additive lower expression, with an explicit zero extension when
the threshold is negative and the existing relative endpoint at l=m. -/
def FiniteAdditiveChernoffLowerBound (n : ℕ) (m l : ℝ) : ℝ :=
  if m < l then 0
  else if l = m then (1 - m / (n : ℝ)) ^ n
  else (m / (m - l)) ^ (m - l) *
    (((n : ℝ) - m) / ((n : ℝ) - m + l)) ^ ((n : ℝ) - m + l)

theorem FiniteAdditiveChernoffLowerZeroMean (n : ℕ) (l : ℝ) (Nonnegative : 0 ≤ l) :
    FiniteAdditiveChernoffLowerBound n 0 l = if l = 0 then 1 else 0 := by
  by_cases Zero : l = 0
  · simp [Zero, FiniteAdditiveChernoffLowerBound]
  · have Positive : 0 < l := lt_of_le_of_ne Nonnegative (Ne.symm Zero)
    simp [FiniteAdditiveChernoffLowerBound, Positive, Zero]

/-- The original relative parameterization is valid up to the zero threshold. -/
theorem FiniteAdditiveChernoffLowerEqRelative (n : ℕ) (m l : ℝ)
    (PositiveMean : 0 < m) (Nonnegative : 0 ≤ l) (Small : l ≤ m) :
    FiniteAdditiveChernoffLowerBound n m l = FiniteChernoffLowerBound n m (l / m) := by
  have Threshold : (1 - l / m) * m = m - l := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
  by_cases Endpoint : l = m
  · subst l
    simp [FiniteAdditiveChernoffLowerBound, FiniteChernoffLowerBound, PositiveMean.ne']
  · have RelativeNe : l / m ≠ 1 := by
      intro Equal
      exact Endpoint ((div_eq_one_iff_eq PositiveMean.ne').mp Equal)
    have Gap : m - l ≠ 0 := sub_ne_zero.mpr (Ne.symm Endpoint)
    have RelativeGap : 1 - l / m ≠ 0 := sub_ne_zero.mpr (Ne.symm RelativeNe)
    have Ratio : m / (m - l) = 1 / (1 - l / m) := by
      field_simp
    have Complement : (n : ℝ) - m + l = (n : ℝ) - (m - l) := by ring
    simp only [FiniteAdditiveChernoffLowerBound, not_lt.mpr Small, if_false,
      Endpoint, FiniteChernoffLowerBound, RelativeNe, Threshold, Ratio, Complement]

/-- Nonnegative sums have no mass below a negative threshold. Independence
and measurability assumptions are unnecessary for this exact boundary. -/
theorem UnitSumAdditiveLowerBeyondMean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (l : ℝ) (Beyond : (∫ w, ∑ i, X i w ∂P) < l) :
    P.real {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P) - l} = 0 := by
  have Null : P {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P) - l} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    have SumNonnegative : 0 ≤ ∑ i, X i ω := Finset.sum_nonneg (fun i _ => (Bounds i).1)
    intro InEvent
    change (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P) - l at InEvent
    linarith
  rw [Measure.real, Null, ENNReal.toReal_zero]

/-- The finite additive bound includes zero/maximum means, empty families,
zero thresholds and the explicitly repaired negative-threshold branch. -/
theorem UnitIndependentSumFiniteAdditiveChernoffLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P) - l} ≤
      FiniteAdditiveChernoffLowerBound n (∫ w, ∑ i, X i w ∂P) l := by
  let m := ∫ w, ∑ i, X i w ∂P
  change P.real {ω | (∑ i, X i ω) ≤ m - l} ≤ FiniteAdditiveChernoffLowerBound n m l
  by_cases Beyond : m < l
  · rw [UnitSumAdditiveLowerBeyondMean P X Bounded l Beyond]
    simp [FiniteAdditiveChernoffLowerBound, Beyond]
  have Small : l ≤ m := le_of_not_gt Beyond
  have MeanNonnegative : 0 ≤ m := Nonnegative.trans Small
  by_cases ZeroMean : m = 0
  · have ZeroDeviation : l = 0 := le_antisymm (Small.trans_eq ZeroMean) Nonnegative
    rw [ZeroMean, FiniteAdditiveChernoffLowerZeroMean n l Nonnegative, if_pos ZeroDeviation]
    exact measureReal_le_one
  have PositiveMean : 0 < m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
  have InUnit : l / m ∈ Icc 0 1 :=
    ⟨div_nonneg Nonnegative MeanNonnegative, (div_le_one PositiveMean).mpr Small⟩
  have Threshold : (1 - l / m) * m = m - l := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
  rw [FiniteAdditiveChernoffLowerEqRelative n m l PositiveMean Nonnegative Small]
  have Bound := UnitIndependentSumFiniteChernoffLower P X MeasurableX Independent Bounded (l / m) InUnit
  change P.real {ω | (∑ i, X i ω) ≤ (1 - l / m) * m} ≤ _ at Bound
  simpa only [Threshold] using Bound

/-- Raw additive power expression rewritten as the existing logarithmic
relative exponent. The zero-threshold endpoint uses 0^0=1 explicitly. -/
theorem AdditiveChernoffLowerPowerExpression (m l : ℝ) (PositiveMean : 0 < m)
    (Nonnegative : 0 ≤ l) (Small : l ≤ m) :
    Real.exp (-l) * (m / (m - l)) ^ (m - l) =
      Real.exp (-((l / m) + (1 - l / m) * Real.log (1 - l / m)) * m) := by
  by_cases Endpoint : l = m
  · subst l
    simp [PositiveMean.ne']
  have Below : l < m := lt_of_le_of_ne Small Endpoint
  have GapPositive : 0 < m - l := sub_pos.mpr Below
  have RelativePositive : 0 < 1 - l / m := sub_pos.mpr ((div_lt_one PositiveMean).mpr Below)
  have Ratio : m / (m - l) = 1 / (1 - l / m) := by field_simp
  have Threshold : (1 - l / m) * m = m - l := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ PositiveMean.ne']
  rw [Ratio, Real.rpow_def_of_pos (div_pos zero_lt_one RelativePositive),
    ← Real.exp_add, Real.log_div one_ne_zero RelativePositive.ne', Real.log_one]
  congr 1
  calc
    _ = -l - (m - l) * Real.log (1 - l / m) := by ring
    _ = _ := by rw [← Threshold]; field_simp; ring

/-- The mean upper bound is essential for the finite-size scalar comparison.
The raw power form is used only for nonnegative thresholds. -/
theorem FiniteAdditiveChernoffLowerLePower (n : ℕ) (m l : ℝ)
    (MeanBounds : m ∈ Icc 0 (n : ℝ)) (Nonnegative : 0 ≤ l) (Small : l ≤ m) :
    FiniteAdditiveChernoffLowerBound n m l ≤ Real.exp (-l) * (m / (m - l)) ^ (m - l) := by
  by_cases ZeroMean : m = 0
  · have ZeroDeviation : l = 0 := le_antisymm (Small.trans_eq ZeroMean) Nonnegative
    simp [ZeroMean, ZeroDeviation, FiniteAdditiveChernoffLowerBound]
  have PositiveMean : 0 < m := lt_of_le_of_ne MeanBounds.1 (Ne.symm ZeroMean)
  rw [FiniteAdditiveChernoffLowerEqRelative n m l PositiveMean Nonnegative Small,
    AdditiveChernoffLowerPowerExpression m l PositiveMean Nonnegative Small]
  exact FiniteChernoffLowerBoundLeExp n m (l / m) MeanBounds
    ⟨div_nonneg Nonnegative MeanBounds.1, (div_le_one PositiveMean).mpr Small⟩

/-- The raw power-to-quadratic comparison retains 0 <= l <= m, including m=l=0. -/
theorem AdditiveChernoffLowerPowerLeQuadratic (m l : ℝ)
    (Nonnegative : 0 ≤ l) (Small : l ≤ m) :
    Real.exp (-l) * (m / (m - l)) ^ (m - l) ≤ Real.exp (-(l ^ 2) / (2 * m)) := by
  have MeanNonnegative : 0 ≤ m := Nonnegative.trans Small
  by_cases ZeroMean : m = 0
  · have ZeroDeviation : l = 0 := le_antisymm (Small.trans_eq ZeroMean) Nonnegative
    simp [ZeroMean, ZeroDeviation]
  have PositiveMean : 0 < m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
  rw [AdditiveChernoffLowerPowerExpression m l PositiveMean Nonnegative Small]
  apply Real.exp_le_exp.mpr
  have Bound := mul_le_mul_of_nonneg_right (neg_le_neg
    (ChernoffLowerExponentQuadratic (l / m)
      ⟨div_nonneg Nonnegative MeanNonnegative, (div_le_one PositiveMean).mpr Small⟩)) MeanNonnegative
  have Exponent : -((l / m) ^ 2 / 2) * m = -(l ^ 2) / (2 * m) := by field_simp
  exact Bound.trans_eq Exponent

/-- Doerr (1.10.23), on the explicit range 0 <= l <= mean. -/
theorem UnitIndependentSumAdditiveChernoffLowerPower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (l : ℝ) (Nonnegative : 0 ≤ l) (Small : l ≤ ∫ w, ∑ i, X i w ∂P) :
    P.real {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P) - l} ≤
      Real.exp (-l) * ((∫ w, ∑ i, X i w ∂P) /
        ((∫ w, ∑ i, X i w ∂P) - l)) ^ ((∫ w, ∑ i, X i w ∂P) - l) := by
  have MeanNonnegative : 0 ≤ ∫ w, ∑ i, X i w ∂P := Nonnegative.trans Small
  have MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ (n : ℝ) := by
    have IntegrableSum := integrable_finsetSum Finset.univ
      (fun i _ => Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i))
    have Upper : (fun w => ∑ i, X i w) ≤ᵐ[P] (fun _ => (n : ℝ)) := by
      filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _ = _ := by simp
    have Bound := integral_mono_ae IntegrableSum (integrable_const (n : ℝ)) Upper
    simpa only [integral_const, probReal_univ, one_smul] using Bound
  exact (UnitIndependentSumFiniteAdditiveChernoffLower P X MeasurableX Independent Bounded l Nonnegative).trans
    (FiniteAdditiveChernoffLowerLePower n _ l ⟨MeanNonnegative, MeanUpper⟩ Nonnegative Small)

/-- Doerr (1.10.24) for all nonnegative deviations. At zero mean the total
division gives the valid bound one; negative thresholds have probability zero. -/
theorem UnitIndependentSumAdditiveChernoffLowerQuadratic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P) - l} ≤
      Real.exp (-(l ^ 2) / (2 * (∫ w, ∑ i, X i w ∂P))) := by
  by_cases Small : l ≤ ∫ w, ∑ i, X i w ∂P
  · exact (UnitIndependentSumAdditiveChernoffLowerPower P X MeasurableX Independent Bounded l Nonnegative Small).trans
      (AdditiveChernoffLowerPowerLeQuadratic _ l Nonnegative Small)
  · rw [UnitSumAdditiveLowerBeyondMean P X Bounded l (lt_of_not_ge Small)]
    exact (Real.exp_pos _).le

end
end ECTheoryLib.Probability

