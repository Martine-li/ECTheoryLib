import ECTheoryLib.Probability.Concentration.AdditiveChernoffLower
import ECTheoryLib.Probability.Concentration.LowerChernoff

/-!
# Lower Chernoff probability bounds with a mean lower estimate

Doerr Theorem 1.10.21(b), selecting the probability conclusions of 1.10.5.
The estimate may be negative. Scalar comparison chains are only reused on
their nonnegative domain; the probability interfaces retain all lower estimates.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Substitute a mean lower estimate in both the closed lower event and the
strongest finite expression, retaining empty families and negative estimates. -/
theorem UnitIndependentSumFiniteChernoffLowerOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ ∫ ω, ∑ i, X i ω ∂P)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    P.real {ω | (∑ i, X i ω) ≤ (1 - d) * L} ≤ FiniteChernoffLowerBound n L d := by
  by_cases ZeroEstimate : L = 0
  · rw [ZeroEstimate, FiniteChernoffLowerZeroMean]
    exact measureReal_le_one
  by_cases NegativeEstimate : L < 0
  · by_cases Endpoint : d = 1
    · rw [Endpoint, FiniteChernoffLowerBound, if_pos rfl]
      apply measureReal_le_one.trans
      apply one_le_pow₀
      have Ratio := div_nonpos_of_nonpos_of_nonneg NegativeEstimate.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    have BelowOne : d < 1 := lt_of_le_of_ne InUnit.2 Endpoint
    have ThresholdNegative : (1 - d) * L < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr BelowOne) NegativeEstimate
    have NullEvent : P {ω | (∑ i, X i ω) ≤ (1 - d) * L} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
      have SumNonnegative : 0 ≤ ∑ i, X i ω :=
        Finset.sum_nonneg (fun i _ => (Bounds i).1)
      change ¬ (∑ i, X i ω) ≤ (1 - d) * L
      linarith
    rw [Measure.real, NullEvent, ENNReal.toReal_zero,
      FiniteChernoffLowerBound, if_neg Endpoint]
    have NumeratorNonnegative : 0 ≤ (n : ℝ) - L :=
      sub_nonneg.mpr (NegativeEstimate.le.trans (Nat.cast_nonneg n))
    have DenominatorNonnegative : 0 ≤ (n : ℝ) - (1 - d) * L := by
      have NNonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact mul_nonneg (Real.rpow_nonneg (div_nonneg zero_le_one (sub_nonneg.mpr InUnit.2)) _)
      (Real.rpow_nonneg (div_nonneg NumeratorNonnegative DenominatorNonnegative) _)
  have PositiveL : 0 < L := lt_of_le_of_ne (le_of_not_gt NegativeEstimate) (Ne.symm ZeroEstimate)
  let m := ∫ ω, ∑ i, X i ω ∂P
  have PositiveMean : 0 < m := PositiveL.trans_le MeanLower
  let c := L / m
  have ScaleNonnegative : 0 ≤ c := div_nonneg PositiveL.le PositiveMean.le
  have ScaleAtMostOne : c ≤ 1 := (div_le_one PositiveMean).mpr MeanLower
  let Y : Fin n → Ω → ℝ := fun i ω => c * X i ω
  have MeasurableY (i : Fin n) : AEMeasurable (Y i) P :=
    aemeasurable_const.mul (MeasurableX i)
  have IndependentY : iIndepFun Y P :=
    Independent.comp (fun (_ : Fin n) (x : ℝ) => c * x)
      (fun _ => measurable_const.mul measurable_id)
  have BelowOriginal (i : Fin n) : ∀ᵐ ω ∂P, Y i ω ≤ X i ω := by
    filter_upwards [Bounded i] with ω Bounds
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ScaleAtMostOne Bounds.1
  have BoundedY (i : Fin n) : ∀ᵐ ω ∂P, Y i ω ∈ Icc 0 1 := by
    filter_upwards [Bounded i, BelowOriginal i] with ω Bounds Below
    exact ⟨mul_nonneg ScaleNonnegative Bounds.1, Below.trans Bounds.2⟩
  have MeanY : (∫ ω, ∑ i, Y i ω ∂P) = L := by
    simp only [Y, ← Finset.mul_sum, integral_const_mul]
    change L / m * m = L
    exact div_mul_cancel₀ _ PositiveMean.ne'
  have Bound := UnitIndependentSumFiniteChernoffLower P Y MeasurableY IndependentY BoundedY d InUnit
  rw [MeanY] at Bound
  apply le_trans ?_ Bound
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono_ae
  filter_upwards [ae_all_iff.mpr BelowOriginal] with ω Below
  exact fun Event => (Finset.sum_le_sum (fun i _ => Below i)).trans Event

/-- The logarithmic lower bound retains every real lower estimate. For a
negative estimate its right side is at least one. -/
theorem UnitIndependentSumChernoffLowerOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ ∫ ω, ∑ i, X i ω ∂P)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    P.real {ω | (∑ i, X i ω) ≤ (1 - d) * L} ≤
      Real.exp (-(d + (1 - d) * Real.log (1 - d)) * L) := by
  by_cases NonnegativeL : 0 ≤ L
  · have IntegrableSum := integrable_finsetSum Finset.univ
      (fun i _ => Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i))
    have SumAtMost : ∀ᵐ ω ∂P, (∑ i, X i ω) ≤ (n : ℝ) := by
      filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _ = _ := by simp
    have MeanAtMostN : (∫ ω, ∑ i, X i ω ∂P) ≤ (n : ℝ) := by
      simpa using integral_mono_ae IntegrableSum (integrable_const (n : ℝ)) SumAtMost
    exact (UnitIndependentSumFiniteChernoffLowerOfLeMean P X MeasurableX Independent
      Bounded L MeanLower d InUnit).trans
      (FiniteChernoffLowerBoundLeExp n L d ⟨NonnegativeL, MeanLower.trans MeanAtMostN⟩ InUnit)
  have CoefficientNonnegative : 0 ≤ d + (1 - d) * Real.log (1 - d) :=
    (div_nonneg (sq_nonneg d) (by norm_num)).trans (ChernoffLowerExponentQuadratic d InUnit)
  exact measureReal_le_one.trans (Real.one_le_exp_iff.mpr
    (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr CoefficientNonnegative)
      (le_of_not_ge NonnegativeL)))

/-- The source power expression is equivalent to the logarithmic expression,
including d=1 with the explicit 0^0=1 convention. -/
theorem UnitIndependentSumChernoffLowerPowerOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ ∫ ω, ∑ i, X i ω ∂P)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    P.real {ω | (∑ i, X i ω) ≤ (1 - d) * L} ≤
      (Real.exp (-d) / (1 - d) ^ (1 - d)) ^ L := by
  rw [ChernoffLowerPowerExpression d L InUnit]
  exact UnitIndependentSumChernoffLowerOfLeMean P X MeasurableX Independent Bounded L MeanLower d InUnit

/-- The quadratic probability bound is valid for negative estimates too,
although the scalar comparison with the logarithmic bound then reverses. -/
theorem UnitIndependentSumChernoffLowerQuadraticOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ ∫ ω, ∑ i, X i ω ∂P)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    P.real {ω | (∑ i, X i ω) ≤ (1 - d) * L} ≤ Real.exp (-(d ^ 2 / 2) * L) := by
  by_cases NonnegativeL : 0 ≤ L
  · apply (UnitIndependentSumChernoffLowerOfLeMean P X MeasurableX Independent
      Bounded L MeanLower d InUnit).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (neg_le_neg (ChernoffLowerExponentQuadratic d InUnit)) NonnegativeL)
  exact measureReal_le_one.trans (Real.one_le_exp_iff.mpr
    (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity))
      (le_of_not_ge NonnegativeL)))

end
end ECTheoryLib.Probability



/-! Additive Chernoff lower tails with an estimate for the actual mean. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The finite expression uses its explicit negative-threshold zero branch.
The lower estimate is an arbitrary real number, including negative values. -/
theorem UnitIndependentSumFiniteAdditiveChernoffLowerOfLeMean {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ ∫ ω, ∑ i, X i ω ∂P)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∑ i, X i ω) ≤ L - l} ≤ FiniteAdditiveChernoffLowerBound n L l := by
  by_cases Beyond : L < l
  · have Null := UnitSumAdditiveLowerBeyondMean P X Bounded
      ((∫ ω, ∑ i, X i ω ∂P) - (L - l)) (by linarith)
    have Threshold : (∫ ω, ∑ i, X i ω ∂P) -
        ((∫ ω, ∑ i, X i ω ∂P) - (L - l)) = L - l := by ring
    rw [Threshold] at Null
    rw [Null, FiniteAdditiveChernoffLowerBound, if_pos Beyond]
  have Small : l ≤ L := le_of_not_gt Beyond
  have EstimateNonnegative : 0 ≤ L := Nonnegative.trans Small
  by_cases ZeroEstimate : L = 0
  · have ZeroDeviation : l = 0 := le_antisymm (Small.trans_eq ZeroEstimate) Nonnegative
    rw [ZeroEstimate, FiniteAdditiveChernoffLowerZeroMean n l Nonnegative,
      if_pos ZeroDeviation]
    exact measureReal_le_one
  have PositiveEstimate : 0 < L := lt_of_le_of_ne EstimateNonnegative (Ne.symm ZeroEstimate)
  have InUnit : l / L ∈ Icc 0 1 :=
    ⟨div_nonneg Nonnegative EstimateNonnegative, (div_le_one PositiveEstimate).mpr Small⟩
  have Threshold : (1 - l / L) * L = L - l := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ PositiveEstimate.ne']
  have Bound := UnitIndependentSumFiniteChernoffLowerOfLeMean P X MeasurableX
    Independent Bounded L MeanLower (l / L) InUnit
  rw [Threshold] at Bound
  rw [FiniteAdditiveChernoffLowerEqRelative n L l PositiveEstimate Nonnegative Small]
  exact Bound

/-- The power expression retains the source-domain repair 0<=l<=L. -/
theorem UnitIndependentSumAdditiveChernoffLowerPowerOfLeMean {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ ∫ ω, ∑ i, X i ω ∂P)
    (l : ℝ) (Nonnegative : 0 ≤ l) (Small : l ≤ L) :
    P.real {ω | (∑ i, X i ω) ≤ L - l} ≤ Real.exp (-l) * (L / (L - l)) ^ (L - l) := by
  have IntegrableSum := integrable_finsetSum Finset.univ
    (fun i _ => Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i))
  have Upper : (fun ω => ∑ i, X i ω) ≤ᵐ[P] (fun _ => (n : ℝ)) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
      _ = _ := by simp
  have MeanAtMostN : (∫ ω, ∑ i, X i ω ∂P) ≤ (n : ℝ) := by
    simpa using integral_mono_ae IntegrableSum (integrable_const (n : ℝ)) Upper
  exact (UnitIndependentSumFiniteAdditiveChernoffLowerOfLeMean P X MeasurableX
    Independent Bounded L MeanLower l Nonnegative).trans
    (FiniteAdditiveChernoffLowerLePower n L l
      ⟨Nonnegative.trans Small, MeanLower.trans MeanAtMostN⟩ Nonnegative Small)

/-- The equivalent logarithmic form requires a positive estimate and l<=L. -/
theorem UnitIndependentSumAdditiveChernoffLowerOfLeMean {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ ∫ ω, ∑ i, X i ω ∂P) (PositiveEstimate : 0 < L)
    (l : ℝ) (Nonnegative : 0 ≤ l) (Small : l ≤ L) :
    P.real {ω | (∑ i, X i ω) ≤ L - l} ≤
      Real.exp (-((l / L) + (1 - l / L) * Real.log (1 - l / L)) * L) := by
  rw [← AdditiveChernoffLowerPowerExpression L l PositiveEstimate Nonnegative Small]
  exact UnitIndependentSumAdditiveChernoffLowerPowerOfLeMean P X MeasurableX
    Independent Bounded L MeanLower l Nonnegative Small

/-- The quadratic probability bound allows negative estimates and deviations
beyond L; it does not extend the raw power comparison to those domains. -/
theorem UnitIndependentSumAdditiveChernoffLowerQuadraticOfLeMean {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ ∫ ω, ∑ i, X i ω ∂P)
    (l : ℝ) (Nonnegative : 0 ≤ l) :
    P.real {ω | (∑ i, X i ω) ≤ L - l} ≤ Real.exp (-(l ^ 2) / (2 * L)) := by
  by_cases Nonpositive : L ≤ 0
  · exact measureReal_le_one.trans (Real.one_le_exp_iff.mpr
      (div_nonneg_of_nonpos (neg_nonpos.mpr (sq_nonneg l))
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) Nonpositive)))
  by_cases Beyond : L < l
  · have Null := UnitSumAdditiveLowerBeyondMean P X Bounded
      ((∫ ω, ∑ i, X i ω ∂P) - (L - l)) (by linarith)
    have Threshold : (∫ ω, ∑ i, X i ω ∂P) -
        ((∫ ω, ∑ i, X i ω ∂P) - (L - l)) = L - l := by ring
    rw [Threshold] at Null
    rw [Null]
    exact (Real.exp_pos _).le
  have Small : l ≤ L := le_of_not_gt Beyond
  exact (UnitIndependentSumAdditiveChernoffLowerPowerOfLeMean P X MeasurableX
    Independent Bounded L MeanLower l Nonnegative Small).trans
    (AdditiveChernoffLowerPowerLeQuadratic L l Nonnegative Small)

end
end ECTheoryLib.Probability

