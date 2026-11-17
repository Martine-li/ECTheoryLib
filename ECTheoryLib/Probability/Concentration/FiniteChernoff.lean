import ECTheoryLib.Probability.Concentration.Chernoff
import Mathlib.Analysis.MeanInequalities

/-!
# Finite-size Chernoff upper bounds with complete boundary cases

Doerr equation (1.10.1) uses the number of variables as well as their mean.
Mathlib AM-GM controls the product of affine MGF bounds. The interior proof
uses the optimizing tilt; at the maximum sum, independence factors the event
that every coordinate attains one. Thresholds beyond the maximum have zero
probability. The public theorem requires no positive mean, positive length
or interior-threshold assumption. Zero mean and the empty family are explicit.

The piecewise expression compares the actual threshold (1+d)*mean with n,
avoiding division by the mean. When mean>0 these branches agree with the
source cutoff d=(n-mean)/mean. The empty endpoint uses 0^0=1. Bounds may hold
almost surely and variables need not have identical distributions.

The final scalar theorem proves the displayed comparison with equation
(1.10.2), including the endpoint and beyond-maximum branches.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Mathlib AM-GM, converted to a product bound with a natural exponent; used for both MGF and endpoint events. -/
theorem NonnegativeProductLeMeanPow {n : ℕ} (PositiveLength : 0 < n)
    (z : Fin n → ℝ) (Nonnegative : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ≤ ((∑ i, z i)/(n : ℝ))^n := by
  have PositiveReal : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have MeanBound := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) z (fun _ _ => zero_le_one)
    (by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using PositiveReal)
    (fun i _ => Nonnegative i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at MeanBound
  have Raised := Real.rpow_le_rpow (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => Nonnegative i)) _)
    MeanBound PositiveReal.le
  rw [← Real.rpow_mul (Finset.prod_nonneg (fun i _ => Nonnegative i)),
    inv_mul_cancel₀ PositiveReal.ne', Real.rpow_one, Real.rpow_natCast] at Raised
  exact Raised

/-- The sharper, affine MGF estimate preserves the finite-size correction before exponential relaxation. -/
theorem UnitIntervalMGFChord {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (MeasurableX : AEMeasurable X P) (Bounded : ∀ᵐ ω ∂P, X ω ∈ Icc 0 1) (t : ℝ) :
    mgf X P t ≤ 1+(∫ ω, X ω ∂P)*(Real.exp t-1) := by
  have IntegrableX := Integrable.of_mem_Icc 0 1 MeasurableX Bounded
  have IntegrableExp : Integrable (fun ω => Real.exp (t*X ω)) P :=
    integrable_exp_mul_of_mem_Icc MeasurableX Bounded
  have IntegrableLine : Integrable (fun ω => 1+X ω*(Real.exp t-1)) P :=
    (integrable_const 1).add (IntegrableX.mul_const _)
  have Chord : mgf X P t ≤ ∫ ω, 1+X ω*(Real.exp t-1) ∂P := by
    apply integral_mono_ae IntegrableExp IntegrableLine
    filter_upwards [Bounded] with ω InUnit
    exact UnitIntervalExpChord (X ω) t InUnit
  rw [integral_add (integrable_const _) (IntegrableX.mul_const _),
    integral_const, probReal_univ, one_smul, integral_mul_const] at Chord
  exact Chord

/-- Independent unit-interval variables have MGF bounded by that of a binomial variable with the same mean. -/
theorem UnitIndependentSumFiniteMGFBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0 < n)
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) (t : ℝ) :
    mgf (fun ω => ∑ i, X i ω) P t ≤
      (1+((∫ ω, ∑ i, X i ω ∂P)/(n : ℝ))*(Real.exp t-1))^n := by
  have MeanSum : (∫ ω, ∑ i, X i ω ∂P) = ∑ i, ∫ ω, X i ω ∂P := by
    apply integral_finsetSum
    intro i _
    exact Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i)
  have Product := Independent.mgf_sum₀ MeasurableX Finset.univ (t := t)
  have SumFunction : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by
    funext ω
    exact Finset.sum_apply _ _ _
  rw [SumFunction] at Product
  have LineBound (i : Fin n) := UnitIntervalMGFChord P (X i) (MeasurableX i) (Bounded i) t
  have LineNonnegative (i : Fin n) : 0 ≤ 1+(∫ ω, X i ω ∂P)*(Real.exp t-1) :=
    mgf_nonneg.trans (LineBound i)
  rw [Product, MeanSum]
  calc
    _ ≤ ∏ i, (1+(∫ ω, X i ω ∂P)*(Real.exp t-1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mgf_nonneg
      · intro i _
        exact LineBound i
    _ ≤ ((∑ i, (1+(∫ ω, X i ω ∂P)*(Real.exp t-1)))/(n : ℝ))^n :=
      NonnegativeProductLeMeanPow PositiveLength _ LineNonnegative
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      congr 1
      have Nonzero : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr PositiveLength.ne'
      field_simp

/-- The optimizing finite-size tilt is nonnegative for a threshold between the mean and the maximum. -/
theorem FiniteChernoffTiltNonnegative (N m a : ℝ)
    (PositiveMean : 0 < m) (AboveMean : m ≤ a) (BelowMaximum : a < N) :
    0 ≤ Real.log (a*(N-m)/(m*(N-a))) := by
  have DenominatorPositive : 0 < m*(N-a) := mul_pos PositiveMean (sub_pos.mpr BelowMaximum)
  apply Real.log_nonneg
  apply (le_div_iff₀ DenominatorPositive).mpr
  have PositiveN : 0 < N := lt_of_lt_of_le PositiveMean (AboveMean.trans BelowMaximum.le)
  nlinarith

/-- Evaluation of the optimizing MGF expression gives the two real-power factors. -/
theorem FiniteChernoffTiltValue (N m a : ℝ)
    (PositiveMean : 0 < m) (AboveMean : m ≤ a) (BelowMaximum : a < N) :
    Real.exp (-Real.log (a*(N-m)/(m*(N-a)))*a) *
      (1+(m/N)*(Real.exp (Real.log (a*(N-m)/(m*(N-a))))-1))^N =
      (m/a)^a * ((N-m)/(N-a))^(N-a) := by
  have PositiveA : 0 < a := PositiveMean.trans_le AboveMean
  have PositiveN : 0 < N := PositiveA.trans BelowMaximum
  have PositiveGapA : 0 < N-a := sub_pos.mpr BelowMaximum
  have PositiveGapM : 0 < N-m := sub_pos.mpr (AboveMean.trans_lt BelowMaximum)
  have PositiveRatio : 0 < a*(N-m)/(m*(N-a)) :=
    div_pos (mul_pos PositiveA PositiveGapM) (mul_pos PositiveMean PositiveGapA)
  rw [Real.exp_log PositiveRatio]
  have BaseIdentity : 1+(m/N)*(a*(N-m)/(m*(N-a))-1) = (N-m)/(N-a) := by
    field_simp
    ring
  rw [BaseIdentity, Real.rpow_def_of_pos (div_pos PositiveGapM PositiveGapA),
    Real.rpow_def_of_pos (div_pos PositiveMean PositiveA),
    Real.rpow_def_of_pos (div_pos PositiveGapM PositiveGapA), ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_div (mul_ne_zero PositiveA.ne' PositiveGapM.ne')
      (mul_ne_zero PositiveMean.ne' PositiveGapA.ne'),
    Real.log_mul PositiveA.ne' PositiveGapM.ne', Real.log_mul PositiveMean.ne' PositiveGapA.ne',
    Real.log_div PositiveMean.ne' PositiveA.ne', Real.log_div PositiveGapM.ne' PositiveGapA.ne']
  ring

/-- The sharp finite-size upper tail for a positive mean and a threshold strictly below the maximum. -/
theorem UnitIndependentSumFiniteChernoffInterior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0 < n)
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (PositiveMean : 0 < ∫ ω, ∑ i, X i ω ∂P) (a : ℝ)
    (AboveMean : (∫ ω, ∑ i, X i ω ∂P) ≤ a) (BelowMaximum : a < n) :
    P.real {ω | a ≤ ∑ i, X i ω} ≤
      ((∫ ω, ∑ i, X i ω ∂P)/a)^a *
        (((n : ℝ)-(∫ ω, ∑ i, X i ω ∂P))/((n : ℝ)-a))^((n : ℝ)-a) := by
  let m := ∫ ω, ∑ i, X i ω ∂P
  let t := Real.log (a*((n : ℝ)-m)/(m*((n : ℝ)-a)))
  have TiltNonnegative : 0 ≤ t := FiniteChernoffTiltNonnegative n m a PositiveMean AboveMean BelowMaximum
  have SumFunction : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by
    funext ω
    exact Finset.sum_apply _ _ _
  have MeasurableSum : AEMeasurable (fun ω => ∑ i, X i ω) P := by
    rw [← SumFunction]
    exact Finset.aemeasurable_sum _ (fun i _ => MeasurableX i)
  have SumBounded : ∀ᵐ ω ∂P, (∑ i, X i ω) ∈ Icc 0 (n : ℝ) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    constructor
    · exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
    · calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have IntegrableExp : Integrable (fun ω => Real.exp (t*(∑ i, X i ω))) P :=
    integrable_exp_mul_of_mem_Icc MeasurableSum SumBounded
  have Bound := measure_ge_le_exp_mul_mgf a TiltNonnegative IntegrableExp
  calc
    _ ≤ _ := Bound
    _ ≤ Real.exp (-t*a)*(1+(m/(n : ℝ))*(Real.exp t-1))^n :=
      mul_le_mul_of_nonneg_left
        (UnitIndependentSumFiniteMGFBound P PositiveLength X MeasurableX Independent Bounded t)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.rpow_natCast]
      exact FiniteChernoffTiltValue n m a PositiveMean AboveMean BelowMaximum

/-- At the maximum sum, independence and the first moment give the exact endpoint bound (mean/n)^n. -/
theorem UnitIndependentSumFiniteChernoffEndpoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) :
    P.real {ω | (n : ℝ) ≤ ∑ i, X i ω} ≤ ((∫ ω, ∑ i, X i ω ∂P)/(n : ℝ))^n := by
  classical
  by_cases Empty : n = 0
  · subst n
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, le_refl, Set.ofPred_true,
      probReal_univ, pow_zero]
  have PositiveLength : 0 < n := Nat.pos_of_ne_zero Empty
  have ConstantSum : (∑ _i : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
  have EventEq : {ω | (n : ℝ) ≤ ∑ i, X i ω} =ᵐ[P]
      (⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' Ici 1) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    apply propext
    change ((n : ℝ) ≤ ∑ i, X i ω) ↔
      ω ∈ (⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' Ici 1)
    simp only [mem_iInter, Finset.mem_univ, mem_preimage, mem_Ici, forall_true_left]
    constructor
    · intro SumLarge i
      by_contra Small
      have Strict := Finset.sum_lt_sum (fun j (_hj : j ∈ Finset.univ) => (Bounds j).2)
        ⟨i, Finset.mem_univ i, lt_of_not_ge Small⟩
      rw [ConstantSum] at Strict
      exact (not_lt_of_ge SumLarge) Strict
    · intro EachLarge
      rw [← ConstantSum]
      exact Finset.sum_le_sum (fun i _ => EachLarge i)
  have ProbabilityIdentity := measure_congr EventEq
  rw [Independent.measure_inter_preimage_eq_mul Finset.univ (fun _ _ => measurableSet_Ici)] at ProbabilityIdentity
  have IndividualBound (i : Fin n) : P.real (X i ⁻¹' Ici 1) ≤ ∫ ω, X i ω ∂P := by
    have NonnegativeX : 0 ≤ᵐ[P] X i := by
      filter_upwards [Bounded i] with ω Bound
      exact Bound.1
    have Markov := mul_meas_ge_le_integral_of_nonneg NonnegativeX
      (Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i)) 1
    rw [one_mul] at Markov
    exact Markov
  have NonnegativeMean (i : Fin n) : 0 ≤ ∫ ω, X i ω ∂P :=
    (measureReal_nonneg).trans (IndividualBound i)
  have MeanSum : (∫ ω, ∑ i, X i ω ∂P) = ∑ i, ∫ ω, X i ω ∂P := by
    apply integral_finsetSum
    intro i _
    exact Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i)
  change (P {ω | (n : ℝ) ≤ ∑ i, X i ω}).toReal ≤ _
  rw [ProbabilityIdentity, ENNReal.toReal_prod, MeanSum]
  calc
    _ ≤ ∏ i, ∫ ω, X i ω ∂P := by
      apply Finset.prod_le_prod
      · intro i _
        exact ENNReal.toReal_nonneg
      · intro i _
        exact IndividualBound i
    _ ≤ _ := NonnegativeProductLeMeanPow PositiveLength _ NonnegativeMean

/-- Doerr equation (1.10.1), with explicit beyond-maximum and endpoint branches, including n=0. -/
def FiniteChernoffUpperBound (n : ℕ) (m d : ℝ) : ℝ :=
  if (n : ℝ) < (1+d)*m then 0
  else if (1+d)*m = (n : ℝ) then (m/(n : ℝ))^n
  else (1/(1+d))^((1+d)*m) * (((n : ℝ)-m)/((n : ℝ)-(1+d)*m))^((n : ℝ)-(1+d)*m)

/-- Doerr equation (1.10.1) for every nonnegative relative deviation, including zero mean and empty families. -/
theorem UnitIndependentSumFiniteChernoffUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (1+d)*(∫ w, ∑ i, X i w ∂P) ≤ ∑ i, X i ω} ≤
      FiniteChernoffUpperBound n (∫ w, ∑ i, X i w ∂P) d := by
  let m := ∫ ω, ∑ i, X i ω ∂P
  have NonnegativeMean : 0 ≤ m := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  have AboveMean : m ≤ (1+d)*m := by nlinarith
  change P.real {ω | (1+d)*m ≤ ∑ i, X i ω} ≤ FiniteChernoffUpperBound n m d
  unfold FiniteChernoffUpperBound
  split_ifs with AboveMaximum AtMaximum
  · have NullEvent : P {ω | (1+d)*m ≤ ∑ i, X i ω} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
      have SumLe : (∑ i, X i ω) ≤ (n : ℝ) := by
        calc
          _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
          _ = _ := by simp
      exact not_le_of_gt (SumLe.trans_lt AboveMaximum)
    rw [Measure.real, NullEvent, ENNReal.toReal_zero]
  · rw [AtMaximum]
    exact UnitIndependentSumFiniteChernoffEndpoint P X MeasurableX Independent Bounded
  · have BelowMaximum : (1+d)*m < (n : ℝ) := lt_of_le_of_ne (le_of_not_gt AboveMaximum) AtMaximum
    by_cases ZeroMean : m = 0
    · have PositiveN : (0 : ℝ) < n := by simpa only [ZeroMean, mul_zero] using BelowMaximum
      simp only [ZeroMean, mul_zero, Real.rpow_zero, sub_zero, div_self PositiveN.ne',
        Real.one_rpow, one_mul]
      exact measureReal_le_one
    · have PositiveMean : 0 < m := lt_of_le_of_ne NonnegativeMean (Ne.symm ZeroMean)
      have PositiveLength : 0 < n := Nat.cast_pos.mp (PositiveMean.trans (AboveMean.trans_lt BelowMaximum))
      have Bound := UnitIndependentSumFiniteChernoffInterior P PositiveLength X
        MeasurableX Independent Bounded PositiveMean ((1+d)*m) AboveMean BelowMaximum
      have RatioIdentity : m/((1+d)*m) = 1/(1+d) := by
        field_simp
      change P.real {ω | (1+d)*m ≤ ∑ i, X i ω} ≤
        (m/((1+d)*m))^((1+d)*m) *
          (((n : ℝ)-m)/((n : ℝ)-(1+d)*m))^((n : ℝ)-(1+d)*m) at Bound
      rw [RatioIdentity] at Bound
      exact Bound

/-- In the interior, log(x) <= x-1 bounds the finite-size expression by the exponential Chernoff expression. -/
theorem FiniteChernoffInteriorLeExp (N m d : ℝ)
    (NonnegativeMean : 0 ≤ m) (NonnegativeDeviation : 0 ≤ d)
    (BelowMaximum : (1+d)*m < N) :
    (1/(1+d))^((1+d)*m) * ((N-m)/(N-(1+d)*m))^(N-(1+d)*m) ≤
      Real.exp (-((1+d)*Real.log (1+d)-d)*m) := by
  have PositiveBase : 0 < 1+d := by linarith
  have AboveMean : m ≤ (1+d)*m := by nlinarith
  have GapPositive : 0 < N-(1+d)*m := sub_pos.mpr BelowMaximum
  have MeanGapPositive : 0 < N-m := sub_pos.mpr (AboveMean.trans_lt BelowMaximum)
  have RatioPositive : 0 < (N-m)/(N-(1+d)*m) := div_pos MeanGapPositive GapPositive
  rw [Real.rpow_def_of_pos (div_pos zero_lt_one PositiveBase),
    Real.rpow_def_of_pos RatioPositive, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div one_ne_zero PositiveBase.ne', Real.log_one, zero_sub]
  have LogBound := mul_le_mul_of_nonneg_right
    (Real.log_le_sub_one_of_pos RatioPositive) GapPositive.le
  have Normalize : ((N-m)/(N-(1+d)*m)-1)*(N-(1+d)*m) = d*m := by
    rw [sub_mul, div_mul_cancel₀ _ GapPositive.ne']
    ring
  rw [Normalize] at LogBound
  nlinarith

/-- The strongest finite-size expression is no larger than equation (1.10.2), including all boundary branches. -/
theorem FiniteChernoffUpperBoundLeExp (n : ℕ) (m d : ℝ)
    (NonnegativeMean : 0 ≤ m) (NonnegativeDeviation : 0 ≤ d) :
    FiniteChernoffUpperBound n m d ≤ Real.exp (-((1+d)*Real.log (1+d)-d)*m) := by
  have PositiveBase : 0 < 1+d := by linarith
  unfold FiniteChernoffUpperBound
  split_ifs with AboveMaximum AtMaximum
  · exact (Real.exp_pos _).le
  · by_cases Empty : n = 0
    · have ZeroMean : m = 0 := by
        have ZeroProduct : (1+d)*m = 0 := by simpa only [Empty, Nat.cast_zero] using AtMaximum
        exact (mul_eq_zero.mp ZeroProduct).resolve_left PositiveBase.ne'
      simp only [Empty, pow_zero, ZeroMean, mul_zero, Real.exp_zero, le_refl]
    · have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero Empty)
      have NonzeroMean : m ≠ 0 := by
        intro ZeroMean
        rw [ZeroMean, mul_zero] at AtMaximum
        exact PositiveN.ne' AtMaximum.symm
      have RatioIdentity : m/(n : ℝ) = 1/(1+d) := by
        rw [← AtMaximum]
        field_simp
      rw [RatioIdentity, ← Real.rpow_natCast,
        Real.rpow_def_of_pos (div_pos zero_lt_one PositiveBase)]
      apply Real.exp_le_exp.mpr
      rw [Real.log_div one_ne_zero PositiveBase.ne', Real.log_one, zero_sub, ← AtMaximum]
      nlinarith
  · have BelowMaximum : (1+d)*m < (n : ℝ) := lt_of_le_of_ne (le_of_not_gt AboveMaximum) AtMaximum
    exact FiniteChernoffInteriorLeExp n m d NonnegativeMean NonnegativeDeviation BelowMaximum

end
end ECTheoryLib.Probability
