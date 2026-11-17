import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelation
import ECTheoryLib.Probability.Concentration.LowerChernoff

/-!
# Finite-size concentration under event negative correlation

The strongest finite-size upper/lower expressions are valid for one/zero
negatively correlated event counts. Preserve the existing all-subset
condition, actual indicator family and exact marginal sum. AM-GM and the
scalar tilt evaluation are reused; endpoints and all mean boundaries are
explicit. This covers the unweighted finite-size part of Theorems 1.10.23
and 1.10.24, not their entire affine, variance or mean-replacement scope.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Preserve the finite-size correction in the MGF of a dependent event
count. AM-GM is applied only after the all-subset product estimate. -/
theorem OneNegativeCorrelationCountFiniteMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (t : ℝ) (Nonnegative : 0≤t) :
    mgf (fun ω => ∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω) P t≤
      (1+((∑ i, P.real (Events i))/(n : ℝ))*(Real.exp t-1))^n := by
  have Bound := OneNegativeCorrelationAffineMGF P Events MeasurableEvents Correlated
    (fun _ => 0) (fun _ => 1) (fun _ => zero_le_one) t Nonnegative
  simp only [sub_zero,one_mul,zero_add,mul_zero,Real.exp_zero,mul_one] at Bound
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  apply Bound.trans
  calc
    _≤((∑ i : Fin n, (1-P.real (Events i)+P.real (Events i)*Real.exp t))/(n : ℝ))^n := by
      apply NonnegativeProductLeMeanPow PositiveLength
      intro i
      have AtMostOne := measureReal_le_one (μ := P) (s := Events i)
      positivity
    _=_ := by
      congr 1
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      field_simp
      ring

/-- The event count reaches its maximum exactly when all events occur. -/
theorem EventCountAtMaximum {Ω : Type*} {n : ℕ} (Events : Fin n → Set Ω) (ω : Ω) :
    (n : ℝ)≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω ↔ ∀ i, ω∈Events i := by
  classical
  have AtMostOne (i : Fin n) : (Events i).indicator (fun _ => (1 : ℝ)) ω≤1 := by
    by_cases Inside : ω∈Events i <;> simp [Inside]
  have Ones : (∑ _i : Fin n, (1 : ℝ))=(n : ℝ) := by simp
  constructor
  · intro Large i
    by_contra Outside
    have Strict := Finset.sum_lt_sum (fun j (_ : j∈(Finset.univ : Finset (Fin n))) => AtMostOne j)
      ⟨i,Finset.mem_univ i,by simp [Outside]⟩
    rw [Ones] at Strict
    exact (not_lt_of_ge Large) Strict
  · intro Inside
    simp [indicator_of_mem (Inside _)]

/-- The finite-size endpoint needs only one-negative correlation, not
independence. Empty families retain the value 0^0=1. -/
theorem OneNegativeCorrelationFiniteEndpoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (Correlated : OneNegativelyCorrelated P Events) :
    P.real {ω | (n : ℝ)≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}≤
      ((∑ i, P.real (Events i))/(n : ℝ))^n := by
  classical
  by_cases Empty : n=0
  · subst n
    simp
  have Event : {ω | (n : ℝ)≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}=
      ⋂ i∈(Finset.univ : Finset (Fin n)), Events i := by
    ext ω
    simp only [mem_ofPred_eq,mem_iInter,Finset.mem_univ,forall_true_left,EventCountAtMaximum]
  rw [Event]
  exact (Correlated Finset.univ).trans
    (NonnegativeProductLeMeanPow (Nat.pos_of_ne_zero Empty) _ (fun _ => ENNReal.toReal_nonneg))

/-- The optimizing finite-size Chernoff tilt uses the dependent count MGF
certificate; all scalar optimization is reused from the independent case. -/
theorem OneNegativeCorrelationFiniteInterior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events)
    (PositiveMean : 0<∑ i, P.real (Events i)) (a : ℝ)
    (AboveMean : (∑ i, P.real (Events i))≤a) (BelowMaximum : a<n) :
    P.real {ω | a≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}≤
      ((∑ i, P.real (Events i))/a)^a*
        (((n : ℝ)-(∑ i, P.real (Events i)))/((n : ℝ)-a))^((n : ℝ)-a) := by
  let m := ∑ i, P.real (Events i)
  let t := Real.log (a*((n : ℝ)-m)/(m*((n : ℝ)-a)))
  have TiltNonnegative : 0≤t := FiniteChernoffTiltNonnegative n m a PositiveMean AboveMean BelowMaximum
  have Bounded : ∀ᵐ ω ∂P, (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)∈Icc 0 (n : ℝ) := by
    exact ae_of_all _ (fun ω => by simpa only [Fintype.card_fin] using EventCountInUnitSum Events ω)
  have IntegrableExp : Integrable (fun ω => Real.exp (t*(∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω))) P :=
    integrable_exp_mul_of_mem_Icc (EventCountMeasurable Events MeasurableEvents).aemeasurable Bounded
  have Bound := measure_ge_le_exp_mul_mgf a TiltNonnegative IntegrableExp
  calc
    _≤_ := Bound
    _≤Real.exp (-t*a)*(1+(m/(n : ℝ))*(Real.exp t-1))^n :=
      mul_le_mul_of_nonneg_left
        (OneNegativeCorrelationCountFiniteMGF P PositiveLength Events MeasurableEvents Correlated t TiltNonnegative)
        (Real.exp_pos _).le
    _=_ := by
      rw [← Real.rpow_natCast]
      exact FiniteChernoffTiltValue n m a PositiveMean AboveMean BelowMaximum

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- All branches of the strongest finite-size upper expression hold for
one-negatively correlated event indicators. -/
theorem OneNegativeCorrelationFiniteChernoffUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (1+d)*(∑ i, P.real (Events i))≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}≤
      FiniteChernoffUpperBound n (∑ i, P.real (Events i)) d := by
  let m := ∑ i, P.real (Events i)
  have MeanNonnegative : 0≤m := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have AboveMean : m≤(1+d)*m := by nlinarith
  change P.real {ω | (1+d)*m≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}≤FiniteChernoffUpperBound n m d
  unfold FiniteChernoffUpperBound
  split_ifs with AboveMaximum AtMaximum
  · have Empty : {ω | (1+d)*m≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}=∅ := by
      ext ω
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      have AtMostN : (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(n : ℝ) := by
        simpa only [Fintype.card_fin] using (EventCountInUnitSum Events ω).2
      exact not_le_of_gt (AtMostN.trans_lt AboveMaximum)
    rw [Empty]
    simp
  · rw [AtMaximum]
    exact OneNegativeCorrelationFiniteEndpoint P Events Correlated
  · have BelowMaximum : (1+d)*m<(n : ℝ) := lt_of_le_of_ne (le_of_not_gt AboveMaximum) AtMaximum
    by_cases ZeroMean : m=0
    · have PositiveN : (0 : ℝ)<n := by simpa only [ZeroMean,mul_zero] using BelowMaximum
      simp only [ZeroMean,mul_zero,Real.rpow_zero,sub_zero,div_self PositiveN.ne',Real.one_rpow,one_mul]
      exact measureReal_le_one
    · have PositiveMean : 0<m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
      have PositiveN : 0<n := Nat.cast_pos.mp (PositiveMean.trans (AboveMean.trans_lt BelowMaximum))
      have Bound := OneNegativeCorrelationFiniteInterior P PositiveN Events MeasurableEvents Correlated
        PositiveMean ((1+d)*m) AboveMean BelowMaximum
      change P.real {ω | (1+d)*m≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}≤
        (m/((1+d)*m))^((1+d)*m)*(((n : ℝ)-m)/((n : ℝ)-(1+d)*m))^((n : ℝ)-(1+d)*m) at Bound
      have Ratio : m/((1+d)*m)=1/(1+d) := by field_simp
      rw [Ratio] at Bound
      exact Bound

/-- Complementing actual indicators changes the total count by n. -/
theorem EventComplementCount {Ω : Type*} {n : ℕ} (Events : Fin n → Set Ω) (ω : Ω) :
    (∑ i, (Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω)=
      (n : ℝ)-(∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω) := by
  classical
  have Each (i : Fin n) : (Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω=
      1-(Events i).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases Inside : ω∈Events i <;> simp [Inside]
  simp_rw [Each]
  rw [Finset.sum_sub_distrib]
  simp

/-- The complementary mean is exact, without an independence premise. -/
theorem EventComplementMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i)) :
    (∑ i, P.real (Events i)ᶜ)=(n : ℝ)-(∑ i, P.real (Events i)) := by
  simp_rw [probReal_compl_eq_one_sub (MeasurableEvents _)]
  rw [Finset.sum_sub_distrib]
  simp

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The sharp lower endpoint comes from the upper endpoint of the actual
complement family, retaining its finite-size factor. -/
theorem ZeroNegativeCorrelationFiniteEndpoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) :
    P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤0}≤
      (1-(∑ i, P.real (Events i))/(n : ℝ))^n := by
  by_cases Empty : n=0
  · subst n
    simp
  have Bound := OneNegativeCorrelationFiniteEndpoint P (fun i => (Events i)ᶜ) Correlated
  have Event : {ω | (n : ℝ)≤∑ i, (Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω}=
      {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤0} := by
    ext ω
    simp only [mem_ofPred_eq,EventComplementCount]
    constructor <;> intro H <;> linarith
  rw [Event,EventComplementMean P Events MeasurableEvents] at Bound
  have Ratio : ((n : ℝ)-(∑ i, P.real (Events i)))/(n : ℝ)=1-(∑ i, P.real (Events i))/(n : ℝ) := by
    rw [sub_div,div_self (Nat.cast_ne_zero.mpr Empty)]
  rw [Ratio] at Bound
  exact Bound

/-- Complement reflection gives the finite-size lower interior formula for
dependent indicators with zero-negative correlation. -/
theorem ZeroNegativeCorrelationFiniteInterior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events)
    (PositiveMean : 0<∑ i, P.real (Events i)) (BelowMaximum : (∑ i, P.real (Events i))<n)
    (d : ℝ) (Nonnegative : 0≤d) (BelowOne : d<1) :
    P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*(∑ i, P.real (Events i))}≤
      FiniteChernoffLowerBound n (∑ i, P.real (Events i)) d := by
  let m := ∑ i, P.real (Events i)
  have MeanComplement := EventComplementMean P Events MeasurableEvents
  have PositiveComplement : 0<∑ i, P.real (Events i)ᶜ := by
    rw [MeanComplement]
    exact sub_pos.mpr BelowMaximum
  have AboveMean : (∑ i, P.real (Events i)ᶜ)≤(n : ℝ)-(1-d)*m := by
    rw [MeanComplement]
    have Product := mul_nonneg Nonnegative PositiveMean.le
    nlinarith
  have Below : (n : ℝ)-(1-d)*m<n := by
    have Product := mul_pos (sub_pos.mpr BelowOne) PositiveMean
    linarith
  have PositiveN : 0<n := Nat.cast_pos.mp (PositiveMean.trans BelowMaximum)
  have Bound := OneNegativeCorrelationFiniteInterior P PositiveN (fun i => (Events i)ᶜ)
    (fun i => (MeasurableEvents i).compl) Correlated PositiveComplement ((n : ℝ)-(1-d)*m) AboveMean Below
  rw [MeanComplement] at Bound
  have Event : {ω | (n : ℝ)-(1-d)*m≤∑ i, (Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω}=
      {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*m} := by
    ext ω
    simp only [mem_ofPred_eq,EventComplementCount]
    constructor <;> intro H <;> linarith
  rw [Event] at Bound
  change P.real _≤(((n : ℝ)-m)/((n : ℝ)-(1-d)*m))^((n : ℝ)-(1-d)*m)*
    (((n : ℝ)-((n : ℝ)-m))/((n : ℝ)-((n : ℝ)-(1-d)*m)))^((n : ℝ)-((n : ℝ)-(1-d)*m)) at Bound
  have Gap : (n : ℝ)-((n : ℝ)-(1-d)*m)=(1-d)*m := by ring
  have MeanGap : (n : ℝ)-((n : ℝ)-m)=m := by ring
  have MNonzero : m≠0 := ne_of_gt PositiveMean
  have Ratio : m/((1-d)*m)=1/(1-d) := by field_simp [MNonzero]
  rw [Gap,MeanGap,Ratio] at Bound
  change P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*m}≤FiniteChernoffLowerBound n m d
  rw [FiniteChernoffLowerBound,if_neg (ne_of_lt BelowOne)]
  exact Bound.trans_eq (mul_comm _ _)

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The strongest finite-size lower expression holds on its full parameter
domain for zero-negatively correlated indicators. -/
theorem ZeroNegativeCorrelationFiniteChernoffLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*(∑ i, P.real (Events i))}≤
      FiniteChernoffLowerBound n (∑ i, P.real (Events i)) d := by
  let m := ∑ i, P.real (Events i)
  have MeanNonnegative : 0≤m := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have MeanAtMostN : m≤(n : ℝ) := by
    calc
      _≤∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => measureReal_le_one)
      _=_ := by simp
  by_cases Endpoint : d=1
  · subst d
    simp only [sub_self,zero_mul,FiniteChernoffLowerBound,ite_true]
    exact ZeroNegativeCorrelationFiniteEndpoint P Events MeasurableEvents Correlated
  by_cases ZeroDeviation : d=0
  · subst d
    rw [FiniteChernoffLowerZeroDeviation]
    exact measureReal_le_one
  by_cases ZeroMean : m=0
  · change P.real _≤FiniteChernoffLowerBound n m d
    rw [ZeroMean,FiniteChernoffLowerZeroMean]
    exact measureReal_le_one
  have PositiveMean : 0<m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
  have BelowOne : d<1 := lt_of_le_of_ne InUnit.2 Endpoint
  by_cases FullMean : m=(n : ℝ)
  · have Bounded (i : Fin n) : ∀ᵐ ω ∂P, (Events i).indicator (fun _ => (1 : ℝ)) ω∈Icc 0 1 := by
      apply ae_of_all
      intro ω
      by_cases Inside : ω∈Events i <;> simp [Inside]
    have IntegralFull : (∫ ω, ∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω ∂P)=(n : ℝ) := by
      rw [EventCountExpectation P Events MeasurableEvents]
      exact FullMean
    have AlwaysMaximal := UnitSumMaximalMeanAE P
      (fun i ω => (Events i).indicator (fun _ => (1 : ℝ)) ω)
      (fun i => (measurable_const.indicator (MeasurableEvents i)).aemeasurable) Bounded IntegralFull
    have NullEvent : P {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*m}=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [AlwaysMaximal] with ω Maximal
      intro Before
      change (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*m at Before
      have PositiveDeviation : 0<d := lt_of_le_of_ne InUnit.1 (Ne.symm ZeroDeviation)
      have Product := mul_pos PositiveDeviation PositiveMean
      rw [Maximal,← FullMean] at Before
      nlinarith
    change P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*m}≤FiniteChernoffLowerBound n m d
    rw [Measure.real,NullEvent,ENNReal.toReal_zero,FiniteChernoffLowerBound,if_neg Endpoint,FullMean,sub_self,zero_div]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  · exact ZeroNegativeCorrelationFiniteInterior P Events MeasurableEvents Correlated
      PositiveMean (lt_of_le_of_ne MeanAtMostN FullMean) d InUnit.1 BelowOne

end
end ECTheoryLib.Probability
