import ECTheoryLib.Probability.Concentration.FiniteChernoff

/-!
# Complete multiplicative Chernoff lower tails

Doerr Theorem 1.10.5, printed page 45: all three displayed bounds and
comparisons, including empty families, zero/full means and d=0 or d=1.
The strongest finite-size bound reuses the existing upper bound through
complement variables. Variables may be nonidentical, real-valued and
bounded almost surely. Mathlib provides exponential Markov, logarithmic
estimates, integration and calculus; 0^0=1 is retained explicitly.
-/

namespace ECTheoryLib.Probability
open Set
noncomputable section

/-- The lower-tail logarithmic exponent has the sharper quadratic constant
one half. The endpoint d=1 is handled without taking log of a positive base. -/
theorem ChernoffLowerExponentQuadratic (d : ℝ) (InUnit : d∈Icc 0 1) :
    d^2/2≤d+(1-d)*Real.log (1-d) := by
  by_cases Endpoint : d=1
  · subst d
    norm_num
  have BelowOne : d<1 := lt_of_le_of_ne InUnit.2 Endpoint
  let f : ℝ → ℝ := fun x => x+(1-x)*Real.log (1-x)-x^2/2
  let g : ℝ → ℝ := fun x => -Real.log (1-x)-x
  have Derivative (x : ℝ) (Inside : x∈Icc 0 d) : HasDerivAt f (g x) x := by
    have BasePositive : 0<1-x := by linarith [Inside.2]
    have BaseDerivative : HasDerivAt (fun y : ℝ => 1-y) (-1) x := (hasDerivAt_id x).const_sub 1
    have SquareDerivative : HasDerivAt (fun y : ℝ => y^2/2) (2*x/2) x := by
      simpa only [Nat.cast_ofNat,Nat.add_one_sub_one,pow_one,id_eq,mul_one,Pi.pow_apply] using
        ((hasDerivAt_id x).pow 2).div_const 2
    have Raw := ((hasDerivAt_id x).add (BaseDerivative.mul (BaseDerivative.log BasePositive.ne'))).sub SquareDerivative
    have Identity : 1+((-1)*Real.log (1-x)+(1-x)*((-1)/(1-x)))-2*x/2=g x := by
      dsimp [g]
      field_simp
      ring
    rw [Identity] at Raw
    exact Raw
  have DerivativeNonnegative (x : ℝ) (Inside : x∈Icc 0 d) : 0≤g x := by
    have BasePositive : 0<1-x := by linarith [Inside.2]
    have Bound := Real.log_le_sub_one_of_pos BasePositive
    dsimp [g]
    linarith
  have MonotoneF : MonotoneOn f (Icc 0 d) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 d)
    · intro x Inside
      exact (Derivative x Inside).continuousAt.continuousWithinAt
    · intro x Inside
      exact (Derivative x (interior_subset Inside)).hasDerivWithinAt
    · intro x Inside
      exact DerivativeNonnegative x (interior_subset Inside)
  have Bound := MonotoneF (show (0 : ℝ)∈Icc 0 d from ⟨le_rfl,InUnit.1⟩)
    (show d∈Icc 0 d from ⟨InUnit.1,le_rfl⟩) InUnit.1
  dsimp [f] at Bound
  norm_num at Bound
  linarith

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section

/-- The negative optimizing tilt gives the lower-tail logarithmic expression
strictly before d=1. Endpoint estimates require a separate argument. -/
theorem MGFMultiplicativeLowerTailInterior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (m d : ℝ)
    (Nonnegative : 0≤d) (BelowOne : d<1)
    (IntegrableExp : Integrable (fun ω => Real.exp (Real.log (1-d)*X ω)) P)
    (Certificate : mgf X P (Real.log (1-d))≤Real.exp (-m*d)) :
    P.real {ω | X ω≤(1-d)*m}≤Real.exp (-(d+(1-d)*Real.log (1-d))*m) := by
  have NonpositiveLog : Real.log (1-d)≤0 := Real.log_nonpos (by linarith) (by linarith)
  have Bound := measure_le_le_exp_mul_mgf ((1-d)*m) NonpositiveLog IntegrableExp
  apply Bound.trans
  calc
    _≤Real.exp (-Real.log (1-d)*((1-d)*m))*Real.exp (-m*d) :=
      mul_le_mul_of_nonneg_left Certificate (Real.exp_pos _).le
    _=_ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Independent bounded variables supply the negative-tilt certificate. -/
theorem UnitIndependentSumChernoffLowerInterior {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Set.Icc 0 1)
    (d : ℝ) (Nonnegative : 0≤d) (BelowOne : d<1) :
    P.real {ω | (∑ i, X i ω)≤(1-d)*(∫ w, ∑ i, X i w ∂P)}≤
      Real.exp (-(d+(1-d)*Real.log (1-d))*(∫ w, ∑ i, X i w ∂P)) := by
  have MeasurableSum : AEMeasurable (fun ω => ∑ i, X i ω) P := by
    have SumFunction : (∑ i, X i)=(fun ω => ∑ i, X i ω) := funext (fun ω => Finset.sum_apply _ _ _)
    rw [← SumFunction]
    exact Finset.aemeasurable_sum _ (fun i _ => MeasurableX i)
  have SumBounded : ∀ᵐ ω ∂P, (∑ i, X i ω)∈Set.Icc 0 (Fintype.card ι : ℝ) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    constructor
    · exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
    · calc
        _≤∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _=_ := by simp
  have Certificate := UnitIndependentSumMGFBound P X MeasurableX Independent Bounded (Real.log (1-d))
  rw [Real.exp_log (by linarith : 0<1-d)] at Certificate
  have Exponent : (∫ w, ∑ i, X i w ∂P)*(1-d-1)= -(∫ w, ∑ i, X i w ∂P)*d := by ring
  rw [Exponent] at Certificate
  exact MGFMultiplicativeLowerTailInterior P _ _ d Nonnegative BelowOne
    (integrable_exp_mul_of_mem_Icc MeasurableSum SumBounded) Certificate

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem UnitComplementSum {Ω ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (ω : Ω) :
    (∑ i, (1-X i ω))=(Fintype.card ι : ℝ)-∑ i, X i ω := by
  rw [Finset.sum_sub_distrib]
  simp

theorem UnitComplementMean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Icc 0 1) :
    (∫ ω, ∑ i, (1-X i ω) ∂P)=(Fintype.card ι : ℝ)-(∫ ω, ∑ i, X i ω ∂P) := by
  have IntegrableSum := integrable_finsetSum Finset.univ
    (fun i _ => Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i))
  simp_rw [UnitComplementSum]
  rw [integral_sub (integrable_const _) IntegrableSum,integral_const,probReal_univ,one_smul]

/-- The lower endpoint is the upper endpoint of the complementary family.
This includes empty families and a zero mean. -/
theorem UnitIndependentSumChernoffLowerEndpoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Icc 0 1) :
    P.real {ω | (∑ i, X i ω)≤0}≤(1-(∫ w, ∑ i, X i w ∂P)/(n : ℝ))^n := by
  have MeasurableY (i : Fin n) : AEMeasurable (fun ω => 1-X i ω) P := aemeasurable_const.sub (MeasurableX i)
  have IndependentY := Independent.comp (fun (_ : Fin n) (x : ℝ) => 1-x)
    (fun _ => measurable_const.sub measurable_id)
  have BoundedY (i : Fin n) : ∀ᵐ ω ∂P, 1-X i ω∈Icc 0 1 := by
    filter_upwards [Bounded i] with ω Inside
    constructor <;> linarith [Inside.1,Inside.2]
  have Bound := UnitIndependentSumFiniteChernoffEndpoint P (fun i ω => 1-X i ω) MeasurableY IndependentY BoundedY
  rw [UnitComplementMean P X MeasurableX Bounded,Fintype.card_fin] at Bound
  have Event : {ω | (n : ℝ)≤∑ i, (1-X i ω)}={ω | (∑ i, X i ω)≤0} := by
    ext ω
    simp only [Set.mem_ofPred_eq,UnitComplementSum,Fintype.card_fin]
    constructor <;> intro H <;> linarith
  rw [Event] at Bound
  by_cases Empty : n=0
  · subst n
    simpa only [pow_zero] using Bound
  · have Ratio : ((n : ℝ)-(∫ w, ∑ i, X i w ∂P))/(n : ℝ)=1-(∫ w, ∑ i, X i w ∂P)/(n : ℝ) := by
      field_simp
    rwa [Ratio] at Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
noncomputable section

/-- The source's real-power form agrees with the logarithmic expression,
including d=1 under Mathlib's convention 0^0=1. -/
theorem ChernoffLowerPowerExpression (d m : ℝ) (InUnit : d∈Set.Icc 0 1) :
    (Real.exp (-d)/(1-d)^(1-d))^m=Real.exp (-(d+(1-d)*Real.log (1-d))*m) := by
  by_cases Endpoint : d=1
  · subst d
    simp only [sub_self,Real.rpow_zero,div_one,zero_mul,add_zero]
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  · have BasePositive : 0<1-d := sub_pos.mpr (lt_of_le_of_ne InUnit.2 Endpoint)
    have DenPositive := Real.rpow_pos_of_pos BasePositive (1-d)
    rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) DenPositive),
      Real.log_div (Real.exp_ne_zero _) DenPositive.ne',Real.log_exp,Real.log_rpow BasePositive]
    congr 1
    ring

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The strongest source lower-tail expression has a separate d=1 endpoint. -/
def FiniteChernoffLowerBound (n : ℕ) (m d : ℝ) : ℝ :=
  if d=1 then (1-m/(n : ℝ))^n
  else (1/(1-d))^((1-d)*m)*(((n : ℝ)-m)/((n : ℝ)-(1-d)*m))^((n : ℝ)-(1-d)*m)

theorem FiniteChernoffLowerZeroMean (n : ℕ) (d : ℝ) : FiniteChernoffLowerBound n 0 d=1 := by
  unfold FiniteChernoffLowerBound
  split_ifs
  · simp
  · by_cases Empty : n=0
    · subst n
      simp
    · simp [Nat.cast_ne_zero.mpr Empty]

theorem FiniteChernoffLowerZeroDeviation (n : ℕ) (m : ℝ) : FiniteChernoffLowerBound n m 0=1 := by
  unfold FiniteChernoffLowerBound
  simp only [zero_ne_one,if_false,sub_zero,one_div_one,one_mul,Real.one_rpow]
  by_cases GapZero : (n : ℝ)-m=0
  · rw [GapZero]
    simp
  · rw [div_self GapZero,Real.one_rpow]

/-- Reflection in the interval endpoints reuses the verified sharp upper
bound; no separate finite-size MGF optimization is required. -/
theorem UnitIndependentSumFiniteChernoffLowerInterior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Icc 0 1)
    (PositiveMean : 0<(∫ ω, ∑ i, X i ω ∂P))
    (BelowMaximum : (∫ ω, ∑ i, X i ω ∂P)<n)
    (d : ℝ) (Nonnegative : 0≤d) (BelowOne : d<1) :
    P.real {ω | (∑ i, X i ω)≤(1-d)*(∫ w, ∑ i, X i w ∂P)}≤
      FiniteChernoffLowerBound n (∫ w, ∑ i, X i w ∂P) d := by
  let m := ∫ w, ∑ i, X i w ∂P
  have MeasurableY (i : Fin n) : AEMeasurable (fun ω => 1-X i ω) P := aemeasurable_const.sub (MeasurableX i)
  have IndependentY := Independent.comp (fun (_ : Fin n) (x : ℝ) => 1-x)
    (fun _ => measurable_const.sub measurable_id)
  have BoundedY (i : Fin n) : ∀ᵐ ω ∂P, 1-X i ω∈Icc 0 1 := by
    filter_upwards [Bounded i] with ω Inside
    constructor <;> linarith [Inside.1,Inside.2]
  have MeanY : (∫ ω, ∑ i, (1-X i ω) ∂P)=(n : ℝ)-m := by
    simpa only [Fintype.card_fin] using UnitComplementMean P X MeasurableX Bounded
  have PositiveN : 0<n := Nat.cast_pos.mp (PositiveMean.trans BelowMaximum)
  have PositiveComplement : 0<(∫ ω, ∑ i, (1-X i ω) ∂P) := by rw [MeanY]; exact sub_pos.mpr BelowMaximum
  have AboveMean : (∫ ω, ∑ i, (1-X i ω) ∂P)≤(n : ℝ)-(1-d)*m := by
    rw [MeanY]
    have Product := mul_nonneg Nonnegative PositiveMean.le
    nlinarith
  have Below : (n : ℝ)-(1-d)*m<n := by
    have Product := mul_pos (sub_pos.mpr BelowOne) PositiveMean
    linarith
  have Bound := UnitIndependentSumFiniteChernoffInterior P PositiveN (fun i ω => 1-X i ω)
    MeasurableY IndependentY BoundedY PositiveComplement ((n : ℝ)-(1-d)*m) AboveMean Below
  rw [MeanY] at Bound
  have Event : {ω | (n : ℝ)-(1-d)*m≤∑ i, (1-X i ω)}={ω | (∑ i, X i ω)≤(1-d)*m} := by
    ext ω
    simp only [Set.mem_ofPred_eq,UnitComplementSum,Fintype.card_fin]
    constructor <;> intro H <;> linarith
  rw [Event] at Bound
  have Gap : (n : ℝ)-((n : ℝ)-(1-d)*m)=(1-d)*m := by ring
  have MeanGap : (n : ℝ)-((n : ℝ)-m)=m := by ring
  have MNonzero : m≠0 := ne_of_gt PositiveMean
  have Ratio : m/((1-d)*m)=1/(1-d) := by field_simp [MNonzero]
  rw [Gap,MeanGap,Ratio] at Bound
  change P.real {ω | (∑ i, X i ω)≤(1-d)*m}≤FiniteChernoffLowerBound n m d
  rw [FiniteChernoffLowerBound,if_neg (ne_of_lt BelowOne)]
  exact Bound.trans_eq (mul_comm _ _)

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- A unit-interval sum attaining its maximal mean is maximal almost surely. -/
theorem UnitSumMaximalMeanAE {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Icc 0 1)
    (FullMean : (∫ ω, ∑ i, X i ω ∂P)=(n : ℝ)) :
    ∀ᵐ ω ∂P, (∑ i, X i ω)=(n : ℝ) := by
  have IntegralComplement : (∫ ω, ∑ i, (1-X i ω) ∂P)=0 := by
    rw [UnitComplementMean P X MeasurableX Bounded,Fintype.card_fin,FullMean,sub_self]
  have IntegrableComplement := integrable_finsetSum Finset.univ
    (fun i _ => (integrable_const (1 : ℝ)).sub (Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i)))
  have NonnegativeComplement : (0 : Ω → ℝ)≤ᵐ[P](fun ω => ∑ i, (1-X i ω)) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (Bounds i).2)
  have Zero := (integral_eq_zero_iff_of_nonneg_ae NonnegativeComplement IntegrableComplement).mp IntegralComplement
  filter_upwards [Zero] with ω Equal
  change (∑ i, (1-X i ω))=0 at Equal
  rw [UnitComplementSum,Fintype.card_fin] at Equal
  linarith

/-- The full strongest finite-size lower tail has no hidden positivity or
interior assumptions on the mean, family size or relative deviation. -/
theorem UnitIndependentSumFiniteChernoffLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Icc 0 1)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, X i ω)≤(1-d)*(∫ w, ∑ i, X i w ∂P)}≤
      FiniteChernoffLowerBound n (∫ w, ∑ i, X i w ∂P) d := by
  let m := ∫ w, ∑ i, X i w ∂P
  have IntegrableSum := integrable_finsetSum Finset.univ
    (fun i _ => Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i))
  have SumBounds : ∀ᵐ ω ∂P, (∑ i, X i ω)∈Icc 0 (n : ℝ) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    constructor
    · exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
    · calc
        _≤∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _=_ := by simp
  have MeanNonnegative : 0≤m := integral_nonneg_of_ae (SumBounds.mono (fun _ Bound => Bound.1))
  have MeanAtMostN : m≤n := by
    have Bound := integral_mono_ae IntegrableSum (integrable_const (n : ℝ))
      (SumBounds.mono (fun _ Bound => Bound.2))
    simpa only [integral_const,probReal_univ,one_smul] using Bound
  by_cases Endpoint : d=1
  · subst d
    simp only [sub_self,zero_mul,FiniteChernoffLowerBound,ite_true]
    exact UnitIndependentSumChernoffLowerEndpoint P X MeasurableX Independent Bounded
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
  · have AlwaysMaximal := UnitSumMaximalMeanAE P X MeasurableX Bounded FullMean
    have NullEvent : P {ω | (∑ i, X i ω)≤(1-d)*m}=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [AlwaysMaximal] with ω Maximal
      intro Before
      change (∑ i, X i ω)≤(1-d)*m at Before
      have PositiveDeviation : 0<d := lt_of_le_of_ne InUnit.1 (Ne.symm ZeroDeviation)
      have Product := mul_pos PositiveDeviation PositiveMean
      rw [Maximal,← FullMean] at Before
      nlinarith
    change P.real {ω | (∑ i, X i ω)≤(1-d)*m}≤FiniteChernoffLowerBound n m d
    rw [Measure.real,NullEvent,ENNReal.toReal_zero,FiniteChernoffLowerBound,if_neg Endpoint,FullMean,sub_self,zero_div]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  · exact UnitIndependentSumFiniteChernoffLowerInterior P X MeasurableX Independent Bounded
      PositiveMean (lt_of_le_of_ne MeanAtMostN FullMean) d InUnit.1 BelowOne

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Logarithmic relaxation of the finite-size lower expression in its interior. -/
theorem FiniteChernoffLowerInteriorLeExp (N m d : ℝ)
    (NonnegativeMean : 0≤m) (BelowMaximum : m<N)
    (NonnegativeDeviation : 0≤d) (BelowOne : d<1) :
    (1/(1-d))^((1-d)*m)*((N-m)/(N-(1-d)*m))^(N-(1-d)*m)≤
      Real.exp (-(d+(1-d)*Real.log (1-d))*m) := by
  have PositiveBase : 0<1-d := sub_pos.mpr BelowOne
  have ThresholdBelow : (1-d)*m≤m := by nlinarith
  have GapPositive : 0<N-(1-d)*m := sub_pos.mpr (ThresholdBelow.trans_lt BelowMaximum)
  have MeanGapPositive : 0<N-m := sub_pos.mpr BelowMaximum
  have RatioPositive : 0<(N-m)/(N-(1-d)*m) := div_pos MeanGapPositive GapPositive
  rw [Real.rpow_def_of_pos (div_pos zero_lt_one PositiveBase),
    Real.rpow_def_of_pos RatioPositive,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div one_ne_zero PositiveBase.ne',Real.log_one,zero_sub]
  have LogBound := mul_le_mul_of_nonneg_right
    (Real.log_le_sub_one_of_pos RatioPositive) GapPositive.le
  have Normalize : ((N-m)/(N-(1-d)*m)-1)*(N-(1-d)*m)= -d*m := by
    rw [sub_mul,div_mul_cancel₀ _ GapPositive.ne']
    ring
  rw [Normalize] at LogBound
  nlinarith

/-- The full finite-size lower bound dominates all boundary cases correctly
and is bounded by the usual logarithmic Chernoff expression. -/
theorem FiniteChernoffLowerBoundLeExp (n : ℕ) (m d : ℝ)
    (MeanBounds : m∈Icc 0 (n : ℝ)) (InUnit : d∈Icc 0 1) :
    FiniteChernoffLowerBound n m d≤Real.exp (-(d+(1-d)*Real.log (1-d))*m) := by
  by_cases ZeroMean : m=0
  · rw [ZeroMean,FiniteChernoffLowerZeroMean,mul_zero,Real.exp_zero]
  by_cases ZeroDeviation : d=0
  · rw [ZeroDeviation,FiniteChernoffLowerZeroDeviation]
    simp
  have PositiveMean : 0<m := lt_of_le_of_ne MeanBounds.1 (Ne.symm ZeroMean)
  have PositiveN : (0 : ℝ)<n := PositiveMean.trans_le MeanBounds.2
  by_cases Endpoint : d=1
  · rw [Endpoint,FiniteChernoffLowerBound,if_pos rfl]
    simp only [sub_self,zero_mul,add_zero,neg_mul,one_mul]
    have NonnegativeBase : 0≤1-m/(n : ℝ) := sub_nonneg.mpr ((div_le_one PositiveN).mpr MeanBounds.2)
    have BaseBound : 1-m/(n : ℝ)≤Real.exp (-m/(n : ℝ)) := by
      have Bound := Real.add_one_le_exp (-m/(n : ℝ))
      simpa only [neg_div,sub_eq_add_neg,add_comm] using Bound
    have Powered := pow_le_pow_left₀ NonnegativeBase BaseBound n
    have Identity : (Real.exp (-m/(n : ℝ)))^n=Real.exp (-m) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    exact Powered.trans_eq Identity
  have BelowOne : d<1 := lt_of_le_of_ne InUnit.2 Endpoint
  rw [FiniteChernoffLowerBound,if_neg Endpoint]
  by_cases FullMean : m=(n : ℝ)
  · have PositiveDeviation : 0<d := lt_of_le_of_ne InUnit.1 (Ne.symm ZeroDeviation)
    have PositiveGap : 0<(n : ℝ)-(1-d)*m := by
      have Product := mul_pos PositiveDeviation PositiveMean
      rw [← FullMean]
      nlinarith
    rw [FullMean,sub_self,zero_div,Real.zero_rpow (ne_of_gt (by simpa only [FullMean] using PositiveGap)),mul_zero]
    exact (Real.exp_pos _).le
  · exact FiniteChernoffLowerInteriorLeExp n m d MeanBounds.1
      (lt_of_le_of_ne MeanBounds.2 FullMean) InUnit.1 BelowOne

/-- Theorem 1.10.5, logarithmic lower tail, including d=1 and all mean boundaries. -/
theorem UnitIndependentSumChernoffLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Icc 0 1)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, X i ω)≤(1-d)*(∫ w, ∑ i, X i w ∂P)}≤
      Real.exp (-(d+(1-d)*Real.log (1-d))*(∫ w, ∑ i, X i w ∂P)) := by
  have SumBounds : ∀ᵐ ω ∂P, (∑ i, X i ω)∈Icc 0 (n : ℝ) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    constructor
    · exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
    · calc
        _≤∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _=_ := by simp
  have IntegrableSum := integrable_finsetSum Finset.univ
    (fun i _ => Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i))
  have MeanBounds : (∫ ω, ∑ i, X i ω ∂P)∈Icc 0 (n : ℝ) := by
    constructor
    · exact integral_nonneg_of_ae (SumBounds.mono (fun _ Bound => Bound.1))
    · have Bound := integral_mono_ae IntegrableSum (integrable_const (n : ℝ))
        (SumBounds.mono (fun _ Bound => Bound.2))
      simpa only [integral_const,probReal_univ,one_smul] using Bound
  exact (UnitIndependentSumFiniteChernoffLower P X MeasurableX Independent Bounded d InUnit).trans
    (FiniteChernoffLowerBoundLeExp n _ d MeanBounds InUnit)

/-- The source power form uses the explicit 0^0=1 convention at d=1. -/
theorem UnitIndependentSumChernoffLowerPower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Icc 0 1)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, X i ω)≤(1-d)*(∫ w, ∑ i, X i w ∂P)}≤
      (Real.exp (-d)/(1-d)^(1-d))^(∫ w, ∑ i, X i w ∂P) := by
  rw [ChernoffLowerPowerExpression d _ InUnit]
  exact UnitIndependentSumChernoffLower P X MeasurableX Independent Bounded d InUnit

/-- The quadratic relaxation retains the closed lower event, including zero mean. -/
theorem UnitIndependentSumChernoffLowerQuadratic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω∈Icc 0 1)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, X i ω)≤(1-d)*(∫ w, ∑ i, X i w ∂P)}≤
      Real.exp (-(d^2/2)*(∫ w, ∑ i, X i w ∂P)) := by
  apply (UnitIndependentSumChernoffLower P X MeasurableX Independent Bounded d InUnit).trans
  apply Real.exp_le_exp.mpr
  have MeanNonnegative : 0≤(∫ ω, ∑ i, X i ω ∂P) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  exact mul_le_mul_of_nonneg_right (neg_le_neg (ChernoffLowerExponentQuadratic d InUnit)) MeanNonnegative

end
end ECTheoryLib.Probability
