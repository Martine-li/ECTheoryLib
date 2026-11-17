import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationThresholds
import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationVariance
import ECTheoryLib.Probability.Concentration.VarianceFiniteChernoff

/-!
# Strongest finite-size variance tails under negative correlation

Same-sample ordered affine indicators with a centered one-sided bound
of1 yield the full finite-size variance bound. The parameter is the
sum of actual marginal variances. Quadratic MGF normalization may
produce negative coordinates; upper-threshold correlation handles
the closed endpoint without an independence claim. All deterministic
boundaries and the existing finite-to-Bennett comparison apply.
General scale and all mean replacements remain separate.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The variance normalization is still a same-sample ordered affine indicator. -/
theorem VarianceNormalizedAffineIdentity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (a b q : ℝ) (ω : Ω) :
    VarianceNormalizedCoordinate P (fun w => a+(b-a)*E.indicator (fun _ => (1 : ℝ)) w) q ω=
      (a-(∫ w, a+(b-a)*E.indicator (fun _ => (1 : ℝ)) w ∂P)+q)/(1+q)+
      (((b-(∫ w, a+(b-a)*E.indicator (fun _ => (1 : ℝ)) w ∂P)+q)/(1+q))-
        ((a-(∫ w, a+(b-a)*E.indicator (fun _ => (1 : ℝ)) w ∂P)+q)/(1+q)))*
          E.indicator (fun _ => (1 : ℝ)) ω := by
  unfold VarianceNormalizedCoordinate
  ring

theorem OneNegativeCorrelationNormalizedFiniteMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : Fin n → ℝ) (Ordered : ∀ i, a i≤b i)
    (Upper : ∀ i, ∀ᵐ ω ∂P, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω≤
      (∫ w, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w ∂P)+1)
    (q : ℝ) (NonnegativeQ : 0≤q)
    (AverageVariance : (∑ i, variance (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) P)=(n : ℝ)*q)
    (t : ℝ) (NonnegativeTilt : 0≤t) :
    mgf (fun ω => ∑ i, VarianceNormalizedCoordinate P
      (fun w => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) q ω) P t≤
      (1+(q/(1+q))*(Real.exp t-1))^n := by
  let X := fun i ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω
  let Y := fun i => VarianceNormalizedCoordinate P (X i) q
  let A := fun i => (a i-(∫ w, X i w ∂P)+q)/(1+q)
  let B := fun i => (b i-(∫ w, X i w ∂P)+q)/(1+q)
  have PositiveDenominator : 0<1+q := by linarith
  have OrderedAB (i : Fin n) : A i≤B i := by
    apply (div_le_div_iff_of_pos_right PositiveDenominator).mpr
    linarith [Ordered i]
  have Identity (i : Fin n) (ω : Ω) :
      A i+(B i-A i)*(Events i).indicator (fun _ => (1 : ℝ)) ω=Y i ω :=
    (VarianceNormalizedAffineIdentity P (Events i) (a i) (b i) q ω).symm
  have ProductBound := OneNegativeCorrelationAffineMGF P Events MeasurableEvents Correlated A B OrderedAB t NonnegativeTilt
  have EachMGF (i : Fin n) :
      (1-P.real (Events i))*Real.exp (t*A i)+P.real (Events i)*Real.exp (t*B i)=mgf (Y i) P t := by
    rw [← AffineIndicatorMGF P _ (MeasurableEvents i)]
    simp_rw [Identity]
  simp_rw [Identity,EachMGF] at ProductBound
  let C := fun i => 1+t*(q/(1+q))+(∫ ω, (Y i ω)^2 ∂P)*(Real.exp t-1-t)
  have SquareIntegrable (i : Fin n) : MemLp (X i) 2 P :=
    AffineIndicatorMemLpTwo P _ (MeasurableEvents i) _ _ (Ordered i)
  have EachBound (i : Fin n) : mgf (Y i) P t≤C i := by
    have Bound := UpperBoundedQuadraticMGF P (Y i) (VarianceNormalizedMemLp P _ (SquareIntegrable i) q)
      (VarianceNormalizedUpper P _ q NonnegativeQ (Upper i)) t NonnegativeTilt
    rw [VarianceNormalizedMean P _ (SquareIntegrable i) q] at Bound
    exact Bound
  have EachNonnegative (i : Fin n) : 0≤C i := mgf_nonneg.trans (EachBound i)
  apply ProductBound.trans
  calc
    _≤∏ i, C i := Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i _ => EachBound i)
    _≤((∑ i, C i)/(n : ℝ))^n := NonnegativeProductLeMeanPow PositiveLength C EachNonnegative
    _=_ := by
      congr 1
      dsimp only [C,Y]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,
        VarianceNormalizedSecondMomentSum P X SquareIntegrable q NonnegativeQ AverageVariance]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have NonzeroN : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr PositiveLength.ne'
      have NonzeroQ : 1+q≠0 := PositiveDenominator.ne'
      field_simp
      ring

theorem OneNegativeCorrelationNormalizedFiniteEndpoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : Fin n → ℝ) (Ordered : ∀ i, a i≤b i)
    (Upper : ∀ i, ∀ᵐ ω ∂P, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω≤
      (∫ w, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w ∂P)+1)
    (q : ℝ) (NonnegativeQ : 0≤q)
    (AverageVariance : (∑ i, variance (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) P)=(n : ℝ)*q) :
    P.real {ω | (n : ℝ)≤∑ i, VarianceNormalizedCoordinate P
      (fun w => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) q ω}≤(q/(1+q))^n := by
  let X := fun i ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω
  let Y := fun i => VarianceNormalizedCoordinate P (X i) q
  let A := fun i => (a i-(∫ w, X i w ∂P)+q)/(1+q)
  let B := fun i => (b i-(∫ w, X i w ∂P)+q)/(1+q)
  have PositiveDenominator : 0<1+q := by linarith
  have OrderedAB (i : Fin n) : A i≤B i := by
    apply (div_le_div_iff_of_pos_right PositiveDenominator).mpr
    linarith [Ordered i]
  have Identity (i : Fin n) (ω : Ω) :
      A i+(B i-A i)*(Events i).indicator (fun _ => (1 : ℝ)) ω=Y i ω :=
    (VarianceNormalizedAffineIdentity P (Events i) (a i) (b i) q ω).symm
  have ThresholdCorrelation := OneNegativeCorrelationAffineThresholds P Events MeasurableEvents Correlated A B (fun _ => 1) OrderedAB
  simp_rw [Identity] at ThresholdCorrelation
  have SquareIntegrable (i : Fin n) : MemLp (X i) 2 P :=
    AffineIndicatorMemLpTwo P _ (MeasurableEvents i) _ _ (Ordered i)
  have Bound := SumEndpointOfSecondMomentsOfCorrelation P PositiveLength Y
    (fun i => VarianceNormalizedMemLp P _ (SquareIntegrable i) q) ThresholdCorrelation
    (fun i => VarianceNormalizedUpper P _ q NonnegativeQ (Upper i))
  rw [VarianceNormalizedSecondMomentSum P X SquareIntegrable q NonnegativeQ AverageVariance] at Bound
  have Ratio : ((n : ℝ)*q/(1+q))/(n : ℝ)=q/(1+q) := by
    have NonzeroN : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr PositiveLength.ne'
    field_simp
  rwa [Ratio] at Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem OneNegativeCorrelationFiniteVarianceUpperPositive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : Fin n → ℝ) (Ordered : ∀ i, a i≤b i)
    (Upper : ∀ i, ∀ᵐ ω ∂P, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω≤
      (∫ w, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w ∂P)+1)
    (v : ℝ) (PositiveVariance : 0<v)
    (TotalVariance : (∑ i, variance (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) P)=v)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) ∂P)+d≤
      ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)}≤
      FiniteChernoffUpperBound n ((n : ℝ)*v/((n : ℝ)+v)) (d/v) := by
  let X := fun i ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω
  have SquareIntegrable (i : Fin n) : MemLp (X i) 2 P :=
    AffineIndicatorMemLpTwo P _ (MeasurableEvents i) _ _ (Ordered i)
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  let q := v/(n : ℝ)
  let m := (n : ℝ)*q/(1+q)
  let Y := fun i => VarianceNormalizedCoordinate P (X i) q
  have NonnegativeQ : 0≤q := div_nonneg PositiveVariance.le PositiveN.le
  have DenominatorPositive : 0<1+q := by linarith
  have AverageVariance : (∑ i, variance (X i) P)=(n : ℝ)*q := by
    rw [TotalVariance]
    dsimp only [q]
    field_simp
  have MemY (i : Fin n) : MemLp (Y i) 2 P := VarianceNormalizedMemLp P _ (SquareIntegrable i) q
  have UpperY (i : Fin n) : ∀ᵐ ω ∂P, Y i ω≤1 := VarianceNormalizedUpper P _ q NonnegativeQ (Upper i)
  have UpperSum : ∀ᵐ ω ∂P, (∑ i, Y i ω)≤(n : ℝ) := by
    filter_upwards [ae_all_iff.mpr UpperY] with ω Bounds
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => Bounds i)
  have MeanRatio : m/(n : ℝ)=q/(1+q) := by dsimp only [m]; field_simp
  have Certificate (t : ℝ) (Nonnegative : 0≤t) :
      mgf (fun ω => ∑ i, Y i ω) P t≤(1+(m/(n : ℝ))*(Real.exp t-1))^n := by
    rw [MeanRatio]
    exact OneNegativeCorrelationNormalizedFiniteMGF P PositiveLength Events MeasurableEvents Correlated a b Ordered Upper
      q NonnegativeQ AverageVariance t Nonnegative
  have Endpoint : P.real {ω | (n : ℝ)≤∑ i, Y i ω}≤(m/(n : ℝ))^n := by
    rw [MeanRatio]
    exact OneNegativeCorrelationNormalizedFiniteEndpoint P PositiveLength Events MeasurableEvents Correlated a b Ordered Upper
      q NonnegativeQ AverageVariance
  have MeasurableSum : AEMeasurable (fun ω => ∑ i, Y i ω) P := by
    have SumFunction : (∑ i, Y i)=(fun ω => ∑ i, Y i ω) := by funext ω; exact Finset.sum_apply _ _ _
    rw [← SumFunction]
    exact Finset.aemeasurable_sum Finset.univ (fun i _ => (MemY i).aemeasurable)
  have Bound := UpperBoundedFiniteMGFCertificateChernoffUpper P (fun ω => ∑ i, Y i ω) n m
    MeasurableSum UpperSum Certificate Endpoint (by dsimp only [m]; positivity) (d/v)
    (div_nonneg NonnegativeDeviation PositiveVariance.le)
  have TransformThreshold : (1+d/v)*m*(1+q)=v+d := by
    dsimp only [m,q]
    field_simp
  have VarianceScale : (n : ℝ)*q=v := by dsimp only [q]; field_simp
  have Event : {ω | (1+d/v)*m≤∑ i, Y i ω}=
      {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω} := by
    ext ω
    simp only [mem_ofPred_eq,Y,VarianceNormalizedSum P X SquareIntegrable q,
      le_div_iff₀ DenominatorPositive,TransformThreshold,VarianceScale]
    constructor <;> intro h <;> linarith
  have MeanIdentity : m=(n : ℝ)*v/((n : ℝ)+v) := by
    dsimp only [m,q]
    field_simp
  rw [Event,MeanIdentity] at Bound
  exact Bound

/-- Strongest finite-size variance upper tail for the actual affine
negative-correlated family, including deterministic and maximum endpoints. -/
theorem OneNegativeCorrelationFiniteVarianceUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : Fin n → ℝ) (Ordered : ∀ i, a i≤b i)
    (Upper : ∀ i, ∀ᵐ ω ∂P, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω≤
      (∫ w, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w ∂P)+1)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) ∂P)+d≤
      ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)}≤
      VarianceFiniteUpperBound n
        (∑ i, variance (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) P) d := by
  let X := fun i ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω
  have SquareIntegrable (i : Fin n) : MemLp (X i) 2 P :=
    AffineIndicatorMemLpTwo P _ (MeasurableEvents i) _ _ (Ordered i)
  change P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤VarianceFiniteUpperBound n (∑ i, variance (X i) P) d
  by_cases ZeroDeviation : d=0
  · simp only [VarianceFiniteUpperBound,ZeroDeviation,ite_true]
    exact measureReal_le_one
  by_cases Beyond : (n : ℝ)<d
  · simp only [VarianceFiniteUpperBound,ZeroDeviation,Beyond,ite_false,ite_true]
    have MeanSum := integral_finsetSum Finset.univ (fun i _ => (SquareIntegrable i).integrable (by norm_num))
    have EventZero : P {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ae_all_iff.mpr Upper] with ω Bounds
      have Sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Bounds i)
      change (∑ i, X i ω)≤∑ i, ((∫ w, X i w ∂P)+1) at Sum
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,mul_one,← MeanSum] at Sum
      change ¬(∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω
      linarith
    simp only [Measure.real,EventZero,ENNReal.toReal_zero,le_refl]
  by_cases ZeroVariance : (∑ i, variance (X i) P)=0
  · simp only [VarianceFiniteUpperBound,ZeroDeviation,Beyond,ZeroVariance,ite_false,ite_true]
    have Bound := OneNegativeCorrelationAffineBennettUpper P Events MeasurableEvents Correlated a b Ordered Upper d NonnegativeDeviation
    change _≤BennettUpperBound (∑ i, variance (X i) P) d at Bound
    simpa only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false,ite_true] using Bound
  have PositiveVariance : 0<∑ i, variance (X i) P :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) (Ne.symm ZeroVariance)
  have PositiveLength : 0<n := by
    by_contra Empty
    have ZeroN : n=0 := Nat.eq_zero_of_not_pos Empty
    subst n
    simp only [Finset.univ_eq_empty,Finset.sum_empty,lt_self_iff_false] at PositiveVariance
  simp only [VarianceFiniteUpperBound,ZeroDeviation,Beyond,ZeroVariance,ite_false]
  exact OneNegativeCorrelationFiniteVarianceUpperPositive P PositiveLength Events MeasurableEvents Correlated a b Ordered Upper
    _ PositiveVariance rfl d NonnegativeDeviation

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem ZeroNegativeCorrelationFiniteVarianceLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (Events : Fin n → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (a b : Fin n → ℝ) (Ordered : ∀ i, a i≤b i)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w ∂P)-1≤
      a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)
    (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤
      (∫ w, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) ∂P)-d}≤
      VarianceFiniteUpperBound n (∑ i, variance (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) P) d := by
  have UpperNeg (i : Fin n) : ∀ᵐ ω ∂P,
      -b i+(-a i- -b i)*(Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω≤
        (∫ w, -b i+(-a i- -b i)*(Events i)ᶜ.indicator (fun _ => (1 : ℝ)) w ∂P)+1 := by
    simp_rw [NegatedAffineIndicator,integral_neg]
    filter_upwards [Lower i] with ω Bound
    linarith
  have Bound := OneNegativeCorrelationFiniteVarianceUpper P (fun i => (Events i)ᶜ)
    (fun i => (MeasurableEvents i).compl) Correlated (fun i => -b i) (fun i => -a i)
    (fun i => neg_le_neg (Ordered i)) UpperNeg d Nonnegative
  simp_rw [NegatedAffineIndicator,Finset.sum_neg_distrib,integral_neg,variance_fun_neg] at Bound
  have Event : {ω | -(∫ w, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) ∂P)+d≤
      -(∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))}=
      {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤
        (∫ w, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) ∂P)-d} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rwa [Event] at Bound

end
end ECTheoryLib.Probability
