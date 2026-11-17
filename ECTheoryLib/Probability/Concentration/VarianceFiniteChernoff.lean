import ECTheoryLib.Probability.Concentration.Bennett
import ECTheoryLib.Probability.Concentration.LowerChernoff

/-!
# Strongest finite-size variance Chernoff bounds

Doerr1.10.12/13, formula1.10.25, including its literal real-power form,
closed maximum endpoint, impossible-event cutoff and comparison with Bennett.
Independent square-integrable variables need only a one-sided centered
bound of1. Normalized coordinates may be negative: the quadratic moment
certificate and endpoint proof deliberately impose no lower bound.
Zero deviation, zero variance and empty families are explicit extensions.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Common centering and scaling used in the finite-size variance estimate.
The transformed coordinate has upper bound1 but may be negative. -/
def VarianceNormalizedCoordinate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (a : ℝ) (ω : Ω) : ℝ :=
  (X ω-(∫ w, X w ∂P)+a)/(1+a)

theorem VarianceNormalizedMemLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (a : ℝ) :
    MemLp (VarianceNormalizedCoordinate P X a) 2 P := by
  change MemLp (fun ω => (X ω-(∫ w, X w ∂P)+a)/(1+a)) 2 P
  simpa only [div_eq_mul_inv,Pi.sub_apply,Pi.add_apply] using
    ((SquareIntegrable.sub (memLp_const _)).add (memLp_const a)).mul_const (1+a)⁻¹

theorem VarianceNormalizedMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (a : ℝ) :
    (∫ ω, VarianceNormalizedCoordinate P X a ω ∂P)=a/(1+a) := by
  unfold VarianceNormalizedCoordinate
  rw [integral_div,integral_add (f := fun ω => X ω-(∫ w, X w ∂P))
      ((SquareIntegrable.integrable (by norm_num)).sub (integrable_const _))
      (integrable_const _),integral_sub (SquareIntegrable.integrable (by norm_num)) (integrable_const _)]
  simp

theorem VarianceNormalizedSecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (a : ℝ) :
    (∫ ω, (VarianceNormalizedCoordinate P X a ω)^2 ∂P)=(variance X P+a^2)/(1+a)^2 := by
  have Identity := variance_eq_sub (VarianceNormalizedMemLp P X SquareIntegrable a)
  rw [VarianceNormalizedMean P X SquareIntegrable a] at Identity
  have Var : variance (VarianceNormalizedCoordinate P X a) P=variance X P/(1+a)^2 := by
    unfold VarianceNormalizedCoordinate
    simp_rw [div_eq_mul_inv]
    rw [variance_mul_const,variance_add_const (X := fun ω => X ω-(∫ w, X w ∂P))
      (SquareIntegrable.aestronglyMeasurable.sub aestronglyMeasurable_const),
      variance_sub_const SquareIntegrable.aestronglyMeasurable]
    simp only [inv_pow]
  rw [Var] at Identity
  change variance X P/(1+a)^2=(∫ ω, (VarianceNormalizedCoordinate P X a ω)^2 ∂P)-(a/(1+a))^2 at Identity
  rw [div_pow] at Identity
  rw [add_div]
  linarith

theorem VarianceNormalizedUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (a : ℝ) (Nonnegative : 0≤a)
    (Upper : ∀ᵐ ω ∂P, X ω≤(∫ w, X w ∂P)+1) :
    ∀ᵐ ω ∂P, VarianceNormalizedCoordinate P X a ω≤1 := by
  filter_upwards [Upper] with ω Bound
  unfold VarianceNormalizedCoordinate
  apply (div_le_one (by linarith : 0<1+a)).mpr
  linarith

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Normalize by the average variance: the sum of second moments equals
the sum of first moments, even though individual coordinates can be negative. -/
theorem VarianceNormalizedSecondMomentSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (a : ℝ) (Nonnegative : 0≤a)
    (AverageVariance : (∑ i, variance (X i) P)=(n : ℝ)*a) :
    (∑ i, ∫ ω, (VarianceNormalizedCoordinate P (X i) a ω)^2 ∂P)=(n : ℝ)*a/(1+a) := by
  simp_rw [VarianceNormalizedSecondMoment P _ (SquareIntegrable _) a]
  rw [← Finset.sum_div,Finset.sum_add_distrib,AverageVariance]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have Nonzero : 1+a≠0 := ne_of_gt (by linarith)
  field_simp

/-- A finite-size binomial MGF certificate from the actual total variance.
The proof keeps the quadratic MGF polynomial until after AM-GM. -/
theorem VarianceNormalizedFiniteMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (a : ℝ) (Nonnegative : 0≤a)
    (AverageVariance : (∑ i, variance (X i) P)=(n : ℝ)*a)
    (t : ℝ) (NonnegativeTilt : 0≤t) :
    mgf (fun ω => ∑ i, VarianceNormalizedCoordinate P (X i) a ω) P t≤
      (1+(a/(1+a))*(Real.exp t-1))^n := by
  let Y := fun i => VarianceNormalizedCoordinate P (X i) a
  let q := a/(1+a)
  let B := fun i => 1+t*q+(∫ ω, (Y i ω)^2 ∂P)*(Real.exp t-1-t)
  have IndependentY : iIndepFun Y P := Independent.comp
    (fun i x => (x-(∫ w, X i w ∂P)+a)/(1+a)) (fun _ => by fun_prop)
  have EachBound (i : Fin n) : mgf (Y i) P t≤B i := by
    have Bound := UpperBoundedQuadraticMGF P (Y i) (VarianceNormalizedMemLp P _ (SquareIntegrable i) a)
      (VarianceNormalizedUpper P _ a Nonnegative (Upper i)) t NonnegativeTilt
    rw [VarianceNormalizedMean P _ (SquareIntegrable i) a] at Bound
    exact Bound
  have EachNonnegative (i : Fin n) : 0≤B i := mgf_nonneg.trans (EachBound i)
  have Product := IndependentY.mgf_sum₀
    (fun i => (VarianceNormalizedMemLp P _ (SquareIntegrable i) a).aemeasurable) Finset.univ (t := t)
  have SumFunction : (∑ i, Y i)=(fun ω => ∑ i, Y i ω) := by funext ω; exact Finset.sum_apply _ _ _
  rw [SumFunction] at Product
  change mgf (fun ω => ∑ i, Y i ω) P t≤_
  rw [Product]
  calc
    _≤∏ i, B i := Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i _ => EachBound i)
    _≤((∑ i, B i)/(n : ℝ))^n := NonnegativeProductLeMeanPow PositiveLength B EachNonnegative
    _=_ := by
      congr 1
      dsimp only [B,Y,q]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,
        VarianceNormalizedSecondMomentSum P X SquareIntegrable a Nonnegative AverageVariance]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have NonzeroN : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr PositiveLength.ne'
      have NonzeroA : 1+a≠0 := ne_of_gt (by linarith)
      field_simp
      ring

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The closed maximum event is controlled by second moments, allowing
arbitrarily negative coordinates. Independence is for the whole family. -/
theorem IndependentSumEndpointOfSecondMoments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (Y : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (Y i) 2 P)
    (Independent : iIndepFun Y P) (Upper : ∀ i, ∀ᵐ ω ∂P, Y i ω≤1) :
    P.real {ω | (n : ℝ)≤∑ i, Y i ω}≤((∑ i, ∫ ω, (Y i ω)^2 ∂P)/(n : ℝ))^n := by
  classical
  have ConstantSum : (∑ _i : Fin n, (1 : ℝ))=(n : ℝ) := by simp
  have EventEq : {ω | (n : ℝ)≤∑ i, Y i ω}=ᵐ[P]
      (⋂ i∈(Finset.univ : Finset (Fin n)), Y i ⁻¹' Ici 1) := by
    filter_upwards [ae_all_iff.mpr Upper] with ω Bounds
    apply propext
    change ((n : ℝ)≤∑ i, Y i ω)↔ω∈(⋂ i∈(Finset.univ : Finset (Fin n)), Y i ⁻¹' Ici 1)
    simp only [mem_iInter,Finset.mem_univ,mem_preimage,mem_Ici,forall_true_left]
    constructor
    · intro SumLarge i
      by_contra Small
      have Strict := Finset.sum_lt_sum (fun j (_hj : j∈Finset.univ) => Bounds j)
        ⟨i,Finset.mem_univ i,lt_of_not_ge Small⟩
      rw [ConstantSum] at Strict
      exact not_lt_of_ge SumLarge Strict
    · intro EachLarge
      rw [← ConstantSum]
      exact Finset.sum_le_sum (fun i _ => EachLarge i)
  have ProbabilityIdentity := measure_congr EventEq
  rw [Independent.measure_inter_preimage_eq_mul Finset.univ (fun _ _ => measurableSet_Ici)] at ProbabilityIdentity
  have IndividualBound (i : Fin n) : P.real (Y i ⁻¹' Ici 1)≤∫ ω, (Y i ω)^2 ∂P := by
    have Markov := mul_meas_ge_le_integral_of_nonneg (ae_of_all P (fun ω => sq_nonneg (Y i ω)))
      (SquareIntegrable i).integrable_sq 1
    rw [one_mul] at Markov
    apply le_trans _ Markov
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change 1≤Y i ω at hω
    change 1≤(Y i ω)^2
    nlinarith
  change (P {ω | (n : ℝ)≤∑ i, Y i ω}).toReal≤_
  rw [ProbabilityIdentity,ENNReal.toReal_prod]
  calc
    _≤∏ i, ∫ ω, (Y i ω)^2 ∂P :=
      Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun i _ => IndividualBound i)
    _≤_ := NonnegativeProductLeMeanPow PositiveLength _
      (fun i => integral_nonneg (fun ω => sq_nonneg (Y i ω)))

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Finite MGF optimization needs an upper bound only. This variant
accepts transformed variables with negative values. -/
theorem UpperBoundedFiniteMGFCertificateChernoffUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (n : ℕ) (m : ℝ)
    (MeasurableX : AEMeasurable X P) (Upper : ∀ᵐ ω ∂P, X ω≤(n : ℝ))
    (Certificate : ∀ t : ℝ, 0≤t → mgf X P t≤(1+(m/(n : ℝ))*(Real.exp t-1))^n)
    (Endpoint : P.real {ω | (n : ℝ)≤X ω}≤(m/(n : ℝ))^n)
    (MeanNonnegative : 0≤m) (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (1+d)*m≤X ω}≤FiniteChernoffUpperBound n m d := by
  have AboveMean : m≤(1+d)*m := by nlinarith
  unfold FiniteChernoffUpperBound
  split_ifs with AboveMaximum AtMaximum
  · have NullEvent : P {ω | (1+d)*m≤X ω}=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [Upper] with ω Bound
      exact not_le_of_gt (Bound.trans_lt AboveMaximum)
    simp only [Measure.real,NullEvent,ENNReal.toReal_zero,le_refl]
  · rw [AtMaximum]
    exact Endpoint
  · have BelowMaximum : (1+d)*m<(n : ℝ) := lt_of_le_of_ne (le_of_not_gt AboveMaximum) AtMaximum
    by_cases ZeroMean : m=0
    · have PositiveN : (0 : ℝ)<n := by simpa only [ZeroMean,mul_zero] using BelowMaximum
      simp only [ZeroMean,mul_zero,Real.rpow_zero,sub_zero,div_self PositiveN.ne',Real.one_rpow,one_mul]
      exact measureReal_le_one
    · have PositiveMean : 0<m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
      let a := (1+d)*m
      let t := Real.log (a*((n : ℝ)-m)/(m*((n : ℝ)-a)))
      have TiltNonnegative : 0≤t := FiniteChernoffTiltNonnegative n m a PositiveMean AboveMean BelowMaximum
      have IntExp := UpperBoundedExponentialIntegrable P X n t MeasurableX Upper TiltNonnegative
      have Bound := measure_ge_le_exp_mul_mgf a TiltNonnegative IntExp
      apply Bound.trans
      calc
        _≤Real.exp (-t*a)*(1+(m/(n : ℝ))*(Real.exp t-1))^n :=
          mul_le_mul_of_nonneg_left (Certificate t TiltNonnegative) (Real.exp_pos _).le
        _=(m/a)^a*(((n : ℝ)-m)/((n : ℝ)-a))^((n : ℝ)-a) := by
          rw [← Real.rpow_natCast]
          exact FiniteChernoffTiltValue n m a PositiveMean AboveMean BelowMaximum
        _=_ := by
          have Ratio : m/((1+d)*m)=1/(1+d) := by field_simp
          dsimp only [a]
          rw [Ratio]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The normalization retains the actual centered sum, including negative values. -/
theorem VarianceNormalizedSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (a : ℝ) (ω : Ω) :
    (∑ i, VarianceNormalizedCoordinate P (X i) a ω)=
      ((∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)+(n : ℝ)*a)/(1+a) := by
  have MeanSum := integral_finsetSum Finset.univ (fun i _ => (SquareIntegrable i).integrable (by norm_num))
  simp only [VarianceNormalizedCoordinate,← Finset.sum_div,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,MeanSum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- The strongest finite-size variance expression, represented by the
existing finite Chernoff function after the justified affine transform. -/
theorem IndependentSumFiniteVarianceUpperPositive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (v : ℝ) (PositiveVariance : 0<v) (TotalVariance : (∑ i, variance (X i) P)=v)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      FiniteChernoffUpperBound n ((n : ℝ)*v/((n : ℝ)+v)) (d/v) := by
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  let a := v/(n : ℝ)
  let m := (n : ℝ)*a/(1+a)
  let Y := fun i => VarianceNormalizedCoordinate P (X i) a
  have NonnegativeA : 0≤a := div_nonneg PositiveVariance.le PositiveN.le
  have DenominatorPositive : 0<1+a := by linarith
  have AverageVariance : (∑ i, variance (X i) P)=(n : ℝ)*a := by
    rw [TotalVariance]
    dsimp only [a]
    field_simp
  have IndependentY : iIndepFun Y P := Independent.comp
    (fun i x => (x-(∫ w, X i w ∂P)+a)/(1+a)) (fun _ => by fun_prop)
  have MemY (i : Fin n) : MemLp (Y i) 2 P := VarianceNormalizedMemLp P _ (SquareIntegrable i) a
  have UpperY (i : Fin n) : ∀ᵐ ω ∂P, Y i ω≤1 := VarianceNormalizedUpper P _ a NonnegativeA (Upper i)
  have UpperSum : ∀ᵐ ω ∂P, (∑ i, Y i ω)≤(n : ℝ) := by
    filter_upwards [ae_all_iff.mpr UpperY] with ω Bounds
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => Bounds i)
  have MeanRatio : m/(n : ℝ)=a/(1+a) := by dsimp only [m]; field_simp
  have Certificate (t : ℝ) (Nonnegative : 0≤t) :
      mgf (fun ω => ∑ i, Y i ω) P t≤(1+(m/(n : ℝ))*(Real.exp t-1))^n := by
    rw [MeanRatio]
    exact VarianceNormalizedFiniteMGF P PositiveLength X SquareIntegrable Independent Upper
      a NonnegativeA AverageVariance t Nonnegative
  have Endpoint : P.real {ω | (n : ℝ)≤∑ i, Y i ω}≤(m/(n : ℝ))^n := by
    have Bound := IndependentSumEndpointOfSecondMoments P PositiveLength Y MemY IndependentY UpperY
    rw [VarianceNormalizedSecondMomentSum P X SquareIntegrable a NonnegativeA AverageVariance] at Bound
    exact Bound
  have MeasurableSum : AEMeasurable (fun ω => ∑ i, Y i ω) P := by
    have SumFunction : (∑ i, Y i)=(fun ω => ∑ i, Y i ω) := by funext ω; exact Finset.sum_apply _ _ _
    rw [← SumFunction]
    exact Finset.aemeasurable_sum Finset.univ (fun i _ => (MemY i).aemeasurable)
  have Bound := UpperBoundedFiniteMGFCertificateChernoffUpper P (fun ω => ∑ i, Y i ω) n m
    MeasurableSum UpperSum Certificate Endpoint (by dsimp only [m]; positivity) (d/v)
    (div_nonneg NonnegativeDeviation PositiveVariance.le)
  have TransformThreshold : (1+d/v)*m*(1+a)=v+d := by
    dsimp only [m,a]
    field_simp
  have VarianceScale : (n : ℝ)*a=v := by dsimp only [a]; field_simp
  have Event : {ω | (1+d/v)*m≤∑ i, Y i ω}=
      {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω} := by
    ext ω
    simp only [mem_ofPred_eq,Y,VarianceNormalizedSum P X SquareIntegrable a,
      le_div_iff₀ DenominatorPositive,TransformThreshold,VarianceScale]
    constructor <;> intro h <;> linarith
  have MeanIdentity : m=(n : ℝ)*v/((n : ℝ)+v) := by
    dsimp only [m,a]
    field_simp
  rw [Event,MeanIdentity] at Bound
  exact Bound

/-- The source finite-size variance bound, with deterministic and empty
boundaries made explicit. The natural cutoff is the raw deviation d=n. -/
def VarianceFiniteUpperBound (n : ℕ) (v d : ℝ) : ℝ :=
  if d=0 then 1 else if (n : ℝ)<d then 0 else if v=0 then 0
  else FiniteChernoffUpperBound n ((n : ℝ)*v/((n : ℝ)+v)) (d/v)

theorem IndependentSumFiniteVarianceUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      VarianceFiniteUpperBound n (∑ i, variance (X i) P) d := by
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
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,mul_one,← MeanSum] at Sum
      change ¬(∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω
      linarith
    simp only [Measure.real,EventZero,ENNReal.toReal_zero,le_refl]
  by_cases ZeroVariance : (∑ i, variance (X i) P)=0
  · simp only [VarianceFiniteUpperBound,ZeroDeviation,Beyond,ZeroVariance,ite_false,ite_true]
    have Bound := IndependentSumBennettUpperAll P X SquareIntegrable Independent Upper d NonnegativeDeviation
    simpa only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false,ite_true] using Bound
  have PositiveVariance : 0<∑ i, variance (X i) P :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) (Ne.symm ZeroVariance)
  have PositiveLength : 0<n := by
    by_contra Empty
    have ZeroN : n=0 := Nat.eq_zero_of_not_pos Empty
    subst n
    simp only [Finset.univ_eq_empty,Finset.sum_empty,lt_self_iff_false] at PositiveVariance
  simp only [VarianceFiniteUpperBound,ZeroDeviation,Beyond,ZeroVariance,ite_false]
  exact IndependentSumFiniteVarianceUpperPositive P PositiveLength X SquareIntegrable Independent Upper
    _ PositiveVariance rfl d NonnegativeDeviation

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open Set
noncomputable section

/-- The upper-tail logarithmic exponent is at most x²/2 on x≥0. -/
theorem ChernoffExponentQuadraticUpper (d : ℝ) (Nonnegative : 0≤d) :
    (1+d)*Real.log (1+d)-d≤d^2/2 := by
  let f := fun x : ℝ => x^2/2-((1+x)*Real.log (1+x)-x)
  have Derivative (x : ℝ) (Inside : x∈Icc 0 d) : HasDerivAt f (x-Real.log (1+x)) x := by
    have BasePositive : 0<1+x := by linarith [Inside.1]
    have BaseDerivative : HasDerivAt (fun y : ℝ => 1+y) 1 x := (hasDerivAt_id x).const_add 1
    have SquareDerivative : HasDerivAt (fun y : ℝ => y^2/2) (2*x/2) x := by
      simpa only [Nat.cast_ofNat,Nat.add_one_sub_one,pow_one,id_eq,mul_one,Pi.pow_apply] using
        ((hasDerivAt_id x).pow 2).div_const 2
    have Raw := SquareDerivative.sub ((BaseDerivative.mul (BaseDerivative.log BasePositive.ne')).sub (hasDerivAt_id x))
    have Identity : 2*x/2-(1*Real.log (1+x)+(1+x)*(1/(1+x))-1)=x-Real.log (1+x) := by
      field_simp
      ring
    rw [Identity] at Raw
    exact Raw
  have MonotoneF : MonotoneOn f (Icc 0 d) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 d)
    · intro x Inside
      exact (Derivative x Inside).continuousAt.continuousWithinAt
    · intro x Inside
      exact (Derivative x (interior_subset Inside)).hasDerivWithinAt
    · intro x Inside
      have Bound := Real.log_le_sub_one_of_pos (by linarith [(interior_subset Inside).1] : 0<1+x)
      linarith
  have Bound := MonotoneF (show (0 : ℝ)∈Icc 0 d from ⟨le_rfl,Nonnegative⟩)
    (show d∈Icc 0 d from ⟨Nonnegative,le_rfl⟩) Nonnegative
  dsimp only [f] at Bound
  norm_num at Bound
  linarith

/-- Logarithmic form of the printed strongest variance formula. The
outer natural power in the book has been distributed into both exponents. -/
theorem VarianceFiniteUpperBoundInterior {n : ℕ} (v d : ℝ)
    (PositiveVariance : 0<v) (NonnegativeDeviation : 0≤d) (BelowMaximum : d<n) :
    VarianceFiniteUpperBound n v d=
      Real.exp (-((n : ℝ)*(v+d)/((n : ℝ)+v))*Real.log (1+d/v)-
        ((n : ℝ)*((n : ℝ)-d)/((n : ℝ)+v))*Real.log (1-d/(n : ℝ))) := by
  by_cases ZeroDeviation : d=0
  · subst d
    simp [VarianceFiniteUpperBound]
  have PositiveN : (0 : ℝ)<n := NonnegativeDeviation.trans_lt BelowMaximum
  have PositiveDenominator : 0<(n : ℝ)+v := add_pos PositiveN PositiveVariance
  have PositiveBase : 0<1+d/v := by positivity
  have PositiveComplement : 0<1-d/(n : ℝ) := by
    have := (div_lt_one PositiveN).mpr BelowMaximum
    linarith
  let m := (n : ℝ)*v/((n : ℝ)+v)
  have Threshold : (1+d/v)*m=(n : ℝ)*(v+d)/((n : ℝ)+v) := by dsimp only [m]; field_simp
  have Below : (1+d/v)*m<(n : ℝ) := by
    rw [Threshold]
    apply (div_lt_iff₀ PositiveDenominator).mpr
    nlinarith
  have Ratio : ((n : ℝ)-m)/((n : ℝ)-(1+d/v)*m)=1/(1-d/(n : ℝ)) := by
    dsimp only [m]
    field_simp
    ring
  have ComplementExponent : (n : ℝ)-(1+d/v)*m=(n : ℝ)*((n : ℝ)-d)/((n : ℝ)+v) := by
    rw [Threshold]
    field_simp
    ring
  simp only [VarianceFiniteUpperBound,ZeroDeviation,not_lt_of_ge BelowMaximum.le,
    ne_of_gt PositiveVariance,ite_false]
  change FiniteChernoffUpperBound n m (d/v)=_
  rw [FiniteChernoffUpperBound,if_neg (not_lt_of_ge Below.le),if_neg (ne_of_lt Below),Ratio,
    Real.rpow_def_of_pos (div_pos zero_lt_one PositiveBase),
    Real.rpow_def_of_pos (div_pos zero_lt_one PositiveComplement),← Real.exp_add,
    Real.log_div one_ne_zero PositiveBase.ne',Real.log_div one_ne_zero PositiveComplement.ne',
    Real.log_one,zero_sub,zero_sub,ComplementExponent,Threshold]
  congr 1
  ring

theorem VarianceFiniteUpperBoundEndpoint {n : ℕ} (PositiveLength : 0<n)
    (v : ℝ) (PositiveVariance : 0<v) :
    VarianceFiniteUpperBound n v n=(v/((n : ℝ)+v))^n := by
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  have Threshold : (1+(n : ℝ)/v)*((n : ℝ)*v/((n : ℝ)+v))=(n : ℝ) := by field_simp; ring
  simp only [VarianceFiniteUpperBound,PositiveN.ne',lt_self_iff_false,PositiveVariance.ne',ite_false,
    FiniteChernoffUpperBound,Threshold,ite_true]
  congr 1
  field_simp

theorem VarianceFiniteUpperBoundBeyond {n : ℕ} (v d : ℝ) (Beyond : (n : ℝ)<d) :
    VarianceFiniteUpperBound n v d=0 := by
  have PositiveD : 0<d := (Nat.cast_nonneg n).trans_lt Beyond
  simp only [VarianceFiniteUpperBound,PositiveD.ne',Beyond,ite_false,ite_true]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open Set
noncomputable section

/-- The finite-size variance estimate is stronger than Bennett's bound.
The interior comparison balances the two quadratic logarithm estimates. -/
theorem VarianceFiniteUpperBoundLeBennett (n : ℕ) (v d : ℝ)
    (NonnegativeVariance : 0≤v) (NonnegativeDeviation : 0≤d) :
    VarianceFiniteUpperBound n v d≤BennettUpperBound v d := by
  by_cases ZeroDeviation : d=0
  · simp only [VarianceFiniteUpperBound,BennettUpperBound,ZeroDeviation,ite_true,le_refl]
  by_cases ZeroVariance : v=0
  · simp [VarianceFiniteUpperBound,BennettUpperBound,ZeroDeviation,ZeroVariance]
  have PositiveVariance : 0<v := lt_of_le_of_ne NonnegativeVariance (Ne.symm ZeroVariance)
  have PositiveD : 0<d := lt_of_le_of_ne NonnegativeDeviation (Ne.symm ZeroDeviation)
  by_cases Beyond : (n : ℝ)<d
  · rw [VarianceFiniteUpperBoundBeyond v d Beyond]
    simp only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false]
    exact (Real.exp_pos _).le
  have PositiveN : (0 : ℝ)<n := PositiveD.trans_le (le_of_not_gt Beyond)
  have PositiveDenominator : 0<(n : ℝ)+v := add_pos PositiveN PositiveVariance
  by_cases Endpoint : d=(n : ℝ)
  · rw [Endpoint,VarianceFiniteUpperBoundEndpoint (Nat.cast_pos.mp PositiveN) v PositiveVariance]
    simp only [BennettUpperBound,PositiveN.ne',ZeroVariance,ite_false]
    have BasePositive : 0<1+(n : ℝ)/v := by positivity
    have Ratio : v/((n : ℝ)+v)=1/(1+(n : ℝ)/v) := by field_simp; ring
    rw [Ratio,← Real.rpow_natCast,Real.rpow_def_of_pos (div_pos zero_lt_one BasePositive),
      Real.log_div one_ne_zero BasePositive.ne',Real.log_one,zero_sub]
    apply Real.exp_le_exp.mpr
    have LogBound := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos BasePositive) NonnegativeVariance
    have Normalized : v*(1+(n : ℝ)/v-1)=(n : ℝ) := by field_simp; ring
    rw [Normalized] at LogBound
    have Exponent : -v*((1+(n : ℝ)/v)*Real.log (1+(n : ℝ)/v)-(n : ℝ)/v)=
        -(v+(n : ℝ))*Real.log (1+(n : ℝ)/v)+(n : ℝ) := by field_simp; ring
    rw [Exponent]
    nlinarith
  have Below : d<(n : ℝ) := lt_of_le_of_ne (le_of_not_gt Beyond) Endpoint
  rw [VarianceFiniteUpperBoundInterior v d PositiveVariance NonnegativeDeviation Below]
  simp only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false]
  apply Real.exp_le_exp.mpr
  let H := (1+d/v)*Real.log (1+d/v)-d/v
  let G := d/(n : ℝ)+(1-d/(n : ℝ))*Real.log (1-d/(n : ℝ))
  let F := -((n : ℝ)*(v+d)/((n : ℝ)+v))*Real.log (1+d/v)-
    ((n : ℝ)*((n : ℝ)-d)/((n : ℝ)+v))*Real.log (1-d/(n : ℝ))
  have Upper := mul_le_mul_of_nonneg_left
    (ChernoffExponentQuadraticUpper (d/v) (div_nonneg NonnegativeDeviation NonnegativeVariance)) (sq_nonneg v)
  have Lower := mul_le_mul_of_nonneg_left
    (ChernoffLowerExponentQuadratic (d/(n : ℝ))
      ⟨div_nonneg NonnegativeDeviation PositiveN.le,(div_le_one PositiveN).mpr Below.le⟩) (sq_nonneg (n : ℝ))
  have NormalizeV : v^2*((d/v)^2/2)=d^2/2 := by field_simp
  have NormalizeN : (n : ℝ)^2*((d/(n : ℝ))^2/2)=d^2/2 := by field_simp
  rw [NormalizeV] at Upper
  rw [NormalizeN] at Lower
  have Comparison : v^2*H-(n : ℝ)^2*G≤0 := by dsimp only [H,G]; linarith
  have Difference : (F-(-v*H))*((n : ℝ)+v)=v^2*H-(n : ℝ)^2*G := by
    dsimp only [F,H,G]
    field_simp
    ring
  rw [← Difference] at Comparison
  apply sub_nonpos.mp
  apply (mul_le_mul_iff_of_pos_right PositiveDenominator).mp
  simpa only [zero_mul] using Comparison

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Literal real-power layout of Doerr1.10.25 away from the singular
maximum endpoint, whose convention is proved separately. -/
theorem VarianceFiniteUpperBoundBookInterior {n : ℕ} (v d : ℝ)
    (PositiveVariance : 0<v) (NonnegativeDeviation : 0≤d) (BelowMaximum : d<n) :
    VarianceFiniteUpperBound n v d=
      ((1+d/v)^(-((1+d/v)*v/((n : ℝ)+v)))*
        (1-d/(n : ℝ))^(-((1-d/(n : ℝ))*(n : ℝ)/((n : ℝ)+v))))^n := by
  have PositiveN : (0 : ℝ)<n := NonnegativeDeviation.trans_lt BelowMaximum
  have PositiveBase : 0<1+d/v := by positivity
  have PositiveComplement : 0<1-d/(n : ℝ) := by
    have := (div_lt_one PositiveN).mpr BelowMaximum
    linarith
  rw [VarianceFiniteUpperBoundInterior v d PositiveVariance NonnegativeDeviation BelowMaximum,
    Real.rpow_def_of_pos PositiveBase,Real.rpow_def_of_pos PositiveComplement,
    ← Real.exp_add,← Real.exp_nat_mul]
  congr 1
  field_simp
  ring

/-- The full finite-size lower bound uses the same variance and the
opposite one-sided centered premise. -/
theorem IndependentSumFiniteVarianceLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-1≤X i ω)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d}≤
      VarianceFiniteUpperBound n (∑ i, variance (X i) P) d := by
  have IndependentNeg : iIndepFun (fun i ω => -X i ω) P :=
    Independent.comp (fun _ x => -x) (fun _ => measurable_neg)
  have UpperNeg (i : Fin n) : ∀ᵐ ω ∂P, -X i ω≤(∫ w, -X i w ∂P)+1 := by
    rw [integral_neg]
    filter_upwards [Lower i] with ω Bound
    linarith
  have Bound := IndependentSumFiniteVarianceUpper P (fun i ω => -X i ω)
    (fun i => (SquareIntegrable i).neg) IndependentNeg UpperNeg d NonnegativeDeviation
  have Event : {ω | (∫ w, ∑ i, -X i w ∂P)+d≤∑ i, -X i ω}=
      {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d} := by
    simp only [Finset.sum_neg_distrib,integral_neg]
    ext ω
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [Event] at Bound
  simpa only [variance_fun_neg] using Bound

end
end ECTheoryLib.Probability


/-! Estimated sum thresholds retain actual coordinate centers and variances. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The estimate only changes the sum-event threshold, not coordinate centers or variance. -/
theorem IndependentSumFiniteVarianceUpperOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P)≤U)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | U+d≤∑ i, X i ω}≤
      VarianceFiniteUpperBound n (∑ i, variance (X i) P) d := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumFiniteVarianceUpper P X SquareIntegrable Independent Upper d NonnegativeDeviation)
  intro ω Bound
  exact le_trans (add_le_add MeanUpper (le_refl d)) Bound

/-- The estimate only changes the sum-event threshold, not coordinate centers or variance. -/
theorem IndependentSumFiniteVarianceLowerOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-1≤X i ω)
    (L : ℝ) (MeanLower : L≤(∫ w, ∑ i, X i w ∂P))
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤L-d}≤
      VarianceFiniteUpperBound n (∑ i, variance (X i) P) d := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumFiniteVarianceLower P X SquareIntegrable Independent Lower d NonnegativeDeviation)
  intro ω Bound
  exact le_trans Bound (sub_le_sub_right MeanLower d)

end
end ECTheoryLib.Probability



/-! Relative upper thresholds in the finite variance bound use a nonnegative mean estimate. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The multiplicative finite bound is the accepted additive bound at deviation δ * U. -/
theorem IndependentSumFiniteVarianceRelativeUpperOfMeanLe {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + 1)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ U)
    (NonnegativeEstimate : 0 ≤ U) (δ : ℝ) (NonnegativeRelative : 0 ≤ δ) :
    P.real {ω | (1 + δ) * U ≤ ∑ i, X i ω} ≤
      VarianceFiniteUpperBound n (∑ i, variance (X i) P) (δ * U) := by
  have Bound := IndependentSumFiniteVarianceUpperOfMeanLe P X SquareIntegrable Independent Upper
    U MeanUpper (δ * U) (mul_nonneg NonnegativeRelative NonnegativeEstimate)
  simpa only [add_mul, one_mul] using Bound

end
end ECTheoryLib.Probability

