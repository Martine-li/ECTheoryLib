import ECTheoryLib.Probability.Concentration.LowerChernoff

/-!
# Finite-size Chernoff bounds from MGF certificates

Reuse Mathlib exponential Markov and the established scalar optimization.
No independence or event representation is required. The lower interface
uses the actual complement n-X and identifies its mean with the integral.
A separate endpoint certificate avoids a singular optimizing tilt.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Scalar finite-size optimization depends on an MGF certificate, not on
independence or a particular representation of the random variable. -/
theorem FiniteMGFCertificateInterior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (n : ℕ) (m a : ℝ)
    (MeasurableX : AEMeasurable X P) (Bounded : ∀ᵐ ω ∂P, X ω∈Icc 0 (n : ℝ))
    (Certificate : ∀ t : ℝ, 0≤t → mgf X P t≤(1+(m/(n : ℝ))*(Real.exp t-1))^n)
    (PositiveMean : 0<m) (AboveMean : m≤a) (BelowMaximum : a<n) :
    P.real {ω | a≤X ω}≤(m/a)^a*(((n : ℝ)-m)/((n : ℝ)-a))^((n : ℝ)-a) := by
  let t := Real.log (a*((n : ℝ)-m)/(m*((n : ℝ)-a)))
  have TiltNonnegative : 0≤t := FiniteChernoffTiltNonnegative n m a PositiveMean AboveMean BelowMaximum
  have IntegrableExp : Integrable (fun ω => Real.exp (t*X ω)) P :=
    integrable_exp_mul_of_mem_Icc MeasurableX Bounded
  calc
    _ ≤ Real.exp (-t*a)*mgf X P t := measure_ge_le_exp_mul_mgf a TiltNonnegative IntegrableExp
    _ ≤ Real.exp (-t*a)*(1+(m/(n : ℝ))*(Real.exp t-1))^n :=
      mul_le_mul_of_nonneg_left (Certificate t TiltNonnegative) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.rpow_natCast]
      exact FiniteChernoffTiltValue n m a PositiveMean AboveMean BelowMaximum

/-- A finite-size MGF certificate and the closed maximum-event bound give
the complete upper expression, including zero means and empty families. -/
theorem FiniteMGFCertificateChernoffUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (n : ℕ) (m : ℝ)
    (MeasurableX : AEMeasurable X P) (Bounded : ∀ᵐ ω ∂P, X ω∈Icc 0 (n : ℝ))
    (Certificate : ∀ t : ℝ, 0≤t → mgf X P t≤(1+(m/(n : ℝ))*(Real.exp t-1))^n)
    (Endpoint : P.real {ω | (n : ℝ)≤X ω}≤(m/(n : ℝ))^n)
    (MeanNonnegative : 0≤m) (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (1+d)*m≤X ω}≤FiniteChernoffUpperBound n m d := by
  have AboveMean : m≤(1+d)*m := by nlinarith
  unfold FiniteChernoffUpperBound
  split_ifs with AboveMaximum AtMaximum
  · have NullEvent : P {ω | (1+d)*m≤X ω}=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [Bounded] with ω Bound
      exact not_le_of_gt (Bound.2.trans_lt AboveMaximum)
    simp only [Measure.real,NullEvent,ENNReal.toReal_zero,le_refl]
  · rw [AtMaximum]
    exact Endpoint
  · have BelowMaximum : (1+d)*m<(n : ℝ) := lt_of_le_of_ne (le_of_not_gt AboveMaximum) AtMaximum
    by_cases ZeroMean : m=0
    · have PositiveN : (0 : ℝ)<n := by simpa only [ZeroMean,mul_zero] using BelowMaximum
      simp only [ZeroMean,mul_zero,Real.rpow_zero,sub_zero,div_self PositiveN.ne',Real.one_rpow,one_mul]
      exact measureReal_le_one
    · have PositiveMean : 0<m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
      have Bound := FiniteMGFCertificateInterior P X n m ((1+d)*m)
        MeasurableX Bounded Certificate PositiveMean AboveMean BelowMaximum
      have Ratio : m/((1+d)*m)=1/(1+d) := by field_simp
      rwa [Ratio] at Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The lower formula follows from a finite MGF certificate for the actual
complement n-X and its maximum endpoint. The mean is the integral of X. -/
theorem FiniteMGFCertificateChernoffLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (n : ℕ) (m : ℝ)
    (MeasurableX : AEMeasurable X P) (Bounded : ∀ᵐ ω ∂P, X ω∈Icc 0 (n : ℝ))
    (ActualMean : (∫ ω, X ω ∂P)=m)
    (Certificate : ∀ t : ℝ, 0≤t → mgf (fun ω => (n : ℝ)-X ω) P t≤
      (1+(((n : ℝ)-m)/(n : ℝ))*(Real.exp t-1))^n)
    (Endpoint : P.real {ω | X ω≤0}≤(1-m/(n : ℝ))^n)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | X ω≤(1-d)*m}≤FiniteChernoffLowerBound n m d := by
  have IntegrableX := Integrable.of_mem_Icc 0 (n : ℝ) MeasurableX Bounded
  have MeanNonnegative : 0≤m := by
    rw [← ActualMean]
    exact integral_nonneg_of_ae (Bounded.mono (fun _ H => H.1))
  have MeanAtMostN : m≤(n : ℝ) := by
    rw [← ActualMean]
    calc
      _ ≤ ∫ _ω, (n : ℝ) ∂P := integral_mono_ae IntegrableX (integrable_const _)
        (Bounded.mono (fun _ H => H.2))
      _ = _ := by simp
  by_cases AtEndpoint : d=1
  · subst d
    simpa only [sub_self,zero_mul,FiniteChernoffLowerBound,ite_true] using Endpoint
  by_cases ZeroDeviation : d=0
  · subst d
    rw [FiniteChernoffLowerZeroDeviation]
    exact measureReal_le_one
  by_cases ZeroMean : m=0
  · rw [ZeroMean,FiniteChernoffLowerZeroMean]
    exact measureReal_le_one
  have PositiveMean : 0<m := lt_of_le_of_ne MeanNonnegative (Ne.symm ZeroMean)
  have BelowOne : d<1 := lt_of_le_of_ne InUnit.2 AtEndpoint
  by_cases FullMean : m=(n : ℝ)
  · have IntegralComplement : (∫ ω, (n : ℝ)-X ω ∂P)=0 := by
      rw [integral_sub (integrable_const _) IntegrableX,ActualMean,FullMean]
      simp
    have NonnegativeComplement : (0 : Ω → ℝ)≤ᵐ[P](fun ω => (n : ℝ)-X ω) :=
      Bounded.mono (fun _ H => sub_nonneg.mpr H.2)
    have AlwaysMaximal := (integral_eq_zero_iff_of_nonneg_ae NonnegativeComplement
      ((integrable_const _).sub IntegrableX)).mp IntegralComplement
    have NullEvent : P {ω | X ω≤(1-d)*m}=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [AlwaysMaximal] with ω Maximal
      intro Before
      change X ω≤(1-d)*m at Before
      change (n : ℝ)-X ω=0 at Maximal
      have PositiveDeviation : 0<d := lt_of_le_of_ne InUnit.1 (Ne.symm ZeroDeviation)
      have Product := mul_pos PositiveDeviation PositiveMean
      rw [← FullMean] at Maximal
      nlinarith
    rw [Measure.real,NullEvent,ENNReal.toReal_zero,FiniteChernoffLowerBound,
      if_neg AtEndpoint,FullMean,sub_self,zero_div]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have BelowMaximum : m<(n : ℝ) := lt_of_le_of_ne MeanAtMostN FullMean
  have AboveComplementMean : (n : ℝ)-m≤(n : ℝ)-(1-d)*m := by
    have Product := mul_nonneg InUnit.1 MeanNonnegative
    nlinarith
  have BelowComplementMaximum : (n : ℝ)-(1-d)*m<n := by
    have Product := mul_pos (sub_pos.mpr BelowOne) PositiveMean
    linarith
  have ComplementBounded : ∀ᵐ ω ∂P, (n : ℝ)-X ω∈Icc 0 (n : ℝ) := by
    filter_upwards [Bounded] with ω H
    constructor <;> linarith [H.1,H.2]
  have Bound := FiniteMGFCertificateInterior P (fun ω => (n : ℝ)-X ω) n
    ((n : ℝ)-m) ((n : ℝ)-(1-d)*m) (aemeasurable_const.sub MeasurableX)
    ComplementBounded Certificate (sub_pos.mpr BelowMaximum) AboveComplementMean BelowComplementMaximum
  have Event : {ω | (n : ℝ)-(1-d)*m≤(n : ℝ)-X ω}={ω | X ω≤(1-d)*m} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  rw [Event] at Bound
  have Gap : (n : ℝ)-((n : ℝ)-(1-d)*m)=(1-d)*m := by ring
  have MeanGap : (n : ℝ)-((n : ℝ)-m)=m := by ring
  have Ratio : m/((1-d)*m)=1/(1-d) := by field_simp
  rw [Gap,MeanGap,Ratio] at Bound
  rw [FiniteChernoffLowerBound,if_neg AtEndpoint]
  exact Bound.trans_eq (mul_comm _ _)

end
end ECTheoryLib.Probability
