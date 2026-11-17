import ECTheoryLib.Probability.Concentration.ChernoffExponent
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Multiplicative Chernoff upper tail for independent unit-interval variables

This module provides the logarithmic and real-power upper bounds of Doerr
Theorem 1.10.1, together with base-two, quadratic, minimum and small-deviation
consequences. The strongest finite-size formula is in `FiniteChernoff.lean`;
estimated-mean interfaces are in `ChernoffMeanUpper.lean`.

Mathlib supplies convexity of exp, integrability of exponentials of bounded
variables, independent MGF factorization and the exponential Markov bound.
The local argument supplies the unit-interval chord and the optimizing tilt.
Variables may be continuous and nonidentically distributed. Interval bounds
may hold almost surely; empty families, zero mean and zero relative deviation
are valid. The upper event is closed, so threshold atoms are included.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Convexity bounds the exponential by the chord between the unit-interval endpoints. -/
theorem UnitIntervalExpChord (x t : ℝ) (InUnit : x ∈ Icc 0 1) :
    Real.exp (t*x) ≤ 1+x*(Real.exp t-1) := by
  have Chord := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ t)
    (sub_nonneg.mpr InUnit.2) InUnit.1 (show (1-x)+x=1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at Chord
  rw [mul_comm t x]
  linarith

/-- A bounded variable has the Bernoulli-style exponential MGF bound, for any real tilt. -/
theorem UnitIntervalMGFBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (MeasurableX : AEMeasurable X P) (Bounded : ∀ᵐ ω ∂P, X ω ∈ Icc 0 1) (t : ℝ) :
    mgf X P t ≤ Real.exp ((∫ ω, X ω ∂P)*(Real.exp t-1)) := by
  have IntegrableX := Integrable.of_mem_Icc 0 1 MeasurableX Bounded
  have IntegrableExp : Integrable (fun ω => Real.exp (t*X ω)) P :=
    integrable_exp_mul_of_mem_Icc MeasurableX Bounded
  have IntegrableLine : Integrable (fun ω => 1+X ω*(Real.exp t-1)) P :=
    (integrable_const 1).add (IntegrableX.mul_const _)
  have Chord : mgf X P t ≤ ∫ ω, 1+X ω*(Real.exp t-1) ∂P := by
    apply integral_mono_ae IntegrableExp IntegrableLine
    filter_upwards [Bounded] with ω InUnit
    exact UnitIntervalExpChord (X ω) t InUnit
  have LineIntegral : (∫ ω, 1+X ω*(Real.exp t-1) ∂P) =
      1+(∫ ω, X ω ∂P)*(Real.exp t-1) := by
    rw [integral_add (integrable_const _) (IntegrableX.mul_const _),
      integral_const, probReal_univ, one_smul, integral_mul_const]
  rw [LineIntegral] at Chord
  exact Chord.trans (by simpa only [add_comm] using Real.add_one_le_exp ((∫ ω, X ω ∂P)*(Real.exp t-1)))

/-- Mathlib factors the independent-sum MGF; the local interval estimate bounds each factor. -/
theorem UnitIndependentSumMGFBound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) (t : ℝ) :
    mgf (fun ω => ∑ i, X i ω) P t ≤
      Real.exp ((∫ ω, ∑ i, X i ω ∂P)*(Real.exp t-1)) := by
  have MeanSum : (∫ ω, ∑ i, X i ω ∂P) = ∑ i, ∫ ω, X i ω ∂P := by
    apply integral_finsetSum
    intro i _
    exact Integrable.of_mem_Icc 0 1 (MeasurableX i) (Bounded i)
  have Product := Independent.mgf_sum₀ MeasurableX Finset.univ (t := t)
  have SumFunction : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by
    funext ω
    exact Finset.sum_apply _ _ _
  rw [SumFunction] at Product
  rw [Product, MeanSum]
  calc
    _ ≤ ∏ i, Real.exp ((∫ ω, X i ω ∂P)*(Real.exp t-1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mgf_nonneg
      · intro i _
        exact UnitIntervalMGFBound P (X i) (MeasurableX i) (Bounded i) t
    _ = _ := by rw [← Real.exp_sum, Finset.sum_mul]

/-- Doerr equation (1.10.2), in logarithmic-exponential form, including zero mean and deviation. -/
theorem UnitIndependentSumChernoffUpper {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1+d)*(∫ w, ∑ i, X i w ∂P) ≤ ∑ i, X i ω} ≤
      Real.exp (-((1+d)*Real.log (1+d)-d)*(∫ w, ∑ i, X i w ∂P)) := by
  have PositiveBase : 0 < 1+d := by linarith
  have NonnegativeLog : 0 ≤ Real.log (1+d) := Real.log_nonneg (by linarith)
  have MeasurableSum : AEMeasurable (fun ω => ∑ i, X i ω) P := by
    have SumFunction : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by
      funext ω
      exact Finset.sum_apply _ _ _
    rw [← SumFunction]
    exact Finset.aemeasurable_sum _ (fun i _ => MeasurableX i)
  have SumBounded : ∀ᵐ ω ∂P, (∑ i, X i ω) ∈ Icc 0 (Fintype.card ι : ℝ) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    constructor
    · exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
    · calc
        _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have IntegrableExp : Integrable (fun ω => Real.exp (Real.log (1+d)*(∑ i, X i ω))) P :=
    integrable_exp_mul_of_mem_Icc MeasurableSum SumBounded
  have Bound := measure_ge_le_exp_mul_mgf ((1+d)*(∫ w, ∑ i, X i w ∂P)) NonnegativeLog IntegrableExp
  calc
    _ ≤ _ := Bound
    _ ≤ Real.exp (-Real.log (1+d)*((1+d)*(∫ w, ∑ i, X i w ∂P))) *
        Real.exp ((∫ w, ∑ i, X i w ∂P)*(Real.exp (Real.log (1+d))-1)) := by
      apply mul_le_mul_of_nonneg_left
        (UnitIndependentSumMGFBound P X MeasurableX Independent Bounded (Real.log (1+d)))
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, Real.exp_log PositiveBase]
      congr 1
      ring

/-- The positive-base real-power expression equals the logarithmic-exponential expression. -/
theorem ChernoffPowerExpression (d m : ℝ) (Nonnegative : 0 ≤ d) :
    (Real.exp d/(1+d)^(1+d))^m = Real.exp (-((1+d)*Real.log (1+d)-d)*m) := by
  have PositiveBase : 0 < 1+d := by linarith
  have PositiveDenominator : 0 < (1+d)^(1+d) := Real.rpow_pos_of_pos PositiveBase _
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos d) PositiveDenominator),
    Real.log_div (Real.exp_ne_zero d) PositiveDenominator.ne', Real.log_exp,
    Real.log_rpow PositiveBase]
  congr 1
  ring

/-- Doerr equation (1.10.2), in its real-power form. -/
theorem UnitIndependentSumChernoffUpperPower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1+d)*(∫ w, ∑ i, X i w ∂P) ≤ ∑ i, X i ω} ≤
      (Real.exp d/(1+d)^(1+d))^(∫ w, ∑ i, X i w ∂P) := by
  rw [ChernoffPowerExpression d _ Nonnegative]
  exact UnitIndependentSumChernoffUpper P X MeasurableX Independent Bounded d Nonnegative

end
end ECTheoryLib.Probability

/-!
## Large thresholds

Doerr Corollary 1.10.4 follows with the fixed tilt 1+log 2.
This proof never divides by the mean and includes zero mean, empty families
and the closed event at k=0. The threshold k may be any real number.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- A fixed positive tilt turns an exponential MGF estimate into the base-two upper tail. -/
theorem MGFBaseTwoUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (m k : ℝ)
    (MeanNonnegative : 0 ≤ m)
    (IntegrableExp : Integrable (fun ω => Real.exp ((1+Real.log 2)*X ω)) P)
    (MGFBound : mgf X P (1+Real.log 2) ≤ Real.exp (m*(Real.exp (1+Real.log 2)-1)))
    (LargeThreshold : 2*Real.exp 1*m ≤ k) :
    P.real {ω | k ≤ X ω} ≤ (2 : ℝ)^(-k) := by
  have LogNonnegative : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have TiltNonnegative : 0 ≤ 1+Real.log 2 := by linarith
  have ExpTilt : Real.exp (1+Real.log 2) = 2*Real.exp 1 := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm]
  have Bound := measure_ge_le_exp_mul_mgf k TiltNonnegative IntegrableExp
  calc
    _ ≤ _ := Bound
    _ ≤ Real.exp (-(1+Real.log 2)*k) *
        Real.exp (m*(Real.exp (1+Real.log 2)-1)) :=
      mul_le_mul_of_nonneg_left MGFBound (Real.exp_pos _).le
    _ = Real.exp (-(1+Real.log 2)*k+m*(2*Real.exp 1-1)) := by
      rw [← Real.exp_add, ExpTilt]
    _ ≤ Real.exp (Real.log 2*(-k)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = _ := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-k)).symm

/-- Doerr Corollary 1.10.4: Pr[sum >= k] <= 2^(-k) for k >= 2*e*E[sum]. -/
theorem UnitIndependentSumBaseTwoUpperTail {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (k : ℝ) (LargeThreshold : 2*Real.exp 1*(∫ ω, ∑ i, X i ω ∂P) ≤ k) :
    P.real {ω | k ≤ ∑ i, X i ω} ≤ (2 : ℝ)^(-k) := by
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  have SumFunction : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by
    funext ω
    exact Finset.sum_apply _ _ _
  have MeasurableSum : AEMeasurable (fun ω => ∑ i, X i ω) P := by
    rw [← SumFunction]
    exact Finset.aemeasurable_sum _ (fun i _ => MeasurableX i)
  have SumBounded : ∀ᵐ ω ∂P, (∑ i, X i ω) ∈ Icc 0 (Fintype.card ι : ℝ) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    constructor
    · exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
    · calc
        _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Bounds i).2)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact MGFBaseTwoUpperTail P _ _ k MeanNonnegative
    (integrable_exp_mul_of_mem_Icc MeasurableSum SumBounded)
    (UnitIndependentSumMGFBound P X MeasurableX Independent Bounded _) LargeThreshold

end
end ECTheoryLib.Probability

/-!
## Quadratic and minimum-form upper tails

The following results complete equations (1.10.3)-(1.10.5). The strongest
finite-size formula (1.10.1) remains a separate obligation. All expectations
are nonnegative by the actual variable bounds, including the zero case.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Doerr equation (1.10.3), with the exact denominator 2+2*d/3. -/
theorem UnitIndependentSumChernoffUpperQuadratic {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1+d)*(∫ w, ∑ i, X i w ∂P) ≤ ∑ i, X i ω} ≤
      Real.exp (-(d^2*(∫ w, ∑ i, X i w ∂P))/(2+2*d/3)) := by
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  apply (UnitIndependentSumChernoffUpper P X MeasurableX Independent Bounded d Nonnegative).trans
  apply Real.exp_le_exp.mpr
  have ExponentBound := mul_le_mul_of_nonneg_right
    (ChernoffExponentQuadraticLower d Nonnegative) MeanNonnegative
  rw [div_mul_eq_mul_div] at ExponentBound
  simpa only [neg_mul, neg_div] using neg_le_neg ExponentBound

/-- Doerr equation (1.10.4), with quadratic small deviations and linear large deviations. -/
theorem UnitIndependentSumChernoffUpperMin {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (1+d)*(∫ w, ∑ i, X i w ∂P) ≤ ∑ i, X i ω} ≤
      Real.exp (-(min (d^2) d)*(∫ w, ∑ i, X i w ∂P)/3) := by
  have MeanNonnegative : 0 ≤ ∫ ω, ∑ i, X i ω ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  apply (UnitIndependentSumChernoffUpperQuadratic P X MeasurableX Independent Bounded d Nonnegative).trans
  apply Real.exp_le_exp.mpr
  have ExponentBound := mul_le_mul_of_nonneg_right
    (ChernoffQuadraticMinLower d Nonnegative) MeanNonnegative
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div] at ExponentBound
  simpa only [neg_mul, neg_div] using neg_le_neg ExponentBound

/-- Doerr equation (1.10.5), including both endpoints of the relative-deviation interval. -/
theorem UnitIndependentSumChernoffUpperSmall {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (d : ℝ) (DeviationInUnit : d ∈ Icc 0 1) :
    P.real {ω | (1+d)*(∫ w, ∑ i, X i w ∂P) ≤ ∑ i, X i ω} ≤
      Real.exp (-(d^2)*(∫ w, ∑ i, X i w ∂P)/3) := by
  have SquareLe : d^2 ≤ d := by nlinarith [DeviationInUnit.1, DeviationInUnit.2]
  have Bound := UnitIndependentSumChernoffUpperMin P X MeasurableX Independent Bounded d DeviationInUnit.1
  rw [min_eq_left SquareLe] at Bound
  exact Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section

/-- A single optimized MGF certificate suffices for the multiplicative upper
tail. The certificate may come from independence or negative correlation. -/
theorem MGFMultiplicativeUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (m d : ℝ) (Nonnegative : 0≤d)
    (IntegrableExp : Integrable (fun ω => Real.exp (Real.log (1+d)*X ω)) P)
    (Certificate : mgf X P (Real.log (1+d))≤Real.exp (m*d)) :
    P.real {ω | (1+d)*m≤X ω}≤Real.exp (-((1+d)*Real.log (1+d)-d)*m) := by
  have NonnegativeLog : 0≤Real.log (1+d) := Real.log_nonneg (by linarith)
  have Bound := measure_ge_le_exp_mul_mgf ((1+d)*m) NonnegativeLog IntegrableExp
  apply Bound.trans
  calc
    _≤Real.exp (-Real.log (1+d)*((1+d)*m))*Real.exp (m*d) :=
      mul_le_mul_of_nonneg_left Certificate (Real.exp_pos _).le
    _=_ := by
      rw [← Real.exp_add]
      congr 1
      ring

end
end ECTheoryLib.Probability
