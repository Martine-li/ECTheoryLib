import ECTheoryLib.Probability.Concentration.VarianceFiniteChernoff

/-!
# Variance concentration at an arbitrary centered scale

Doerr1.10.14: divide actual variables by a positive scale, using Mathlib
variance scaling and the unit-scale finite bound. Literal source formulas,
endpoint/cutoff and Bennett/Bernstein/min comparisons are proved. The
source leaves positivity implicit despite dividing by b; APIs require b>0.
Separate zero-scale theorems prove the deterministic boundary without
independence or second-moment assumptions.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Positive-scale version of the finite-size bound. Theorems require b>0. -/
def ScaledVarianceFiniteUpperBound (n : ℕ) (b v d : ℝ) : ℝ :=
  VarianceFiniteUpperBound n (v/b^2) (d/b)

def ScaledBennettUpperBound (b v d : ℝ) : ℝ := BennettUpperBound (v/b^2) (d/b)

/-- Source1.10.14: the scale changes actual variance quadratically. -/
theorem IndependentSumFiniteVarianceUpperScaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0<b)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+b)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      ScaledVarianceFiniteUpperBound n b (∑ i, variance (X i) P) d := by
  have Mem (i : Fin n) : MemLp (fun ω => X i ω/b) 2 P := by
    simpa only [div_eq_mul_inv] using (SquareIntegrable i).mul_const b⁻¹
  have IndependentScaled : iIndepFun (fun i ω => X i ω/b) P :=
    Independent.comp (fun _ x => x/b) (fun _ => by fun_prop)
  have UpperScaled (i : Fin n) : ∀ᵐ ω ∂P, X i ω/b≤(∫ w, X i w/b ∂P)+1 := by
    rw [integral_div]
    filter_upwards [Upper i] with ω Bound
    rw [div_le_iff₀ PositiveScale]
    field_simp
    linarith
  have Bound := IndependentSumFiniteVarianceUpper P (fun i ω => X i ω/b)
    Mem IndependentScaled UpperScaled (d/b) (div_nonneg NonnegativeDeviation PositiveScale.le)
  have Variance (i : Fin n) : variance (fun ω => X i ω/b) P=variance (X i) P/b^2 := by
    simp only [div_eq_mul_inv,variance_mul_const,inv_pow]
  have Event : {ω | (∫ w, ∑ i, X i w/b ∂P)+d/b≤∑ i, X i ω/b}=
      {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω} := by
    simp only [← Finset.sum_div,integral_div,← add_div,div_le_div_iff_of_pos_right PositiveScale]
  rw [Event] at Bound
  simp only [Variance,← Finset.sum_div] at Bound
  exact Bound

theorem IndependentSumFiniteVarianceLowerScaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0<b)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-b≤X i ω)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d}≤
      ScaledVarianceFiniteUpperBound n b (∑ i, variance (X i) P) d := by
  have IndependentNeg : iIndepFun (fun i ω => -X i ω) P :=
    Independent.comp (fun _ x => -x) (fun _ => measurable_neg)
  have UpperNeg (i : Fin n) : ∀ᵐ ω ∂P, -X i ω≤(∫ w, -X i w ∂P)+b := by
    rw [integral_neg]
    filter_upwards [Lower i] with ω Bound
    linarith
  have Bound := IndependentSumFiniteVarianceUpperScaled P (fun i ω => -X i ω)
    (fun i => (SquareIntegrable i).neg) IndependentNeg b PositiveScale UpperNeg d NonnegativeDeviation
  have Event : {ω | (∫ w, ∑ i, -X i w ∂P)+d≤∑ i, -X i ω}=
      {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d} := by
    simp only [Finset.sum_neg_distrib,integral_neg]
    ext ω
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [Event] at Bound
  simpa only [variance_fun_neg] using Bound

theorem ScaledVarianceFiniteUpperBoundLeBennett (n : ℕ) (b v d : ℝ)
    (PositiveScale : 0<b) (NonnegativeVariance : 0≤v) (NonnegativeDeviation : 0≤d) :
    ScaledVarianceFiniteUpperBound n b v d≤ScaledBennettUpperBound b v d :=
  VarianceFiniteUpperBoundLeBennett n _ _ (div_nonneg NonnegativeVariance (sq_nonneg b))
    (div_nonneg NonnegativeDeviation PositiveScale.le)

theorem ScaledBennettUpperBoundLeBernstein (b v d : ℝ) (PositiveScale : 0<b)
    (NonnegativeVariance : 0≤v) (NonnegativeDeviation : 0≤d) :
    ScaledBennettUpperBound b v d≤Real.exp (-d^2/(2*v+2*b*d/3)) := by
  have Bound := BennettUpperBoundLeBernstein (v/b^2) (d/b)
    (div_nonneg NonnegativeVariance (sq_nonneg b)) (div_nonneg NonnegativeDeviation PositiveScale.le)
  have Identity : -(d/b)^2/(2*(v/b^2)+2*(d/b)/3)= -d^2/(2*v+2*b*d/3) := by
    field_simp
  rwa [Identity] at Bound

theorem ScaledBernsteinExponentMinLower (b v d : ℝ) (PositiveScale : 0<b)
    (NonnegativeVariance : 0≤v) (NonnegativeDeviation : 0≤d) :
    min (d^2/v) (d/b)/3≤d^2/(2*v+2*b*d/3) := by
  have Bound := BernsteinExponentMinLower (v/b^2) (d/b)
    (div_nonneg NonnegativeVariance (sq_nonneg b)) (div_nonneg NonnegativeDeviation PositiveScale.le)
  have Left : (d/b)^2/(v/b^2)=d^2/v := by field_simp
  have Right : (d/b)^2/(2*(v/b^2)+2*(d/b)/3)=d^2/(2*v+2*b*d/3) := by field_simp
  rwa [Left,Right] at Bound

theorem IndependentSumBernsteinUpperScaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0<b)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+b)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      Real.exp (-d^2/(2*(∑ i, variance (X i) P)+2*b*d/3)) :=
  ((IndependentSumFiniteVarianceUpperScaled P X SquareIntegrable Independent b PositiveScale Upper d
    NonnegativeDeviation).trans
      (ScaledVarianceFiniteUpperBoundLeBennett n b _ d PositiveScale
        (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) NonnegativeDeviation)).trans
    (ScaledBennettUpperBoundLeBernstein b _ d PositiveScale
      (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) NonnegativeDeviation)

theorem IndependentSumBernsteinLowerScaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0<b)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-b≤X i ω)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d}≤
      Real.exp (-d^2/(2*(∑ i, variance (X i) P)+2*b*d/3)) :=
  ((IndependentSumFiniteVarianceLowerScaled P X SquareIntegrable Independent b PositiveScale Lower d
    NonnegativeDeviation).trans
      (ScaledVarianceFiniteUpperBoundLeBennett n b _ d PositiveScale
        (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) NonnegativeDeviation)).trans
    (ScaledBennettUpperBoundLeBernstein b _ d PositiveScale
      (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) NonnegativeDeviation)

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Literal formula1.10.31 on the nonsingular interior. -/
theorem ScaledVarianceFiniteUpperBoundBookInterior {n : ℕ} (b v d : ℝ)
    (PositiveScale : 0<b) (PositiveVariance : 0<v)
    (NonnegativeDeviation : 0≤d) (BelowMaximum : d<(n : ℝ)*b) :
    ScaledVarianceFiniteUpperBound n b v d=
      ((1+b*d/v)^(-((1+b*d/v)*v/((n : ℝ)*b^2+v)))*
        (1-d/((n : ℝ)*b))^(-((1-d/((n : ℝ)*b))*(n : ℝ)*b^2/((n : ℝ)*b^2+v))))^n := by
  have Bound := VarianceFiniteUpperBoundBookInterior (n := n) (v/b^2) (d/b)
    (div_pos PositiveVariance (sq_pos_of_pos PositiveScale))
    (div_nonneg NonnegativeDeviation PositiveScale.le) ((div_lt_iff₀ PositiveScale).mpr BelowMaximum)
  have Ratio : (d/b)/(v/b^2)=b*d/v := by field_simp
  have Complement : (d/b)/(n : ℝ)=d/((n : ℝ)*b) := by ring
  have Left : (1+b*d/v)*(v/b^2)/((n : ℝ)+v/b^2)=
      (1+b*d/v)*v/((n : ℝ)*b^2+v) := by field_simp
  have Right : (1-d/((n : ℝ)*b))*(n : ℝ)/((n : ℝ)+v/b^2)=
      (1-d/((n : ℝ)*b))*(n : ℝ)*b^2/((n : ℝ)*b^2+v) := by field_simp
  simpa only [ScaledVarianceFiniteUpperBound,Ratio,Complement,Left,Right] using Bound

theorem ScaledVarianceFiniteUpperBoundEndpoint {n : ℕ} (PositiveLength : 0<n)
    (b v : ℝ) (PositiveScale : 0<b) (PositiveVariance : 0<v) :
    ScaledVarianceFiniteUpperBound n b v ((n : ℝ)*b)=(v/((n : ℝ)*b^2+v))^n := by
  unfold ScaledVarianceFiniteUpperBound
  rw [mul_div_cancel_right₀ _ PositiveScale.ne',
    VarianceFiniteUpperBoundEndpoint PositiveLength _ (div_pos PositiveVariance (sq_pos_of_pos PositiveScale))]
  congr 1
  field_simp

theorem ScaledVarianceFiniteUpperBoundBeyond {n : ℕ} (b v d : ℝ)
    (PositiveScale : 0<b) (BeyondMaximum : (n : ℝ)*b<d) :
    ScaledVarianceFiniteUpperBound n b v d=0 :=
  VarianceFiniteUpperBoundBeyond _ _ ((lt_div_iff₀ PositiveScale).mpr BeyondMaximum)

/-- Literal formula1.10.32, with positive variance and deviation. -/
theorem ScaledBennettUpperBoundBook (b v d : ℝ) (PositiveScale : 0<b)
    (PositiveVariance : 0<v) (PositiveDeviation : 0<d) :
    ScaledBennettUpperBound b v d=
      Real.exp (-(d/b)*((1+v/(b*d))*Real.log (1+b*d/v)-1)) := by
  have V : v/b^2≠0 := ne_of_gt (div_pos PositiveVariance (sq_pos_of_pos PositiveScale))
  have D : d/b≠0 := ne_of_gt (div_pos PositiveDeviation PositiveScale)
  simp only [ScaledBennettUpperBound,BennettUpperBound,V,D,ite_false]
  have Ratio : (d/b)/(v/b^2)=b*d/v := by field_simp
  rw [Ratio]
  congr 1
  field_simp
  ring

/-- Formula1.10.33 equals the denominator used by the total Bernstein API. -/
theorem ScaledBernsteinBookDenominator (b v d : ℝ) (NonzeroVariance : v≠0) :
    v*(2+2/3*(b*d/v))=2*v+2*b*d/3 := by field_simp

/-- At b=0, the centered upper premise forces the actual sum to be
constant almost surely. This boundary needs no independence and no variance. -/
theorem SumZeroCenteredUpperScaleDeviation {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (IntegrableX : ∀ i, Integrable (X i) P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤∫ w, X i w ∂P)
    (d : ℝ) (PositiveDeviation : 0<d) :
    P {ω | d≤|(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)|}=0 := by
  have Constant (i : ι) : X i =ᵐ[P] fun _ => ∫ w, X i w ∂P :=
    (integral_eq_iff_of_ae_le (IntegrableX i) (integrable_const _) (Upper i)).mp
      (by simp only [integral_const,probReal_univ,one_smul])
  have MeanSum := integral_finsetSum Finset.univ (fun i _ => IntegrableX i)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_all_iff.mpr Constant] with ω Equal
  simp only [Equal,MeanSum,sub_self,abs_zero,not_le]
  exact PositiveDeviation

/-- The zero lower scale has the same deterministic extension. -/
theorem SumZeroCenteredLowerScaleDeviation {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (IntegrableX : ∀ i, Integrable (X i) P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)≤X i ω)
    (d : ℝ) (PositiveDeviation : 0<d) :
    P {ω | d≤|(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)|}=0 := by
  have UpperNeg (i : ι) : ∀ᵐ ω ∂P, -X i ω≤∫ w, -X i w ∂P := by
    rw [integral_neg]
    exact (Lower i).mono (fun _ Bound => neg_le_neg Bound)
  have Bound := SumZeroCenteredUpperScaleDeviation P (fun i ω => -X i ω)
    (fun i => (IntegrableX i).neg) UpperNeg d PositiveDeviation
  simpa only [Finset.sum_neg_distrib,integral_neg,neg_sub_neg,abs_sub_comm] using Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Formula 1.10.34 as an upper-tail API. At zero variance the displayed
real-valued minimum bound is 1; the finite-size/Bennett APIs give the sharper 0
bound for positive deviation. -/
theorem IndependentSumBernsteinMinUpperScaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + b)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P) + d ≤ ∑ i, X i ω} ≤
      Real.exp (-min (d ^ 2 / (∑ i, variance (X i) P)) (d / b) / 3) := by
  apply (IndependentSumBernsteinUpperScaled P X SquareIntegrable Independent b
    PositiveScale Upper d NonnegativeDeviation).trans
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg
    (ScaledBernsteinExponentMinLower b _ d PositiveScale
      (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) NonnegativeDeviation)

/-- Formula 1.10.34 for the lower tail, under the lower centered bound. -/
theorem IndependentSumBernsteinMinLowerScaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P) - b ≤ X i ω)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P) - d} ≤
      Real.exp (-min (d ^ 2 / (∑ i, variance (X i) P)) (d / b) / 3) := by
  apply (IndependentSumBernsteinLowerScaled P X SquareIntegrable Independent b
    PositiveScale Lower d NonnegativeDeviation).trans
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg
    (ScaledBernsteinExponentMinLower b _ d PositiveScale
      (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) NonnegativeDeviation)

end
end ECTheoryLib.Probability


/-! Estimated sum thresholds retain the positive scale, actual centers and variances. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Only the sum threshold is estimated; the positive scale, actual centers and variance stay fixed. -/
theorem IndependentSumFiniteVarianceUpperScaledOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + b)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ U)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | U + d ≤ ∑ i, X i ω} ≤
      ScaledVarianceFiniteUpperBound n b (∑ i, variance (X i) P) d := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumFiniteVarianceUpperScaled P X SquareIntegrable Independent b PositiveScale
      Upper d NonnegativeDeviation)
  intro ω Bound
  exact le_trans (add_le_add MeanUpper (le_refl d)) Bound

/-- Only the sum threshold is estimated; the positive scale, actual centers and variance stay fixed. -/
theorem IndependentSumFiniteVarianceLowerScaledOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P) - b ≤ X i ω)
    (L : ℝ) (MeanLower : L ≤ (∫ w, ∑ i, X i w ∂P))
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ L - d} ≤
      ScaledVarianceFiniteUpperBound n b (∑ i, variance (X i) P) d := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumFiniteVarianceLowerScaled P X SquareIntegrable Independent b PositiveScale
      Lower d NonnegativeDeviation)
  intro ω Bound
  exact le_trans Bound (sub_le_sub_right MeanLower d)

/-- Only the sum threshold is estimated; the positive scale, actual centers and variance stay fixed. -/
theorem IndependentSumBennettUpperScaledOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + b)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ U)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | U + d ≤ ∑ i, X i ω} ≤
      ScaledBennettUpperBound b (∑ i, variance (X i) P) d := by
  exact (IndependentSumFiniteVarianceUpperScaledOfMeanLe P X SquareIntegrable Independent
    b PositiveScale Upper U MeanUpper d NonnegativeDeviation).trans
      (ScaledVarianceFiniteUpperBoundLeBennett n b _ d PositiveScale
        (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) NonnegativeDeviation)

/-- Only the sum threshold is estimated; the positive scale, actual centers and variance stay fixed. -/
theorem IndependentSumBennettLowerScaledOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P) - b ≤ X i ω)
    (L : ℝ) (MeanLower : L ≤ (∫ w, ∑ i, X i w ∂P))
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ L - d} ≤
      ScaledBennettUpperBound b (∑ i, variance (X i) P) d := by
  exact (IndependentSumFiniteVarianceLowerScaledOfLeMean P X SquareIntegrable Independent
    b PositiveScale Lower L MeanLower d NonnegativeDeviation).trans
      (ScaledVarianceFiniteUpperBoundLeBennett n b _ d PositiveScale
        (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) NonnegativeDeviation)

/-- Only the sum threshold is estimated; the positive scale, actual centers and variance stay fixed. -/
theorem IndependentSumBernsteinUpperScaledOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + b)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ U)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | U + d ≤ ∑ i, X i ω} ≤
      Real.exp (-d ^ 2 / (2 * (∑ i, variance (X i) P) + 2 * b * d / 3)) := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBernsteinUpperScaled P X SquareIntegrable Independent b PositiveScale
      Upper d NonnegativeDeviation)
  intro ω Bound
  exact le_trans (add_le_add MeanUpper (le_refl d)) Bound

/-- Only the sum threshold is estimated; the positive scale, actual centers and variance stay fixed. -/
theorem IndependentSumBernsteinLowerScaledOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P) - b ≤ X i ω)
    (L : ℝ) (MeanLower : L ≤ (∫ w, ∑ i, X i w ∂P))
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ L - d} ≤
      Real.exp (-d ^ 2 / (2 * (∑ i, variance (X i) P) + 2 * b * d / 3)) := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBernsteinLowerScaled P X SquareIntegrable Independent b PositiveScale
      Lower d NonnegativeDeviation)
  intro ω Bound
  exact le_trans Bound (sub_le_sub_right MeanLower d)

/-- Only the sum threshold is estimated; the positive scale, actual centers and variance stay fixed. -/
theorem IndependentSumBernsteinMinUpperScaledOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + b)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ U)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | U + d ≤ ∑ i, X i ω} ≤
      Real.exp (-min (d ^ 2 / (∑ i, variance (X i) P)) (d / b) / 3) := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBernsteinMinUpperScaled P X SquareIntegrable Independent b PositiveScale
      Upper d NonnegativeDeviation)
  intro ω Bound
  exact le_trans (add_le_add MeanUpper (le_refl d)) Bound

/-- Only the sum threshold is estimated; the positive scale, actual centers and variance stay fixed. -/
theorem IndependentSumBernsteinMinLowerScaledOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P) (b : ℝ) (PositiveScale : 0 < b)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P) - b ≤ X i ω)
    (L : ℝ) (MeanLower : L ≤ (∫ w, ∑ i, X i w ∂P))
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ L - d} ≤
      Real.exp (-min (d ^ 2 / (∑ i, variance (X i) P)) (d / b) / 3) := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBernsteinMinLowerScaled P X SquareIntegrable Independent b PositiveScale
      Lower d NonnegativeDeviation)
  intro ω Bound
  exact le_trans Bound (sub_le_sub_right MeanLower d)

end
end ECTheoryLib.Probability

