import ECTheoryLib.Probability.Moments.BennettExponential
import ECTheoryLib.Probability.Concentration.ChernoffExponent
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Variance-sensitive Bennett and Bernstein tails

Doerr1.10.12/13, formulas1.10.26--28: independent square-integrable variables
with a one-sided centered bound of1, arbitrary opposite tails and offsets.
MGF bounds use actual marginal variances, actual sum means, and Mathlib
independence. BennettUpperBound explicitly handles zero deviation and zero
variance. The strongest finite-size formula1.10.25 is outside this module.
Finite second moments make the source variance convention explicit.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- A one-sided upper bound is enough for positive exponential integrability. -/
theorem UpperBoundedExponentialIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Z : Ω → ℝ) (c t : ℝ)
    (MeasurableZ : AEMeasurable Z P) (Upper : ∀ᵐ ω ∂P, Z ω≤c)
    (Nonnegative : 0≤t) : Integrable (fun ω => Real.exp (t*Z ω)) P := by
  apply (integrable_const (Real.exp (t*c))).mono'
    ((MeasurableZ.const_mul t).exp.aestronglyMeasurable)
  filter_upwards [Upper] with ω Bound
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left Bound Nonnegative)

/-- Keep both first and second moments before exponential relaxation. -/
theorem UpperBoundedQuadraticMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (SquareIntegrable : MemLp Y 2 P) (Upper : ∀ᵐ ω ∂P, Y ω≤1)
    (t : ℝ) (Nonnegative : 0≤t) :
    mgf Y P t≤1+t*(∫ ω, Y ω ∂P)+(∫ ω, (Y ω)^2 ∂P)*(Real.exp t-1-t) := by
  have IntY := SquareIntegrable.integrable (by norm_num : (1 : ENNReal)≤2)
  have IntExp := UpperBoundedExponentialIntegrable P Y 1 t SquareIntegrable.aemeasurable Upper Nonnegative
  have Bound : (∫ ω, Real.exp (t*Y ω) ∂P)≤∫ ω, 1+t*Y ω+(Y ω)^2*(Real.exp t-1-t) ∂P := by
    apply integral_mono_ae IntExp (((integrable_const 1).add (IntY.const_mul t)).add
      (SquareIntegrable.integrable_sq.mul_const _))
    filter_upwards [Upper] with ω hω
    exact BennettExponentialMajorant t (Y ω) Nonnegative hω
  rw [integral_add (f := fun ω => 1+t*Y ω) ((integrable_const 1).add (IntY.const_mul t))
      (SquareIntegrable.integrable_sq.mul_const _),
    integral_add (integrable_const 1) (IntY.const_mul t),
    integral_const_mul,integral_mul_const,integral_const,probReal_univ,one_smul] at Bound
  exact Bound

/-- Bennett's centered one-variable MGF bound, with actual second moment. -/
theorem CenteredBennettMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ)
    (SquareIntegrable : MemLp Z 2 P) (Centered : (∫ ω, Z ω ∂P)=0)
    (Upper : ∀ᵐ ω ∂P, Z ω≤1) (t : ℝ) (Nonnegative : 0≤t) :
    mgf Z P t≤Real.exp (variance Z P*(Real.exp t-1-t)) := by
  have Bound := UpperBoundedQuadraticMGF P Z SquareIntegrable Upper t Nonnegative
  rw [Centered, mul_zero, add_zero,
    ← variance_of_integral_eq_zero SquareIntegrable.aemeasurable Centered] at Bound
  exact Bound.trans (by simpa only [add_comm] using
    (Real.add_one_le_exp (variance Z P*(Real.exp t-1-t))))

/-- The actual centered variable, with variance preserved by translation. -/
theorem BennettCenteredVariableMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P)
    (Upper : ∀ᵐ ω ∂P, X ω≤(∫ w, X w ∂P)+1)
    (t : ℝ) (Nonnegative : 0≤t) :
    mgf (fun ω => X ω-(∫ w, X w ∂P)) P t≤
      Real.exp (variance X P*(Real.exp t-1-t)) := by
  have Centered : (∫ ω, X ω-(∫ w, X w ∂P) ∂P)=0 := by
    rw [integral_sub (SquareIntegrable.integrable (by norm_num)) (integrable_const _)]
    simp
  have Bound := CenteredBennettMGF P (fun ω => X ω-(∫ w, X w ∂P))
    (SquareIntegrable.sub (memLp_const _)) Centered
    (by filter_upwards [Upper] with ω hω; linarith) t Nonnegative
  simpa only [variance_sub_const SquareIntegrable.aestronglyMeasurable] using Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The sum MGF uses actual expectations and marginal variances. -/
theorem IndependentSumBennettMGF {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (t : ℝ) (Nonnegative : 0≤t) :
    mgf (fun ω => (∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)) P t≤
      Real.exp ((∑ i, variance (X i) P)*(Real.exp t-1-t)) := by
  classical
  let Z := fun i ω => X i ω-∫ w, X i w ∂P
  have IndependentZ : iIndepFun Z P := Independent.comp
    (fun i x => x-∫ w, X i w ∂P) (fun _ => measurable_id.sub_const _)
  have MeanSum : (∫ w, ∑ i, X i w ∂P)=∑ i, ∫ w, X i w ∂P :=
    integral_finsetSum _ (fun i _ => (SquareIntegrable i).integrable (by norm_num))
  have SumIdentity : (fun ω => (∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P))=∑ i, Z i := by
    funext ω
    simp only [Finset.sum_apply,Z,Finset.sum_sub_distrib,MeanSum]
  rw [SumIdentity,IndependentZ.mgf_sum₀
    (fun i => (SquareIntegrable i).aemeasurable.sub_const _) Finset.univ]
  calc
    _≤∏ i, Real.exp (variance (X i) P*(Real.exp t-1-t)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun _ => (Real.exp_pos _).le)
      · intro i _
        exact BennettCenteredVariableMGF P (X i) (SquareIntegrable i) (Upper i) t Nonnegative
    _=_ := by rw [← Real.exp_sum,Finset.sum_mul]

/-- Translate a Bennett MGF certificate into its optimized logarithmic tail.
Positive variance is required here; deterministic variables are handled separately. -/
theorem BennettUpperTailOfMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ)
    (v d : ℝ) (PositiveVariance : 0<v) (NonnegativeDeviation : 0≤d)
    (IntegrableExp : Integrable (fun ω => Real.exp (Real.log (1+d/v)*Z ω)) P)
    (Certificate : mgf Z P (Real.log (1+d/v))≤Real.exp (v*(d/v-Real.log (1+d/v)))) :
    P.real {ω | d≤Z ω}≤Real.exp (-v*((1+d/v)*Real.log (1+d/v)-d/v)) := by
  have NonnegativeRatio : 0≤d/v := div_nonneg NonnegativeDeviation PositiveVariance.le
  have Bound := measure_ge_le_exp_mul_mgf d
    (Real.log_nonneg (by linarith : (1 : ℝ)≤1+d/v)) IntegrableExp
  apply Bound.trans
  calc
    _≤Real.exp (-Real.log (1+d/v)*d)*Real.exp (v*(d/v-Real.log (1+d/v))) :=
      mul_le_mul_of_nonneg_left Certificate (Real.exp_pos _).le
    _=_ := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring

/-- One-sided centered upper bounds give the Bennett inequality for an
independent family, without a lower bound on any variable. -/
theorem IndependentSumBennettUpper {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (d : ℝ) (NonnegativeDeviation : 0≤d)
    (PositiveVariance : 0<∑ i, variance (X i) P) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      Real.exp (-(∑ i, variance (X i) P)*
        ((1+d/(∑ i, variance (X i) P))*Real.log (1+d/(∑ i, variance (X i) P))-
          d/(∑ i, variance (X i) P))) := by
  classical
  let v := ∑ i, variance (X i) P
  let Z := fun ω => (∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)
  have MeanSum : (∫ w, ∑ i, X i w ∂P)=∑ i, ∫ w, X i w ∂P :=
    integral_finsetSum _ (fun i _ => (SquareIntegrable i).integrable (by norm_num))
  have UpperZ : ∀ᵐ ω ∂P, Z ω≤(Fintype.card ι : ℝ) := by
    filter_upwards [ae_all_iff.mpr Upper] with ω Bounds
    have Each := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Bounds i)
    simpa only [Z,MeanSum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,sub_le_iff_le_add,add_comm] using Each
  have MeasurableZ : AEMeasurable Z P := by
    simpa only [Z,Finset.sum_apply] using
      (Finset.aemeasurable_sum Finset.univ (fun i _ => (SquareIntegrable i).aemeasurable)).sub_const
        (∫ w, ∑ i, X i w ∂P)
  have TiltNonnegative : 0≤Real.log (1+d/v) :=
    Real.log_nonneg (by have := div_nonneg NonnegativeDeviation PositiveVariance.le; linarith)
  have IntExp := UpperBoundedExponentialIntegrable P Z (Fintype.card ι) _
    MeasurableZ UpperZ TiltNonnegative
  have Certificate := IndependentSumBennettMGF P X SquareIntegrable Independent Upper
    (Real.log (1+d/v)) TiltNonnegative
  rw [Real.exp_log (by have := div_nonneg NonnegativeDeviation PositiveVariance.le; linarith),
    add_sub_cancel_left] at Certificate
  have Bound := BennettUpperTailOfMGF P Z v d PositiveVariance NonnegativeDeviation IntExp Certificate
  have Event : {ω | d≤Z ω}={ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω} := by
    ext ω
    simp only [mem_ofPred_eq,Z]
    constructor <;> intro h <;> linarith
  rw [Event] at Bound
  exact Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Vanishing marginal variance makes the sum constant almost surely.
This boundary does not require independence. -/
theorem ZeroVarianceSumDeviationProbability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (ZeroVariance : (∑ i, variance (X i) P)=0) (d : ℝ) (Positive : 0<d) :
    P {ω | d≤|(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)|}=0 := by
  have EachZero (i : ι) : variance (X i) P=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => variance_nonneg (X j) P)).mp
      ZeroVariance i (Finset.mem_univ i)
  have EachConstant (i : ι) := ae_eq_integral_of_variance_eq_zero (SquareIntegrable i) (EachZero i)
  have MeanSum : (∫ w, ∑ i, X i w ∂P)=∑ i, ∫ w, X i w ∂P :=
    integral_finsetSum _ (fun i _ => (SquareIntegrable i).integrable (by norm_num))
  have Excluded : ∀ᵐ ω ∂P, ¬d≤|(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)| := by
    filter_upwards [ae_all_iff.mpr EachConstant] with ω Equal
    simp only [Equal,MeanSum,sub_self,abs_zero,not_le]
    exact Positive
  simpa only [not_not] using ae_iff.mp Excluded

/-- Continuous deterministic extension of Bennett's positive-variance bound. -/
def BennettUpperBound (v d : ℝ) : ℝ :=
  if d=0 then 1 else if v=0 then 0 else Real.exp (-v*((1+d/v)*Real.log (1+d/v)-d/v))

/-- The Bennett upper tail with explicit zero variance and zero deviation. -/
theorem IndependentSumBennettUpperAll {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      BennettUpperBound (∑ i, variance (X i) P) d := by
  by_cases ZeroDeviation : d=0
  · simp only [BennettUpperBound,ZeroDeviation,ite_true]
    exact measureReal_le_one
  by_cases ZeroVariance : (∑ i, variance (X i) P)=0
  · simp only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false,ite_true]
    have Zero := ZeroVarianceSumDeviationProbability P X SquareIntegrable ZeroVariance d
      (lt_of_le_of_ne NonnegativeDeviation (Ne.symm ZeroDeviation))
    have Subset : {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}⊆
        {ω | d≤|(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)|} := by
      intro ω hω
      change (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω at hω
      exact (by linarith : d≤(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)).trans (le_abs_self _)
    have EventZero := measure_mono_null Subset Zero
    simp only [Measure.real,EventZero,ENNReal.toReal_zero,le_refl]
  · simp only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false]
    exact IndependentSumBennettUpper P X SquareIntegrable Independent Upper d NonnegativeDeviation
      (lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) (Ne.symm ZeroVariance))

/-- Scalar simplification of Bennett's bound to Bernstein, including v=0. -/
theorem BennettUpperBoundLeBernstein (v d : ℝ) (NonnegativeVariance : 0≤v)
    (NonnegativeDeviation : 0≤d) :
    BennettUpperBound v d≤Real.exp (-d^2/(2*v+2*d/3)) := by
  by_cases ZeroDeviation : d=0
  · simp [BennettUpperBound,ZeroDeviation]
  by_cases ZeroVariance : v=0
  · simp only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false,ite_true]
    exact (Real.exp_pos _).le
  have PositiveVariance : 0<v := lt_of_le_of_ne NonnegativeVariance (Ne.symm ZeroVariance)
  simp only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false]
  apply Real.exp_le_exp.mpr
  have Scaled := mul_le_mul_of_nonneg_left
    (ChernoffExponentQuadraticLower (d/v) (div_nonneg NonnegativeDeviation NonnegativeVariance))
      NonnegativeVariance
  have Identity : v*((d/v)^2/(2+2*(d/v)/3))=d^2/(2*v+2*d/3) := by
    field_simp
  rw [Identity] at Scaled
  simpa only [neg_mul,neg_div] using neg_le_neg Scaled

/-- Bernstein's inequality under the one-sided bounded-increment premise. -/
theorem IndependentSumBernsteinUpper {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      Real.exp (-d^2/(2*(∑ i, variance (X i) P)+2*d/3)) :=
  (IndependentSumBennettUpperAll P X SquareIntegrable Independent Upper d NonnegativeDeviation).trans
    (BennettUpperBoundLeBernstein _ d (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P))
      NonnegativeDeviation)

/-- Bernstein's exponent also gives the usual minimum-of-linear-and-quadratic form. -/
theorem BernsteinExponentMinLower (v d : ℝ) (NonnegativeVariance : 0≤v)
    (NonnegativeDeviation : 0≤d) :
    min (d^2/v) d / 3≤d^2/(2*v+2*d/3) := by
  by_cases ZeroVariance : v=0
  · simp only [ZeroVariance,div_zero,min_eq_left NonnegativeDeviation,zero_div]
    positivity
  have PositiveVariance : 0<v := lt_of_le_of_ne NonnegativeVariance (Ne.symm ZeroVariance)
  have Bound := mul_le_mul_of_nonneg_left
    (ChernoffQuadraticMinLower (d/v) (div_nonneg NonnegativeDeviation NonnegativeVariance))
      NonnegativeVariance
  have Left : v*(min ((d/v)^2) (d/v)/3)=min (d^2/v) d/3 := by
    rw [← mul_div_assoc,mul_min_of_nonneg _ _ NonnegativeVariance]
    congr 2 <;> field_simp
  have Right : v*((d/v)^2/(2+2*(d/v)/3))=d^2/(2*v+2*d/3) := by
    field_simp
  rwa [Left,Right] at Bound

theorem IndependentSumBernsteinMinUpper {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      Real.exp (-min (d^2/(∑ i, variance (X i) P)) d/3) := by
  apply (IndependentSumBernsteinUpper P X SquareIntegrable Independent Upper d NonnegativeDeviation).trans
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg
    (BernsteinExponentMinLower _ d (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P))
      NonnegativeDeviation)

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Corollary1.10.13, Bennett portion, by negating the same independent family. -/
theorem IndependentSumBennettLower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-1≤X i ω)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d}≤
      BennettUpperBound (∑ i, variance (X i) P) d := by
  have IndependentNeg : iIndepFun (fun i ω => -X i ω) P :=
    Independent.comp (fun _ x => -x) (fun _ => measurable_neg)
  have UpperNeg (i : ι) : ∀ᵐ ω ∂P, -X i ω≤(∫ w, -X i w ∂P)+1 := by
    rw [integral_neg]
    filter_upwards [Lower i] with ω Bound
    linarith
  have Bound := IndependentSumBennettUpperAll P (fun i ω => -X i ω)
    (fun i => (SquareIntegrable i).neg) IndependentNeg UpperNeg d NonnegativeDeviation
  have Event : {ω | (∫ w, ∑ i, -X i w ∂P)+d≤∑ i, -X i ω}=
      {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d} := by
    simp only [Finset.sum_neg_distrib,integral_neg]
    ext ω
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [Event] at Bound
  simpa only [variance_fun_neg] using Bound

theorem IndependentSumBernsteinLower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-1≤X i ω)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d}≤
      Real.exp (-d^2/(2*(∑ i, variance (X i) P)+2*d/3)) :=
  (IndependentSumBennettLower P X SquareIntegrable Independent Lower d NonnegativeDeviation).trans
    (BennettUpperBoundLeBernstein _ d (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P))
      NonnegativeDeviation)

theorem IndependentSumBernsteinMinLower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-1≤X i ω)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤(∫ w, ∑ i, X i w ∂P)-d}≤
      Real.exp (-min (d^2/(∑ i, variance (X i) P)) d/3) := by
  apply (IndependentSumBernsteinLower P X SquareIntegrable Independent Lower d NonnegativeDeviation).trans
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg
    (BernsteinExponentMinLower _ d (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P))
      NonnegativeDeviation)

end
end ECTheoryLib.Probability


/-! Estimated sum thresholds retain actual coordinate centers and variances. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The estimate only changes the sum-event threshold, not coordinate centers or variance. -/
theorem IndependentSumBennettUpperOfMeanLe {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P)≤U)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | U+d≤∑ i, X i ω}≤
      BennettUpperBound (∑ i, variance (X i) P) d := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBennettUpperAll P X SquareIntegrable Independent Upper d NonnegativeDeviation)
  intro ω Bound
  exact le_trans (add_le_add MeanUpper (le_refl d)) Bound

/-- The estimate only changes the sum-event threshold, not coordinate centers or variance. -/
theorem IndependentSumBennettLowerOfLeMean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-1≤X i ω)
    (L : ℝ) (MeanLower : L≤(∫ w, ∑ i, X i w ∂P))
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤L-d}≤
      BennettUpperBound (∑ i, variance (X i) P) d := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBennettLower P X SquareIntegrable Independent Lower d NonnegativeDeviation)
  intro ω Bound
  exact le_trans Bound (sub_le_sub_right MeanLower d)

/-- The estimate only changes the sum-event threshold, not coordinate centers or variance. -/
theorem IndependentSumBernsteinUpperOfMeanLe {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P)≤U)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | U+d≤∑ i, X i ω}≤
      Real.exp (-d^2/(2*(∑ i, variance (X i) P)+2*d/3)) := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBernsteinUpper P X SquareIntegrable Independent Upper d NonnegativeDeviation)
  intro ω Bound
  exact le_trans (add_le_add MeanUpper (le_refl d)) Bound

/-- The estimate only changes the sum-event threshold, not coordinate centers or variance. -/
theorem IndependentSumBernsteinLowerOfLeMean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-1≤X i ω)
    (L : ℝ) (MeanLower : L≤(∫ w, ∑ i, X i w ∂P))
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤L-d}≤
      Real.exp (-d^2/(2*(∑ i, variance (X i) P)+2*d/3)) := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBernsteinLower P X SquareIntegrable Independent Lower d NonnegativeDeviation)
  intro ω Bound
  exact le_trans Bound (sub_le_sub_right MeanLower d)

/-- The estimate only changes the sum-event threshold, not coordinate centers or variance. -/
theorem IndependentSumBernsteinMinUpperOfMeanLe {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P)≤U)
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | U+d≤∑ i, X i ω}≤
      Real.exp (-min (d^2/(∑ i, variance (X i) P)) d/3) := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBernsteinMinUpper P X SquareIntegrable Independent Upper d NonnegativeDeviation)
  intro ω Bound
  exact le_trans (add_le_add MeanUpper (le_refl d)) Bound

/-- The estimate only changes the sum-event threshold, not coordinate centers or variance. -/
theorem IndependentSumBernsteinMinLowerOfLeMean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P) (Independent : iIndepFun X P)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, X i w ∂P)-1≤X i ω)
    (L : ℝ) (MeanLower : L≤(∫ w, ∑ i, X i w ∂P))
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∑ i, X i ω)≤L-d}≤
      Real.exp (-min (d^2/(∑ i, variance (X i) P)) d/3) := by
  apply le_trans (measureReal_mono ?_)
    (IndependentSumBernsteinMinLower P X SquareIntegrable Independent Lower d NonnegativeDeviation)
  intro ω Bound
  exact le_trans Bound (sub_le_sub_right MeanLower d)

end
end ECTheoryLib.Probability



/-! Relative upper thresholds preserve the actual variance and a nonnegative mean estimate. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- A relative upper threshold uses the actual centers and variance, with nonnegative estimate. -/
theorem IndependentSumBennettRelativeUpperOfMeanLe {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + 1)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ U)
    (NonnegativeEstimate : 0 ≤ U) (δ : ℝ) (NonnegativeRelative : 0 ≤ δ) :
    P.real {ω | (1 + δ) * U ≤ ∑ i, X i ω} ≤
      BennettUpperBound (∑ i, variance (X i) P) (δ * U) := by
  have Bound := IndependentSumBennettUpperOfMeanLe P X SquareIntegrable Independent Upper
    U MeanUpper (δ * U) (mul_nonneg NonnegativeRelative NonnegativeEstimate)
  simpa only [add_mul, one_mul] using Bound

/-- The source multiplicative Bernstein form keeps the actual marginal variance sum. -/
theorem IndependentSumBernsteinRelativeUpperOfMeanLe {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + 1)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ U)
    (NonnegativeEstimate : 0 ≤ U) (δ : ℝ) (NonnegativeRelative : 0 ≤ δ) :
    P.real {ω | (1 + δ) * U ≤ ∑ i, X i ω} ≤
      Real.exp (-(δ ^ 2 * U ^ 2) / (2 * (∑ i, variance (X i) P) + 2 * δ * U / 3)) := by
  have Bound := IndependentSumBernsteinUpperOfMeanLe P X SquareIntegrable Independent Upper
    U MeanUpper (δ * U) (mul_nonneg NonnegativeRelative NonnegativeEstimate)
  simpa only [add_mul, one_mul, mul_pow, mul_assoc] using Bound

/-- The totalized minimum expression retains its existing weak zero-variance convention. -/
theorem IndependentSumBernsteinMinRelativeUpperOfMeanLe {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Independent : iIndepFun X P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ (∫ w, X i w ∂P) + 1)
    (U : ℝ) (MeanUpper : (∫ w, ∑ i, X i w ∂P) ≤ U)
    (NonnegativeEstimate : 0 ≤ U) (δ : ℝ) (NonnegativeRelative : 0 ≤ δ) :
    P.real {ω | (1 + δ) * U ≤ ∑ i, X i ω} ≤
      Real.exp (-min (δ ^ 2 * U ^ 2 / (∑ i, variance (X i) P)) (δ * U) / 3) := by
  have Bound := IndependentSumBernsteinMinUpperOfMeanLe P X SquareIntegrable Independent Upper
    U MeanUpper (δ * U) (mul_nonneg NonnegativeRelative NonnegativeEstimate)
  simpa only [add_mul, one_mul, mul_pow] using Bound

end
end ECTheoryLib.Probability

