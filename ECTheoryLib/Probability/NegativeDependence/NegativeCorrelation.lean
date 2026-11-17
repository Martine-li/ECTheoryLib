import ECTheoryLib.Probability.Concentration.Chernoff
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Event negative correlation and upper concentration

Source: Doerr Section 1.10.2.2 and part of Theorem 1.10.23. The condition
quantifies over every finite subfamily. Weighted affine MGF estimates use
the actual indicators on the same sample point; separate marginal laws
do not preserve the joint distribution. Only the exponential and quadratic
unweighted Chernoff tails are claimed here, not every formula cited in
Theorem 1.10.23. Mathlib supplies subset-product expansion and integration.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section

/-- One-negative correlation of event indicators uses every finite subfamily,
not merely pairwise comparisons. -/
def OneNegativelyCorrelated {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Events : ι → Set Ω) : Prop :=
  ∀ A : Finset ι, P.real (⋂ i∈A, Events i)≤∏ i∈A, P.real (Events i)

/-- Zero-negative correlation is one-negative correlation of complements. -/
def ZeroNegativelyCorrelated {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Events : ι → Set Ω) : Prop :=
  OneNegativelyCorrelated P (fun i => (Events i)ᶜ)

/-- Mathlib independence implies the event-product condition by equality. -/
theorem OneNegativeCorrelationOfIndependent {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Events : ι → Set Ω) (Independent : ProbabilityTheory.iIndepSet Events P) :
    OneNegativelyCorrelated P Events := by
  intro A
  unfold Measure.real
  rw [Independent.meas_biInter,ENNReal.toReal_prod]


theorem EventIndicatorProduct {Ω ι : Type*} (Events : ι → Set Ω) (A : Finset ι) :
    (fun ω => ∏ i∈A, (Events i).indicator (fun _ => (1 : ℝ)) ω)=
      (⋂ i∈A, Events i).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  have ConstantPower : (fun _ : Ω => (1 : ℝ))^A.card=(fun _ => (1 : ℝ)) := by
    funext _
    exact one_pow _
  rw [prod_indicator_const_apply,ConstantPower]

theorem EventIndicatorProductIntegrable {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i)) (A : Finset ι) :
    Integrable (fun ω => ∏ i∈A, (Events i).indicator (fun _ => (1 : ℝ)) ω) P := by
  rw [EventIndicatorProduct]
  exact (integrable_const (1 : ℝ)).indicator (A.measurableSet_biInter (fun i _ => MeasurableEvents i))

theorem EventIndicatorProductIntegral {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i)) (A : Finset ι) :
    (∫ ω, ∏ i∈A, (Events i).indicator (fun _ => (1 : ℝ)) ω ∂P)=P.real (⋂ i∈A, Events i) := by
  rw [EventIndicatorProduct,integral_indicator_const _ (A.measurableSet_biInter (fun i _ => MeasurableEvents i))]
  simp only [smul_eq_mul,mul_one]

/-- Expanding a product by subsets transfers all finite joint-event bounds.
The coefficients must be nonnegative; the variables need not be independent. -/
theorem OneNegativeCorrelationAffineProduct {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events)
    (a b : ι → ℝ) (NonnegativeA : ∀ i, 0≤a i) (NonnegativeB : ∀ i, 0≤b i)
    (A : Finset ι) :
    (∫ ω, ∏ i∈A, (a i+b i*(Events i).indicator (fun _ => (1 : ℝ)) ω) ∂P)≤
      ∏ i∈A, (a i+b i*P.real (Events i)) := by
  classical
  have Expansion (ω : Ω) :
      (∏ i∈A, (a i+b i*(Events i).indicator (fun _ => (1 : ℝ)) ω))=
        ∑ S∈A.powerset, ((∏ i∈S, b i)*(∏ i∈A\S, a i))*
          (∏ i∈S, (Events i).indicator (fun _ => (1 : ℝ)) ω) := by
    simp_rw [add_comm (a _) (_ * _)]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [Expansion]
  rw [integral_finsetSum _ (fun S _ =>
    (EventIndicatorProductIntegrable P Events MeasurableEvents S).const_mul _)]
  simp_rw [integral_const_mul,EventIndicatorProductIntegral P Events MeasurableEvents]
  calc
    _≤∑ S∈A.powerset, ((∏ i∈S, b i)*(∏ i∈A\S, a i))*(∏ i∈S, P.real (Events i)) := by
      apply Finset.sum_le_sum
      intro S _
      exact mul_le_mul_of_nonneg_left (Correlated S)
        (mul_nonneg (Finset.prod_nonneg (fun i _ => NonnegativeB i))
          (Finset.prod_nonneg (fun i _ => NonnegativeA i)))
    _=∏ i∈A, (a i+b i*P.real (Events i)) := by
      simp_rw [add_comm (a _) (_ * _)]
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib]
      ring

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Nonnegative tilts preserve the product MGF upper estimate under
one-negative correlation. The affine variables are defined on the same
sample point; merely specifying their marginal laws would not suffice. -/
theorem OneNegativeCorrelationAffineMGF {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events)
    (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (t : ℝ) (Nonnegative : 0≤t) :
    mgf (fun ω => ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)) P t≤
      ∏ i, ((1-P.real (Events i))*Real.exp (t*a i)+P.real (Events i)*Real.exp (t*b i)) := by
  have CoefficientNonnegative (i : ι) : 0≤Real.exp (t*b i)-Real.exp (t*a i) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Ordered i) Nonnegative)
  have Bound := OneNegativeCorrelationAffineProduct P Events MeasurableEvents Correlated
    (fun i => Real.exp (t*a i)) (fun i => Real.exp (t*b i)-Real.exp (t*a i))
    (fun i => (Real.exp_pos _).le) CoefficientNonnegative Finset.univ
  have Pointwise (i : ι) (ω : Ω) :
      Real.exp (t*(a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))=
        Real.exp (t*a i)+(Real.exp (t*b i)-Real.exp (t*a i))*(Events i).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases Inside : ω∈Events i
    · simp [Inside]
    · simp [Inside]
  have Exponential :
      (fun ω => Real.exp (t*(∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))))=
        (fun ω => ∏ i, (Real.exp (t*a i)+(Real.exp (t*b i)-Real.exp (t*a i))*
          (Events i).indicator (fun _ => (1 : ℝ)) ω)) := by
    funext ω
    rw [Finset.mul_sum,Real.exp_sum]
    exact Finset.prod_congr rfl (fun i _ => Pointwise i ω)
  unfold mgf
  rw [Exponential]
  apply Bound.trans_eq
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- The unweighted event count has the familiar Bernoulli MGF estimate. -/
theorem OneNegativeCorrelationCountMGF {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (t : ℝ) (Nonnegative : 0≤t) :
    mgf (fun ω => ∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω) P t≤
      Real.exp ((∑ i, P.real (Events i))*(Real.exp t-1)) := by
  have Bound := OneNegativeCorrelationAffineMGF P Events MeasurableEvents Correlated
    (fun _ => 0) (fun _ => 1) (fun _ => zero_le_one) t Nonnegative
  simp only [sub_zero,one_mul,zero_add,mul_zero,Real.exp_zero,mul_one] at Bound
  apply Bound.trans
  calc
    _≤∏ i, Real.exp (P.real (Events i)*(Real.exp t-1)) := by
      apply Finset.prod_le_prod
      · intro i _
        have Probability := measureReal_le_one (μ := P) (s := Events i)
        positivity
      · intro i _
        have Linear := Real.add_one_le_exp (P.real (Events i)*(Real.exp t-1))
        nlinarith
    _=_ := by rw [← Real.exp_sum,Finset.sum_mul]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem EventCountMeasurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Events : ι → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i)) :
    Measurable (fun ω => ∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.indicator (MeasurableEvents i))

theorem EventCountInUnitSum {Ω ι : Type*} [Fintype ι]
    (Events : ι → Set Ω) (ω : Ω) :
    (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)∈Icc 0 (Fintype.card ι : ℝ) := by
  classical
  have Each (i : ι) : (Events i).indicator (fun _ => (1 : ℝ)) ω∈Icc 0 1 := by
    by_cases Inside : ω∈Events i <;> simp [Inside]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (Each i).1)
  · calc
      _≤∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Each i).2)
      _=_ := by simp

/-- The mean used in the tail bound is the actual integral, even when
the event indicators are dependent. -/
theorem EventCountExpectation {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i)) :
    (∫ ω, ∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω ∂P)=∑ i, P.real (Events i) := by
  rw [integral_finsetSum _ (fun i _ => (integrable_const (1 : ℝ)).indicator (MeasurableEvents i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator_const _ (MeasurableEvents i)]
  simp only [smul_eq_mul,mul_one]

/-- Closed multiplicative upper tail for one-negatively correlated events. -/
theorem OneNegativeCorrelationChernoffUpper {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (1+d)*(∑ i, P.real (Events i))≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}≤
      Real.exp (-((1+d)*Real.log (1+d)-d)*(∑ i, P.real (Events i))) := by
  have MeasurableCount := (EventCountMeasurable Events MeasurableEvents).aemeasurable (μ := P)
  have Bounded : ∀ᵐ ω ∂P, (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)∈Icc 0 (Fintype.card ι : ℝ) :=
    ae_of_all _ (EventCountInUnitSum Events)
  have Certificate := OneNegativeCorrelationCountMGF P Events MeasurableEvents Correlated
    (Real.log (1+d)) (Real.log_nonneg (by linarith))
  rw [Real.exp_log (by linarith : 0<1+d),add_sub_cancel_left] at Certificate
  exact MGFMultiplicativeUpperTail P _ _ d Nonnegative
    (integrable_exp_mul_of_mem_Icc MeasurableCount Bounded) Certificate

/-- A variance-independent quadratic simplification, including zero mean. -/
theorem OneNegativeCorrelationChernoffUpperQuadratic {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (1+d)*(∑ i, P.real (Events i))≤∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω}≤
      Real.exp (-(d^2*(∑ i, P.real (Events i)))/(2+2*d/3)) := by
  have MeanNonnegative : 0≤∑ i, P.real (Events i) := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  apply (OneNegativeCorrelationChernoffUpper P Events MeasurableEvents Correlated d Nonnegative).trans
  apply Real.exp_le_exp.mpr
  have Exponent := mul_le_mul_of_nonneg_right (ChernoffExponentQuadraticLower d Nonnegative) MeanNonnegative
  rw [div_mul_eq_mul_div] at Exponent
  simpa only [neg_mul,neg_div] using neg_le_neg Exponent

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory Set
noncomputable section

/-- Restriction to a subfamily preserves all-subset negative correlation.
Injectivity is essential: repeating one event does not preserve the bound. -/
theorem OneNegativeCorrelationReindex {Ω ι κ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Events : ι → Set Ω) (Correlated : OneNegativelyCorrelated P Events)
    (f : κ → ι) (Injective : Function.Injective f) :
    OneNegativelyCorrelated P (fun j => Events (f j)) := by
  classical
  intro A
  have Bound := Correlated (A.image f)
  have Intersection : (⋂ i∈A.image f, Events i)=⋂ j∈A, Events (f j) := by
    ext ω
    simp
  rw [Intersection,Finset.prod_image (fun i _ j _ Equal => Injective Equal)] at Bound
  exact Bound

theorem ZeroNegativeCorrelationReindex {Ω ι κ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Events : ι → Set Ω) (Correlated : ZeroNegativelyCorrelated P Events)
    (f : κ → ι) (Injective : Function.Injective f) :
    ZeroNegativelyCorrelated P (fun j => Events (f j)) :=
  OneNegativeCorrelationReindex P (fun i => (Events i)ᶜ) Correlated f Injective

end
end ECTheoryLib.Probability
