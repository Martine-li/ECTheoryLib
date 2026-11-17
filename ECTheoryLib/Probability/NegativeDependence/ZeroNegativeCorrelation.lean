import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelation
import ECTheoryLib.Probability.Concentration.LowerChernoff

/-!
# Zero-negative correlation and lower concentration

Part of Doerr Theorem 1.10.24, printed page 66. Ordered affine variables
use the original event indicators on the same sample point. Nonpositive
tilts are controlled by complement-event product bounds. Unweighted
logarithmic, power and quadratic lower tails include d=1, empty families
and zero mean; finite-size, variance and mean-replacement formulas remain
separate work. No independence of the dependent indicators is assumed.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Nonpositive tilts use zero-negative correlation. Each affine variable
is defined using its actual event on the same sample point. -/
theorem ZeroNegativeCorrelationAffineMGF {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events)
    (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (t : ℝ) (Nonpositive : t≤0) :
    mgf (fun ω => ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)) P t≤
      ∏ i, ((1-P.real (Events i))*Real.exp (t*a i)+P.real (Events i)*Real.exp (t*b i)) := by
  have CoefficientNonnegative (i : ι) : 0≤Real.exp (t*a i)-Real.exp (t*b i) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Ordered i) Nonpositive)
  have Bound := OneNegativeCorrelationAffineProduct P (fun i => (Events i)ᶜ)
    (fun i => (MeasurableEvents i).compl) Correlated
    (fun i => Real.exp (t*b i)) (fun i => Real.exp (t*a i)-Real.exp (t*b i))
    (fun i => (Real.exp_pos _).le) CoefficientNonnegative Finset.univ
  have Pointwise (i : ι) (ω : Ω) :
      Real.exp (t*(a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))=
        Real.exp (t*b i)+(Real.exp (t*a i)-Real.exp (t*b i))*(Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases Inside : ω∈Events i <;> simp [Inside]
  have Exponential :
      (fun ω => Real.exp (t*(∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))))=
        (fun ω => ∏ i, (Real.exp (t*b i)+(Real.exp (t*a i)-Real.exp (t*b i))*
          (Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω)) := by
    funext ω
    rw [Finset.mul_sum,Real.exp_sum]
    exact Finset.prod_congr rfl (fun i _ => Pointwise i ω)
  unfold mgf
  rw [Exponential]
  apply Bound.trans_eq
  apply Finset.prod_congr rfl
  intro i _
  rw [probReal_compl_eq_one_sub (MeasurableEvents i)]
  ring

/-- The event count has the Bernoulli MGF estimate for nonpositive tilts. -/
theorem ZeroNegativeCorrelationCountMGF {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (t : ℝ) (Nonpositive : t≤0) :
    mgf (fun ω => ∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω) P t≤
      Real.exp ((∑ i, P.real (Events i))*(Real.exp t-1)) := by
  have Bound := ZeroNegativeCorrelationAffineMGF P Events MeasurableEvents Correlated
    (fun _ => 0) (fun _ => 1) (fun _ => zero_le_one) t Nonpositive
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

/-- At zero count the all-subset condition applies directly, avoiding an
undefined optimizing tilt at d=1. -/
theorem ZeroNegativeCorrelationCountZero {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) :
    P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤0}≤
      Real.exp (-(∑ i, P.real (Events i))) := by
  classical
  have Event : {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤0}=
      ⋂ i∈(Finset.univ : Finset ι), (Events i)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq,mem_iInter,Finset.mem_univ,mem_compl_iff,forall_true_left]
    constructor
    · intro CountNonpositive i Inside
      have Nonnegative (j : ι) : 0≤(Events j).indicator (fun _ => (1 : ℝ)) ω := by
        by_cases InEvent : ω∈Events j <;> simp [InEvent]
      have Bound := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset ι)) => Nonnegative j)
        (Finset.mem_univ i)
      simp only [indicator_of_mem Inside] at Bound
      linarith
    · intro Outside
      simp [indicator_of_notMem (Outside _)]
  rw [Event]
  have Bound := Correlated Finset.univ
  apply Bound.trans
  calc
    _≤∏ i, Real.exp (-P.real (Events i)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact ENNReal.toReal_nonneg
      · intro i _
        rw [probReal_compl_eq_one_sub (MeasurableEvents i)]
        have Bound := Real.add_one_le_exp (-P.real (Events i))
        linarith
    _=_ := by rw [← Real.exp_sum,Finset.sum_neg_distrib]

/-- Closed multiplicative lower tail for zero-negatively correlated events,
including d=1, empty families and zero expectation. -/
theorem ZeroNegativeCorrelationChernoffLower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*(∑ i, P.real (Events i))}≤
      Real.exp (-(d+(1-d)*Real.log (1-d))*(∑ i, P.real (Events i))) := by
  by_cases Endpoint : d=1
  · subst d
    simp only [sub_self,zero_mul,add_zero,neg_mul,one_mul]
    exact ZeroNegativeCorrelationCountZero P Events MeasurableEvents Correlated
  have BelowOne : d<1 := lt_of_le_of_ne InUnit.2 Endpoint
  have MeasurableCount := (EventCountMeasurable Events MeasurableEvents).aemeasurable (μ := P)
  have Bounded : ∀ᵐ ω ∂P, (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)∈Icc 0 (Fintype.card ι : ℝ) :=
    ae_of_all _ (EventCountInUnitSum Events)
  have Certificate := ZeroNegativeCorrelationCountMGF P Events MeasurableEvents Correlated
    (Real.log (1-d)) (Real.log_nonpos (by linarith [InUnit.2]) (by linarith [InUnit.1]))
  rw [Real.exp_log (sub_pos.mpr BelowOne)] at Certificate
  have Exponent : (∑ i, P.real (Events i))*(1-d-1)= -(∑ i, P.real (Events i))*d := by ring
  rw [Exponent] at Certificate
  exact MGFMultiplicativeLowerTailInterior P _ _ d InUnit.1 BelowOne
    (integrable_exp_mul_of_mem_Icc MeasurableCount Bounded) Certificate

/-- The usual quadratic lower bound uses the actual sum of marginals. -/
theorem ZeroNegativeCorrelationChernoffLowerQuadratic {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*(∑ i, P.real (Events i))}≤
      Real.exp (-(d^2/2)*(∑ i, P.real (Events i))) := by
  apply (ZeroNegativeCorrelationChernoffLower P Events MeasurableEvents Correlated d InUnit).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg (ChernoffLowerExponentQuadratic d InUnit))
    (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

/-- The source power expression is also valid at d=1 with 0^0=1. -/
theorem ZeroNegativeCorrelationChernoffLowerPower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, (Events i).indicator (fun _ => (1 : ℝ)) ω)≤(1-d)*(∑ i, P.real (Events i))}≤
      (Real.exp (-d)/(1-d)^(1-d))^(∑ i, P.real (Events i)) := by
  rw [ChernoffLowerPowerExpression d _ InUnit]
  exact ZeroNegativeCorrelationChernoffLower P Events MeasurableEvents Correlated d InUnit

end
end ECTheoryLib.Probability
