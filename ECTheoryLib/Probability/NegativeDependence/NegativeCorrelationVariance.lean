import ECTheoryLib.Probability.Concentration.BennettCertificate
import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationChernoff

/-!
# Variance tails under all-subset negative correlation

Same-sample ordered affine indicators yield Bennett upper/lower bounds
under the appropriate one/zero-negative correlation and a centered bound
of1. Endpoints need not lie in[0,1]. Variance means the sum of marginal
variances; it is not identified with the variance of the total. Existing
scalar comparisons give Bernstein/min consequences. The strongest finite
variance bound, general scale and all mean replacements remain separate.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem AffineIndicatorMemLpTwo {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω) (MeasurableE : MeasurableSet E)
    (a b : ℝ) (Ordered : a≤b) :
    MemLp (fun ω => a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω) 2 P :=
  memLp_of_bounded (ae_of_all _ (AffineIndicatorInInterval E a b Ordered))
    (AffineIndicatorMeasurable E MeasurableE a b).aestronglyMeasurable 2

/-- Marginal variance of an actual two-point affine indicator, without
any assumption on dependence between different coordinates. -/
theorem AffineIndicatorVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω) (MeasurableE : MeasurableSet E)
    (a b : ℝ) (Ordered : a≤b) :
    variance (fun ω => a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω) P=
      (b-a)^2*P.real E*(1-P.real E) := by
  rw [variance_eq_sub (AffineIndicatorMemLpTwo P E MeasurableE a b Ordered)]
  change (∫ ω, (a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω)^2 ∂P)-
    (∫ ω, a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω ∂P)^2=_
  have Square (ω : Ω) : (a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω)^2=
      a^2+(b^2-a^2)*E.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases Inside : ω∈E <;> simp [Inside]
  simp_rw [Square]
  rw [AffineIndicatorIntegral P E MeasurableE,AffineIndicatorIntegral P E MeasurableE]
  ring

/-- All-subset one-negative correlation controls the centered sum MGF.
Its variance parameter remains the marginal sum; covariance is not erased. -/
theorem OneNegativeCorrelationAffineBennettMGF {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i)
    (Upper : ∀ i, ∀ᵐ ω ∂P, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω≤
      (∫ w, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w ∂P)+1)
    (t : ℝ) (Nonnegative : 0≤t) :
    mgf (fun ω => (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))-
      (∫ w, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) ∂P)) P t≤
      Real.exp ((∑ i, variance (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) P)*
        (Real.exp t-1-t)) := by
  let X := fun i ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω
  let m := fun i => ∫ ω, X i ω ∂P
  have OrderedShift (i : ι) : a i-m i≤b i-m i := sub_le_sub_right (Ordered i) _
  have Bound := OneNegativeCorrelationAffineMGF P Events MeasurableEvents Correlated
    (fun i => a i-m i) (fun i => b i-m i) OrderedShift t Nonnegative
  have Pointwise (i : ι) (ω : Ω) :
      a i-m i+(b i-m i-(a i-m i))*(Events i).indicator (fun _ => (1 : ℝ)) ω=X i ω-m i := by
    dsimp only [X]
    ring
  have MeanSum : (∫ ω, ∑ i, X i ω ∂P)=∑ i, m i :=
    integral_finsetSum _ (fun i _ => (AffineIndicatorMemLpTwo P _ (MeasurableEvents i) _ _ (Ordered i)).integrable (by norm_num))
  simp_rw [Pointwise,Finset.sum_sub_distrib,← MeanSum] at Bound
  apply Bound.trans
  calc
    _≤∏ i, Real.exp (variance (X i) P*(Real.exp t-1-t)) := by
      apply Finset.prod_le_prod
      · intro i _
        rw [← AffineIndicatorMGF P _ (MeasurableEvents i)]
        exact mgf_nonneg
      · intro i _
        rw [← AffineIndicatorMGF P _ (MeasurableEvents i)]
        simp_rw [Pointwise]
        exact BennettCenteredVariableMGF P (X i)
          (AffineIndicatorMemLpTwo P _ (MeasurableEvents i) _ _ (Ordered i)) (Upper i) t Nonnegative
    _=_ := by rw [← Real.exp_sum,Finset.sum_mul]

theorem OneNegativeCorrelationAffineBennettUpper {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i)
    (Upper : ∀ i, ∀ᵐ ω ∂P, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω≤
      (∫ w, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w ∂P)+1)
    (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (∫ w, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) ∂P)+d≤
      ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)}≤
      BennettUpperBound (∑ i, variance (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) P) d :=
  SumBennettUpperOfCertificate P _
    (fun i => AffineIndicatorMemLpTwo P _ (MeasurableEvents i) _ _ (Ordered i)) Upper
    (OneNegativeCorrelationAffineBennettMGF P Events MeasurableEvents Correlated a b Ordered Upper) d Nonnegative

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Negating an ordered affine indicator reverses endpoints and complements
the same event. It does not replace the variable by a marginal copy. -/
theorem NegatedAffineIndicator {Ω : Type*} (E : Set Ω) (a b : ℝ) (ω : Ω) :
    -b+(-a- -b)*Eᶜ.indicator (fun _ => (1 : ℝ)) ω=
      -(a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω) := by
  by_cases Inside : ω∈E <;> simp [Inside]

theorem ZeroNegativeCorrelationAffineBennettLower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i)
    (Lower : ∀ i, ∀ᵐ ω ∂P, (∫ w, a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w ∂P)-1≤
      a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)
    (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤
      (∫ w, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) w) ∂P)-d}≤
      BennettUpperBound (∑ i, variance (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) P) d := by
  have UpperNeg (i : ι) : ∀ᵐ ω ∂P,
      -b i+(-a i- -b i)*(Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω≤
        (∫ w, -b i+(-a i- -b i)*(Events i)ᶜ.indicator (fun _ => (1 : ℝ)) w ∂P)+1 := by
    simp_rw [NegatedAffineIndicator,integral_neg]
    filter_upwards [Lower i] with ω Bound
    linarith
  have Bound := OneNegativeCorrelationAffineBennettUpper P (fun i => (Events i)ᶜ)
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
