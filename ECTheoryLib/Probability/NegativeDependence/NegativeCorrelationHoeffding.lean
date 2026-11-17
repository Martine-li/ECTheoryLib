import ECTheoryLib.Probability.NegativeDependence.ZeroNegativeCorrelation
import ECTheoryLib.Probability.Moments.BoundedExponentialMoment

/-!
# Hoeffding tails for negatively correlated affine indicators

The affine variables share the actual indicator family and sample point.
Endpoints may lie outside the unit interval and have negative offsets;
their order ensures nonnegative indicator coefficients. Mathlib supplies
the single-variable Hoeffding lemma. One-negative correlation handles
upper tails, zero-negative correlation lower tails. The sum of marginal
means is proved equal to the actual integral, with valid one-sided mean
replacements. This completes the Hoeffding portion of1.10.23(b)/24(b),
not every listed variance or multiplicative formula. Zero total width uses
the real-division convention giving the trivial upper bound1.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Exact affine indicator expectation; endpoints may be negative. -/
theorem AffineIndicatorIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω) (MeasurableE : MeasurableSet E) (a b : ℝ) :
    (∫ ω, a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω ∂P)=a+(b-a)*P.real E := by
  rw [integral_add (integrable_const a) (((integrable_const (1 : ℝ)).indicator MeasurableE).const_mul (b-a)),
    integral_const,integral_const_mul,integral_indicator_const _ MeasurableE]
  simp only [probReal_univ,smul_eq_mul,mul_one,one_mul]

theorem AffineIndicatorMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (E : Set Ω) (MeasurableE : MeasurableSet E) (a b : ℝ) :
    Measurable (fun ω => a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω) :=
  measurable_const.add (measurable_const.mul (measurable_const.indicator MeasurableE))

theorem AffineIndicatorInInterval {Ω : Type*} (E : Set Ω) (a b : ℝ) (Ordered : a≤b) (ω : Ω) :
    a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω∈Icc a b := by
  by_cases Inside : ω∈E <;> simp [Inside,Ordered]

/-- The actual affine variable's exponential moment is its two-point marginal mixture. -/
theorem AffineIndicatorMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω) (MeasurableE : MeasurableSet E) (a b t : ℝ) :
    mgf (fun ω => a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω) P t=
      (1-P.real E)*Real.exp (t*a)+P.real E*Real.exp (t*b) := by
  have Pointwise :
      (fun ω => Real.exp (t*(a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω)))=
        (fun ω => Real.exp (t*a)+(Real.exp (t*b)-Real.exp (t*a))*E.indicator (fun _ => (1 : ℝ)) ω) := by
    funext ω
    by_cases Inside : ω∈E <;> simp [Inside]
  unfold mgf
  rw [Pointwise,AffineIndicatorIntegral P E MeasurableE]
  ring

/-- Mathlib's Hoeffding lemma applied to the actual affine indicator. -/
theorem AffineIndicatorHoeffdingMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω) (MeasurableE : MeasurableSet E)
    (a b t : ℝ) (Ordered : a≤b) :
    (1-P.real E)*Real.exp (t*a)+P.real E*Real.exp (t*b)≤
      Real.exp (t*(a+(b-a)*P.real E)+(b-a)^2*t^2/8) := by
  have Bound := BoundedVariableExponentialMoment P
    (fun ω => a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω) a b t
    (AffineIndicatorMeasurable E MeasurableE a b).aemeasurable
    (Filter.Eventually.of_forall (AffineIndicatorInInterval E a b Ordered))
  rw [AffineIndicatorIntegral P E MeasurableE] at Bound
  change mgf (fun ω => a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω) P t≤_ at Bound
  rwa [AffineIndicatorMGF P E MeasurableE] at Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem AffineSumMeasurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Events : ι → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i)) (a b : ι → ℝ) :
    Measurable (fun ω => ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)) := by
  exact Finset.measurable_sum _ (fun i _ => AffineIndicatorMeasurable (Events i) (MeasurableEvents i) (a i) (b i))

theorem AffineSumInInterval {Ω ι : Type*} [Fintype ι]
    (Events : ι → Set Ω) (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (ω : Ω) :
    (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))∈Icc (∑ i, a i) (∑ i, b i) := by
  constructor
  · exact Finset.sum_le_sum (fun i _ => (AffineIndicatorInInterval (Events i) (a i) (b i) (Ordered i) ω).1)
  · exact Finset.sum_le_sum (fun i _ => (AffineIndicatorInInterval (Events i) (a i) (b i) (Ordered i) ω).2)

/-- The parameter used in the affine concentration bounds is the actual
same-sample expectation. No independence or correlation assumption is needed. -/
theorem AffineSumIntegral {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i)) (a b : ι → ℝ) :
    (∫ ω, ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω) ∂P)=
      ∑ i, (a i+(b i-a i)*P.real (Events i)) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact AffineIndicatorIntegral P (Events i) (MeasurableEvents i) (a i) (b i)
  · intro i _
    exact (integrable_const (a i)).add
      (((integrable_const (1 : ℝ)).indicator (MeasurableEvents i)).const_mul (b i-a i))

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- One-negative correlation suffices for the positive-tilt Hoeffding MGF
estimate of the same-sample affine sum. No independent replacement family is assumed. -/
theorem OneNegativeCorrelationHoeffdingMGF {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events)
    (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (t : ℝ) (Nonnegative : 0≤t) :
    mgf (fun ω => ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)) P t≤
      Real.exp (t*(∑ i, (a i+(b i-a i)*P.real (Events i)))+(∑ i, (b i-a i)^2)*t^2/8) := by
  apply (OneNegativeCorrelationAffineMGF P Events MeasurableEvents Correlated a b Ordered t Nonnegative).trans
  calc
    _ ≤ ∏ i, Real.exp (t*(a i+(b i-a i)*P.real (Events i))+(b i-a i)^2*t^2/8) := by
      apply Finset.prod_le_prod
      · intro i _
        have ProbabilityBound := measureReal_le_one (μ := P) (s := Events i)
        positivity
      · intro i _
        exact AffineIndicatorHoeffdingMGF P (Events i) (MeasurableEvents i) (a i) (b i) t (Ordered i)
    _ = _ := by
      rw [← Real.exp_sum,Finset.sum_add_distrib,← Finset.mul_sum,
        ← Finset.sum_div,← Finset.sum_mul]

theorem ZeroNegativeCorrelationHoeffdingMGF {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events)
    (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (t : ℝ) (Nonpositive : t≤0) :
    mgf (fun ω => ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)) P t≤
      Real.exp (t*(∑ i, (a i+(b i-a i)*P.real (Events i)))+(∑ i, (b i-a i)^2)*t^2/8) := by
  apply (ZeroNegativeCorrelationAffineMGF P Events MeasurableEvents Correlated a b Ordered t Nonpositive).trans
  calc
    _ ≤ ∏ i, Real.exp (t*(a i+(b i-a i)*P.real (Events i))+(b i-a i)^2*t^2/8) := by
      apply Finset.prod_le_prod
      · intro i _
        have ProbabilityBound := measureReal_le_one (μ := P) (s := Events i)
        positivity
      · intro i _
        exact AffineIndicatorHoeffdingMGF P (Events i) (MeasurableEvents i) (a i) (b i) t (Ordered i)
    _ = _ := by
      rw [← Real.exp_sum,Finset.sum_add_distrib,← Finset.mul_sum,
        ← Finset.sum_div,← Finset.sum_mul]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Hoeffding upper deviation for an actual affine sum of one-negatively
correlated indicators. Endpoints need not lie in the unit interval. -/
theorem OneNegativeCorrelationHoeffdingUpper {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events)
    (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (∑ i, (a i+(b i-a i)*P.real (Events i)))+d≤
      ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)}≤
        Real.exp (-2*d^2/(∑ i, (b i-a i)^2)) := by
  let Width := ∑ i, (b i-a i)^2
  let Mean := ∑ i, (a i+(b i-a i)*P.real (Events i))
  by_cases ZeroWidth : Width=0
  · change _≤Real.exp (-2*d^2/Width)
    rw [ZeroWidth,div_zero,Real.exp_zero]
    exact measureReal_le_one
  have WidthPositive : 0<Width := lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm ZeroWidth)
  let Tilt := 4*d/Width
  have TiltNonnegative : 0≤Tilt := div_nonneg (by positivity) WidthPositive.le
  have IntegrableExp : Integrable
      (fun ω => Real.exp (Tilt*(∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)))) P :=
    integrable_exp_mul_of_mem_Icc (AffineSumMeasurable Events MeasurableEvents a b).aemeasurable
      (Filter.Eventually.of_forall (AffineSumInInterval Events a b Ordered))
  have Bound := measure_ge_le_exp_mul_mgf (Mean+d) TiltNonnegative IntegrableExp
  apply Bound.trans
  calc
    _ ≤ Real.exp (-Tilt*(Mean+d))*Real.exp (Tilt*Mean+Width*Tilt^2/8) :=
      mul_le_mul_of_nonneg_left
        (OneNegativeCorrelationHoeffdingMGF P Events MeasurableEvents Correlated a b Ordered Tilt TiltNonnegative)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      change -(4*d/Width)*(Mean+d)+((4*d/Width)*Mean+Width*(4*d/Width)^2/8)= -2*d^2/Width
      field_simp
      ring

/-- The nonpositive-tilt counterpart uses zero-negative correlation. -/
theorem ZeroNegativeCorrelationHoeffdingLower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events)
    (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤
      (∑ i, (a i+(b i-a i)*P.real (Events i)))-d}≤
        Real.exp (-2*d^2/(∑ i, (b i-a i)^2)) := by
  let Width := ∑ i, (b i-a i)^2
  let Mean := ∑ i, (a i+(b i-a i)*P.real (Events i))
  by_cases ZeroWidth : Width=0
  · change _≤Real.exp (-2*d^2/Width)
    rw [ZeroWidth,div_zero,Real.exp_zero]
    exact measureReal_le_one
  have WidthPositive : 0<Width := lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm ZeroWidth)
  let Tilt := -4*d/Width
  have TiltNonpositive : Tilt≤0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) WidthPositive.le
  have IntegrableExp : Integrable
      (fun ω => Real.exp (Tilt*(∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)))) P :=
    integrable_exp_mul_of_mem_Icc (AffineSumMeasurable Events MeasurableEvents a b).aemeasurable
      (Filter.Eventually.of_forall (AffineSumInInterval Events a b Ordered))
  have Bound := measure_le_le_exp_mul_mgf (Mean-d) TiltNonpositive IntegrableExp
  apply Bound.trans
  calc
    _ ≤ Real.exp (-Tilt*(Mean-d))*Real.exp (Tilt*Mean+Width*Tilt^2/8) :=
      mul_le_mul_of_nonneg_left
        (ZeroNegativeCorrelationHoeffdingMGF P Events MeasurableEvents Correlated a b Ordered Tilt TiltNonpositive)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      change -(-4*d/Width)*(Mean-d)+((-4*d/Width)*Mean+Width*(-4*d/Width)^2/8)= -2*d^2/Width
      field_simp
      ring

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory Set
noncomputable section

/-- An upper estimate of the actual mean gives the same Hoeffding upper bound. -/
theorem OneNegativeCorrelationHoeffdingUpperOfMeanBound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events)
    (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (MeanUpper d : ℝ)
    (MeanBound : (∑ i, (a i+(b i-a i)*P.real (Events i)))≤MeanUpper) (Nonnegative : 0≤d) :
    P.real {ω | MeanUpper+d≤∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)}≤
      Real.exp (-2*d^2/(∑ i, (b i-a i)^2)) := by
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (OneNegativeCorrelationHoeffdingUpper P Events MeasurableEvents Correlated a b Ordered d Nonnegative)
  intro ω Above
  exact le_trans (add_le_add MeanBound (le_refl d)) Above

theorem ZeroNegativeCorrelationHoeffdingLowerOfMeanBound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events)
    (a b : ι → ℝ) (Ordered : ∀ i, a i≤b i) (MeanLower d : ℝ)
    (MeanBound : MeanLower≤∑ i, (a i+(b i-a i)*P.real (Events i))) (Nonnegative : 0≤d) :
    P.real {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤MeanLower-d}≤
      Real.exp (-2*d^2/(∑ i, (b i-a i)^2)) := by
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (ZeroNegativeCorrelationHoeffdingLower P Events MeasurableEvents Correlated a b Ordered d Nonnegative)
  intro ω Below
  exact le_trans Below (sub_le_sub_right MeanBound d)

end
end ECTheoryLib.Probability
