import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationChernoff

/-!
# Upper threshold events of negatively correlated affine indicators

Coordinatewise upper thresholds preserve all-subset one-negative
correlation. A correlated closed-maximum event is then controlled by
actual second moments, allowing negative coordinates.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Taking a coordinatewise upper-threshold event of ordered affine
indicators preserves all-subset one-negative correlation. -/
theorem OneNegativeCorrelationAffineThresholds {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Events : ι → Set Ω)
    (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b c : ι → ℝ) (Ordered : ∀ i, a i≤b i) :
    OneNegativelyCorrelated P
      (fun i => {ω | c i≤a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω}) := by
  classical
  let A := fun i => if c i≤a i then (1 : ℝ) else 0
  let B := fun i => if c i≤b i then (1 : ℝ) else 0
  let F := fun i => {ω | c i≤a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω}
  have NonnegativeA (i : ι) : 0≤A i := by dsimp [A]; split_ifs <;> norm_num
  have OrderedAB (i : ι) : A i≤B i := by
    dsimp only [A,B]
    by_cases First : c i≤a i
    · simp [First,First.trans (Ordered i)]
    · simp [First]
      split_ifs <;> norm_num
  have Pointwise (i : ι) (ω : Ω) :
      A i+(B i-A i)*(Events i).indicator (fun _ => (1 : ℝ)) ω=
        (F i).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases Inside : ω∈Events i
    · simp [A,B,F,indicator_apply,Inside]
    · simp [A,B,F,indicator_apply,Inside]
  have MeasurableF (i : ι) : MeasurableSet (F i) :=
    measurableSet_le measurable_const (AffineIndicatorMeasurable _ (MeasurableEvents i) _ _)
  have Marginal (i : ι) : A i+(B i-A i)*P.real (Events i)=P.real (F i) := by
    rw [← AffineIndicatorIntegral P _ (MeasurableEvents i)]
    simp_rw [Pointwise]
    rw [integral_indicator_const _ (MeasurableF i)]
    simp only [smul_eq_mul,mul_one]
  intro S
  have Bound := OneNegativeCorrelationAffineProduct P Events MeasurableEvents Correlated
    A (fun i => B i-A i) NonnegativeA (fun i => sub_nonneg.mpr (OrderedAB i)) S
  simp_rw [Pointwise,Marginal] at Bound
  rw [EventIndicatorProductIntegral P F MeasurableF S] at Bound
  exact Bound

/-- The closed maximum event is bounded by second moments under
negative correlation of the actual coordinate threshold events. -/
theorem SumEndpointOfSecondMomentsOfCorrelation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (PositiveLength : 0<n)
    (Y : Fin n → Ω → ℝ) (SquareIntegrable : ∀ i, MemLp (Y i) 2 P)
    (Correlated : OneNegativelyCorrelated P (fun i => Y i ⁻¹' Ici 1))
    (Upper : ∀ i, ∀ᵐ ω ∂P, Y i ω≤1) :
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
  rw [show P.real {ω | (n : ℝ)≤∑ i, Y i ω}=
      P.real (⋂ i∈(Finset.univ : Finset (Fin n)), Y i ⁻¹' Ici 1) by
        exact congrArg ENNReal.toReal (measure_congr EventEq)]
  apply (Correlated Finset.univ).trans
  calc
    _≤∏ i, ∫ ω, (Y i ω)^2 ∂P :=
      Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun i _ => IndividualBound i)
    _≤_ := NonnegativeProductLeMeanPow PositiveLength _
      (fun i => integral_nonneg (fun ω => sq_nonneg (Y i ω)))

end
end ECTheoryLib.Probability
