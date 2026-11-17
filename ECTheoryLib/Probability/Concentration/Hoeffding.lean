import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hoeffding bounds through Mathlib sub-Gaussian tools

Doerr Theorems 1.10.7 and 1.10.9 are exposed with interval bounds and
ordinary expectations. Mathlib supplies the centered bounded-variable MGF
lemma and independent-sum tail theorem. The local proof verifies the
centering, integrability, independence and squared-width normalization.

Bounds may hold almost surely; variables need not be identically distributed
or nonnegative. Both tails include the threshold atom. Zero deviation and
empty families are permitted. Real division by zero makes the exponential
bound equal to one when all widths vanish; a separate theorem gives the
exact zero probability of a positive deviation in that case.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Doerr Theorem 1.10.9: upper deviation of a sum with individual interval bounds. -/
theorem BoundedIndependentSumUpperTail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (a b : ι → ℝ) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (a i) (b i))
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d ≤ ∑ i, X i ω} ≤
      Real.exp (-2*d^2/(∑ i, (b i-a i)^2)) := by
  let Z := fun i ω => X i ω-∫ w, X i w ∂P
  let c := fun i => ((‖b i-a i‖₊/2)^2 : NNReal)
  have IndependentZ : iIndepFun Z P := Independent.comp
    (fun i x => x-∫ w, X i w ∂P) (fun _ => measurable_id.sub_const _)
  have Subgaussian (i : ι) : HasSubgaussianMGF (Z i) (c i) P :=
    hasSubgaussianMGF_of_mem_Icc (MeasurableX i) (Bounded i)
  have Bound := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun IndependentZ
    (s := Finset.univ) (fun i _ => Subgaussian i) Nonnegative
  have MeanSum : (∫ w, ∑ i, X i w ∂P) = ∑ i, ∫ w, X i w ∂P := by
    apply integral_finsetSum
    intro i _
    exact Integrable.of_mem_Icc (a i) (b i) (MeasurableX i) (Bounded i)
  have Event : {ω | d ≤ ∑ i, Z i ω} =
      {ω | (∫ w, ∑ i, X i w ∂P)+d ≤ ∑ i, X i ω} := by
    ext ω
    simp only [mem_ofPred_eq, Z, Finset.sum_sub_distrib, MeanSum]
    constructor
    · intro Above
      linarith
    · intro Above
      linarith
  have Constant (i : ι) : (c i : ℝ) = (b i-a i)^2/4 := by
    simp only [c, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs]
    rw [div_pow, sq_abs]
    ring
  have Parameter : (2 : ℝ)*(∑ i, c i : NNReal) = (∑ i, (b i-a i)^2)/2 := by
    rw [NNReal.coe_sum]
    simp_rw [Constant]
    rw [← Finset.sum_div]
    ring
  rw [Event, Parameter] at Bound
  have Exponent : -d^2/((∑ i, (b i-a i)^2)/2) = -2*d^2/(∑ i, (b i-a i)^2) := by
    rw [div_div_eq_mul_div]
    ring
  rw [Exponent] at Bound
  exact Bound

/-- The lower Hoeffding tail follows by negating the same independent family. -/
theorem BoundedIndependentSumLowerTail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (a b : ι → ℝ) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (a i) (b i))
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P)-d} ≤
      Real.exp (-2*d^2/(∑ i, (b i-a i)^2)) := by
  have IndependentNeg : iIndepFun (fun i ω => -X i ω) P :=
    Independent.comp (fun _ x => -x) (fun _ => measurable_neg)
  have BoundedNeg (i : ι) : ∀ᵐ ω ∂P, -X i ω ∈ Icc (-b i) (-a i) := by
    filter_upwards [Bounded i] with ω Bounds
    exact ⟨neg_le_neg Bounds.2, neg_le_neg Bounds.1⟩
  have Bound := BoundedIndependentSumUpperTail P (fun i ω => -X i ω)
    (fun i => (MeasurableX i).neg) IndependentNeg (fun i => -b i) (fun i => -a i) BoundedNeg d Nonnegative
  have Event : {ω | (∫ w, ∑ i, -X i w ∂P)+d ≤ ∑ i, -X i ω} =
      {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P)-d} := by
    simp only [Finset.sum_neg_distrib, integral_neg]
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · intro Below
      linarith
    · intro Below
      linarith
  have Width (i : ι) : (-a i- -b i)^2 = (b i-a i)^2 := by ring
  rw [Event] at Bound
  simp only [Width] at Bound
  exact Bound

/-- Zero-width intervals give zero probability for positive deviations; independence is unnecessary. -/
theorem ZeroWidthSumDeviationProbability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (a : ι → ℝ)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (a i) (a i))
    (d : ℝ) (Positive : 0 < d) :
    P {ω | d ≤ |(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)|} = 0 := by
  have SumConstant : (fun ω => ∑ i, X i ω) =ᵐ[P] (fun _ => ∑ i, a i) := by
    filter_upwards [ae_all_iff.mpr Bounded] with ω AllBounds
    apply Finset.sum_congr rfl
    intro i _
    exact le_antisymm (AllBounds i).2 (AllBounds i).1
  have Mean : (∫ w, ∑ i, X i w ∂P) = ∑ i, a i := by
    rw [integral_congr_ae SumConstant, integral_const, probReal_univ, one_smul]
  rw [Mean]
  have Excluded : ∀ᵐ ω ∂P, ¬d ≤ |(∑ i, X i ω)-(∑ i, a i)| := by
    filter_upwards [SumConstant] with ω Constant
    rw [Constant, sub_self, abs_zero]
    exact not_le_of_gt Positive
  simpa only [not_not] using ae_iff.mp Excluded

/-- Theorem 1.10.7, upper tail for independent variables in the unit interval. -/
theorem UnitIndependentSumUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d ≤ ∑ i, X i ω} ≤
      Real.exp (-2*d^2/(n : ℝ)) := by
  have Bound := BoundedIndependentSumUpperTail P X MeasurableX Independent
    (fun _ => 0) (fun _ => 1) Bounded d Nonnegative
  simpa only [sub_zero, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using Bound

/-- Theorem 1.10.7, lower tail for independent variables in the unit interval. -/
theorem UnitIndependentSumLowerTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P)-d} ≤
      Real.exp (-2*d^2/(n : ℝ)) := by
  have Bound := BoundedIndependentSumLowerTail P X MeasurableX Independent
    (fun _ => 0) (fun _ => 1) Bounded d Nonnegative
  simpa only [sub_zero, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using Bound

/-- The union of the two closed tails controls absolute deviations. -/
theorem UnitIndependentSumDeviation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1) (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | d ≤ |(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)|} ≤
      2*Real.exp (-2*d^2/(n : ℝ)) := by
  have Upper := UnitIndependentSumUpperTail P n X MeasurableX Independent Bounded d Nonnegative
  have Lower := UnitIndependentSumLowerTail P n X MeasurableX Independent Bounded d Nonnegative
  have Event : {ω | d ≤ |(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)|} =
      {ω | (∫ w, ∑ i, X i w ∂P)+d ≤ ∑ i, X i ω} ∪
        {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P)-d} := by
    ext ω
    simp only [mem_union, mem_ofPred_eq, le_abs]
    constructor
    · intro Either
      rcases Either with Above | Below
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · intro Either
      rcases Either with Above | Below
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  rw [Event]
  have Union := measureReal_union_le (μ := P)
    {ω | (∫ w, ∑ i, X i w ∂P)+d ≤ ∑ i, X i ω}
    {ω | (∑ i, X i ω) ≤ (∫ w, ∑ i, X i w ∂P)-d}
  linarith

end
end ECTheoryLib.Probability


/-! Hoeffding upper and lower tails with estimates for the actual mean. -/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The interval upper Hoeffding bound remains valid at an estimated mean.
The variables and estimate may be negative. -/
theorem BoundedIndependentSumUpperTailOfMeanLe {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (a b : ι → ℝ) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (a i) (b i))
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | U + d ≤ ∑ i, X i ω} ≤
      Real.exp (-2 * d ^ 2 / (∑ i, (b i - a i) ^ 2)) := by
  apply le_trans (measureReal_mono ?_)
    (BoundedIndependentSumUpperTail P X MeasurableX Independent a b Bounded d Nonnegative)
  intro ω Above
  exact (add_le_add MeanUpper (le_refl d)).trans Above

/-- The interval lower Hoeffding bound remains valid at an estimated mean.
This uses the opposite estimate direction and the same nonnegative deviation. -/
theorem BoundedIndependentSumLowerTailOfLeMean {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (a b : ι → ℝ) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (a i) (b i))
    (L : ℝ) (MeanLower : L ≤ (∫ ω, ∑ i, X i ω ∂P))
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ L - d} ≤
      Real.exp (-2 * d ^ 2 / (∑ i, (b i - a i) ^ 2)) := by
  apply le_trans (measureReal_mono ?_)
    (BoundedIndependentSumLowerTail P X MeasurableX Independent a b Bounded d Nonnegative)
  intro ω Below
  exact Below.trans (sub_le_sub_right MeanLower d)

/-- Unit-interval specialization, including n=0 and zero deviation. -/
theorem UnitIndependentSumUpperTailOfMeanLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (U : ℝ) (MeanUpper : (∫ ω, ∑ i, X i ω ∂P) ≤ U)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | U + d ≤ ∑ i, X i ω} ≤ Real.exp (-2 * d ^ 2 / (n : ℝ)) := by
  have Bound := BoundedIndependentSumUpperTailOfMeanLe P X MeasurableX Independent
    (fun _ => 0) (fun _ => 1) Bounded U MeanUpper d Nonnegative
  simpa only [sub_zero, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using Bound

/-- Unit-interval lower specialization, including negative lower estimates. -/
theorem UnitIndependentSumLowerTailOfLeMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (L : ℝ) (MeanLower : L ≤ (∫ ω, ∑ i, X i ω ∂P))
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    P.real {ω | (∑ i, X i ω) ≤ L - d} ≤ Real.exp (-2 * d ^ 2 / (n : ℝ)) := by
  have Bound := BoundedIndependentSumLowerTailOfLeMean P X MeasurableX Independent
    (fun _ => 0) (fun _ => 1) Bounded L MeanLower d Nonnegative
  simpa only [sub_zero, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using Bound

end
end ECTheoryLib.Probability

