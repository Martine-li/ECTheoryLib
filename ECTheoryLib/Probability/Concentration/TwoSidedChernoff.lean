import ECTheoryLib.Probability.Concentration.Chernoff
import ECTheoryLib.Probability.Concentration.LowerChernoff

/-!
# Two-sided relative Chernoff concentration

Doerr Corollary 1.10.6 for finite independent unit-interval variables.
The closed event and the complete deviation interval [0,1] are retained.
Bounds may hold almost surely; zero mean and the empty family are allowed.
The proof combines the existing one-sided results with Mathlib's union bound.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Doerr Corollary 1.10.6, including threshold atoms and zero mean. -/
theorem UnitIndependentSumTwoSidedChernoff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (Independent : iIndepFun X P) (Bounded : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc 0 1)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    P.real {ω | d * (∫ w, ∑ i, X i w ∂P) ≤
      |(∑ i, X i ω) - (∫ w, ∑ i, X i w ∂P)|} ≤
      2 * Real.exp (-(d ^ 2) * (∫ w, ∑ i, X i w ∂P) / 3) := by
  let m := ∫ w, ∑ i, X i w ∂P
  have MeanNonnegative : 0 ≤ m := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_all_iff.mpr Bounded] with ω Bounds
    exact Finset.sum_nonneg (fun i _ => (Bounds i).1)
  have Events : {ω | d * m ≤ |(∑ i, X i ω) - m|} =
      {ω | (1 + d) * m ≤ ∑ i, X i ω} ∪
      {ω | (∑ i, X i ω) ≤ (1 - d) * m} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, le_abs]
    constructor
    · rintro (Upper | Lower)
      · left; linarith
      · right; linarith
    · rintro (Upper | Lower)
      · left; linarith
      · right; linarith
  change P.real {ω | d * m ≤ |(∑ i, X i ω) - m|} ≤ _
  rw [Events]
  have Upper := UnitIndependentSumChernoffUpperSmall P X MeasurableX Independent Bounded d InUnit
  have Lower := UnitIndependentSumChernoffLowerQuadratic P X MeasurableX Independent Bounded d InUnit
  have Exponents : Real.exp (-(d ^ 2 / 2) * m) ≤ Real.exp (-(d ^ 2) * m / 3) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg d) MeanNonnegative]
  calc
    _ ≤ P.real {ω | (1 + d) * m ≤ ∑ i, X i ω} +
        P.real {ω | (∑ i, X i ω) ≤ (1 - d) * m} := measureReal_union_le _ _
    _ ≤ Real.exp (-(d ^ 2) * m / 3) + Real.exp (-(d ^ 2 / 2) * m) :=
      add_le_add Upper Lower
    _ ≤ 2 * Real.exp (-(d ^ 2) * m / 3) := by linarith

end
end ECTheoryLib.Probability

