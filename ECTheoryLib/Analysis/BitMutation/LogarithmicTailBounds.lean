import ECTheoryLib.Probability.Concentration.ChernoffMeanUpper
import ECTheoryLib.Analysis.BitMutationConcentration

/-! Logarithmic Hamming-distance tails for actual mutation, following printed page 44 of Doerr. -/
namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax
open scoped unitInterval
noncomputable section

/-- The estimated small-deviation bound for actual mutation distance, with no
probability or independence premise left to the caller. -/
theorem MutationHammingChernoffSmallOfMeanLe {n : ℕ} (p : I) (Parent : Bits n)
    (U : ℝ) (MeanUpper : (n : ℝ) * (p : ℝ) ≤ U)
    (d : ℝ) (InUnit : d ∈ Icc 0 1) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (1 + d) * U ≤ (Hamming Parent y : ℝ)} ≤ Real.exp (-(d ^ 2) * U / 3) := by
  let P := (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
    (MutationProbabilityBound p) Parent).toMeasure
  let X := fun (i : Fin n) (y : Bits n) => if y i = Parent i then (0 : ℝ) else 1
  have Independent : iIndepFun X P := by
    change iIndepFun X (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) Parent).toMeasure
    rw [← IndependentBitMutationProductLaw]
    exact iIndepFun_pi (fun i =>
      (measurable_of_finite (fun b : Bool => if b = Parent i then (0 : ℝ) else 1)).aemeasurable)
  have SumHamming (y : Bits n) : (∑ i, X i y) = (Hamming Parent y : ℝ) := by
    simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, X]
  have Bound := UnitIndependentSumChernoffUpperSmallOfMeanLe P X
    (fun _ => (measurable_of_finite _).aemeasurable) Independent
    (fun _ => ae_of_all _ (fun y => by dsimp only [X]; split_ifs <;> norm_num))
    U (by simpa only [SumHamming, P, MutationHammingExpectation] using MeanUpper) d InUnit
  simpa only [SumHamming] using Bound

/-- The source's logarithmic threshold bound. Any real c is allowed when the
explicit mean estimate holds; this also retains the n=1, zero-rate boundary. -/
theorem MutationHammingLogarithmicTail {n : ℕ} (PositiveLength : 0 < n)
    (p : I) (Parent : Bits n) (c : ℝ)
    (MeanUpper : (n : ℝ) * (p : ℝ) ≤ c * Real.log (n : ℝ)) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | 2 * c * Real.log (n : ℝ) ≤ (Hamming Parent y : ℝ)} ≤ (n : ℝ) ^ (-c / 3) := by
  have Bound := MutationHammingChernoffSmallOfMeanLe p Parent (c * Real.log (n : ℝ))
    MeanUpper 1 (by norm_num)
  have Threshold : (1 + (1 : ℝ)) * (c * Real.log (n : ℝ)) = 2 * c * Real.log (n : ℝ) := by ring
  rw [Threshold] at Bound
  apply Bound.trans_eq
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr PositiveLength)]
  congr 1
  ring

/-- Printed page 44 at the legal mutation rate alpha/n. Rate legality and the
positive length required by this parameterization are explicit. -/
theorem MutationHammingLogarithmicTailAlpha {n : ℕ} (PositiveLength : 0 < n)
    (Parent : Bits n) (α c : ℝ) (AlphaNonnegative : 0 ≤ α)
    (AlphaAtMostLength : α ≤ (n : ℝ)) (MeanUpper : α ≤ c * Real.log (n : ℝ)) :
    let p : I := ⟨α / (n : ℝ),
      ⟨div_nonneg AlphaNonnegative (Nat.cast_nonneg n),
        (div_le_one (Nat.cast_pos.mpr PositiveLength)).mpr AlphaAtMostLength⟩⟩
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | 2 * c * Real.log (n : ℝ) ≤ (Hamming Parent y : ℝ)} ≤ (n : ℝ) ^ (-c / 3) := by
  let p : I := ⟨α / (n : ℝ),
    ⟨div_nonneg AlphaNonnegative (Nat.cast_nonneg n),
      (div_le_one (Nat.cast_pos.mpr PositiveLength)).mpr AlphaAtMostLength⟩⟩
  have Mean : (n : ℝ) * (p : ℝ) = α := by
    change (n : ℝ) * (α / (n : ℝ)) = α
    field_simp [show (n : ℝ) ≠ 0 from (Nat.cast_pos.mpr PositiveLength).ne']
  exact MutationHammingLogarithmicTail PositiveLength p Parent c (by simpa only [Mean] using MeanUpper)

/-- The actual standard mutation used by the algorithms has unit mean. -/
theorem StandardMutationHammingLogarithmicTail {n : ℕ} (PositiveLength : 0 < n)
    (Parent : Bits n) (c : ℝ) (MeanUpper : 1 ≤ c * Real.log (n : ℝ)) :
    (StandardBitMutation PositiveLength Parent).toMeasure.real
      {y | 2 * c * Real.log (n : ℝ) ≤ (Hamming Parent y : ℝ)} ≤ (n : ℝ) ^ (-c / 3) := by
  have PositiveReal : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1 / (n : ℝ), ⟨by positivity,
    (div_le_one PositiveReal).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1 / (n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveReal, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  have Mean : (n : ℝ) * (p : ℝ) = 1 := by
    change (n : ℝ) * (1 / (n : ℝ)) = 1
    exact mul_one_div_cancel PositiveReal.ne'
  have Bound := MutationHammingLogarithmicTail PositiveLength p Parent c (by simpa only [Mean] using MeanUpper)
  simpa only [Rate, StandardBitMutation] using Bound

end
end ECTheoryLib.Analysis.BitMutation

