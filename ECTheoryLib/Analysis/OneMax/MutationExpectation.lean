import ECTheoryLib.Operators.Mutation.IndependentBitCoupling
import ECTheoryLib.Problems.OneMax
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Expected zero count after independent bit mutation

The actual coordinate-product law gives np+(1-2p)V for all rates in [0,1].
No survivor-selection rule or runtime theorem is used here.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

theorem MutationZeroBitIntegral (p : Set.Icc (0 : ℝ) 1) (Parent : Bool) :
    (∫ b, (if b then (0 : ℝ) else 1)
      ∂bernoulliMeasure true false (MutationOneProbability p Parent)) =
      (p : ℝ)+(1-2*(p : ℝ))*(if Parent then 0 else 1) := by
  rw [integral_bernoulliMeasure]
  cases Parent with
  | false =>
    simp only [MutationOneProbability, Bool.false_eq_true, ite_false, ite_true,
      smul_eq_mul, mul_zero, mul_one, zero_add]
    ring
  | true =>
    simp only [MutationOneProbability, ite_true, Bool.false_eq_true, ite_false,
      smul_eq_mul, mul_zero, mul_one, zero_add, unitInterval.coe_symm_eq]
    ring

/-- Expected zero count under the actual independent-bit mutation law,
including rates zero and one and the empty search space. -/
theorem MutationZeroCountExpectation {n : ℕ} (p : Set.Icc (0 : ℝ) 1) (Parent : Bits n) :
    (∫ y, (Problems.OneMax.ZeroCount y : ℝ)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure) =
      (n : ℝ)*(p : ℝ)+(1-2*(p : ℝ))*(Problems.OneMax.ZeroCount Parent : ℝ) := by
  classical
  rw [← IndependentBitMutationProductLaw p Parent]
  let P := Measure.pi (fun i => bernoulliMeasure true false (MutationOneProbability p (Parent i)))
  have CoordinateMean (i : Fin n) :
      (∫ y, (if y i then (0 : ℝ) else 1) ∂P) =
        (p : ℝ)+(1-2*(p : ℝ))*(if Parent i then 0 else 1) := by
    have Map := (measurePreserving_eval
      (fun j : Fin n => bernoulliMeasure true false (MutationOneProbability p (Parent j))) i).map_eq
    have IntegralMap := integral_map_of_stronglyMeasurable (measurable_pi_apply i)
      (measurable_of_finite (fun b : Bool => if b then (0 : ℝ) else 1)).stronglyMeasurable (μ := P)
    rw [Map] at IntegralMap
    rw [← IntegralMap, MutationZeroBitIntegral]
  have SumZeroCount (y : Bits n) : (Problems.OneMax.ZeroCount y : ℝ) =
      ∑ i : Fin n, (if y i then (0 : ℝ) else 1) := (Problems.OneMax.ZeroBitCountAsReal y).symm
  simp_rw [SumZeroCount]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  change (∑ i : Fin n, ∫ y, (if y i then (0 : ℝ) else 1) ∂P) = _
  simp_rw [CoordinateMean]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The standard mutation rate gives one expected added zero minus the
contribution of currently zero coordinates. -/
theorem StandardMutationZeroCountExpectation {n : ℕ} (PositiveLength : 0<n) (Parent : Bits n) :
    (∫ y, (Problems.OneMax.ZeroCount y : ℝ) ∂(StandardBitMutation PositiveLength Parent).toMeasure) =
      1+(1-2/(n : ℝ))*(Problems.OneMax.ZeroCount Parent : ℝ) := by
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  let p : Set.Icc (0 : ℝ) 1 := ⟨1/(n : ℝ), ⟨by positivity,
    (div_le_one PositiveN).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ)=(n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ))=(n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveN, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  have Bound := MutationZeroCountExpectation p Parent
  simp only [Rate] at Bound
  change (∫ y, (Problems.OneMax.ZeroCount y : ℝ) ∂(StandardBitMutation PositiveLength Parent).toMeasure) =
    (n : ℝ)*(1/(n : ℝ))+(1-2*(1/(n : ℝ)))*(Problems.OneMax.ZeroCount Parent : ℝ) at Bound
  rw [mul_one_div_cancel PositiveN.ne'] at Bound
  convert Bound using 1
  ring

end
end ECTheoryLib.Analysis.OneMaxMutation
