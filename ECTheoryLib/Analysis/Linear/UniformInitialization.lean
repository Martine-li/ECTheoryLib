import ECTheoryLib.Problems.Linear
import ECTheoryLib.Algorithms.RLS.Initialization
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Ring

/-!
Actual uniform initialization, independent of selection or weight signs.
The product law and finite-coordinate integration are reused directly.
-/
namespace ECTheoryLib.Analysis.LinearInitialization
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

theorem UniformCoordinateIntegral {n : ℕ} (i : Fin n) (f : Bool → ℝ) :
    (∫ x : Bits n, f (x i) ∂(RLSInit n).toMeasure) = (f false + f true) / 2 := by
  rw [RLSInitProduct n, integral_comp_eval (measurable_of_finite f).aestronglyMeasurable]
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul, Fintype.sum_bool]
  ring

theorem UniformCoordinateOneProbability {n : ℕ} (i : Fin n) :
    (RLSInit n).toMeasure {x : Bits n | x i = true} = (2 : ENNReal)⁻¹ := by
  have CoordinateLaw : (RLSInit n).toMeasure.map (fun x : Bits n => x i) =
      (PMF.uniformOfFintype Bool).toMeasure := by
    rw [RLSInitProduct n]
    exact (measurePreserving_eval (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure) i).map_eq
  calc
    _ = ((RLSInit n).toMeasure.map (fun x : Bits n => x i)) {true} :=
      (Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton true)).symm
    _ = (PMF.uniformOfFintype Bool).toMeasure {true} := by rw [CoordinateLaw]
    _ = _ := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true), PMF.uniformOfFintype_apply]
      norm_num

/-- This expectation permits negative and zero weights, including the empty initial space. -/
theorem UniformLinearScoreExpectation {n : ℕ} (w : Fin n → ℝ) :
    (∫ x, Problems.Linear.Score w x ∂(RLSInit n).toMeasure) = (∑ i, w i) / 2 := by
  classical
  unfold Problems.Linear.Score
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  calc
    _ = ∑ i : Fin n, w i / 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using UniformCoordinateIntegral i (fun b => w i * (if b then (1 : ℝ) else 0))
    _ = _ := (Finset.sum_div _ _ _).symm

end
end ECTheoryLib.Analysis.LinearInitialization

