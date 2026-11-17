import ECTheoryLib.Operators.Mutation.IndependentBitCoupling
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Coordinate moments of actual independent bit mutation

Independent output indicators, their means, square integrability and variance
for every rate in [0,1]. These are candidate laws for a fixed parent, before
selection. The existing OneMaxMutation namespace is retained for compatibility;
none of the declarations depends on a fitness function.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- Actual independent mutation has independent real one-bit indicators. -/
theorem MutationOneCoordinatesIndependent {n : ℕ} (p : I) (Parent : Bits n) :
    iIndepFun (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure := by
  rw [← IndependentBitMutationProductLaw]
  exact iIndepFun_pi (fun _ => (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).aemeasurable)

/-- The probability of a one depends on the corresponding parent coordinate. -/
theorem MutationOneCoordinateExpectation {n : ℕ} (p : I) (Parent : Bits n) (i : Fin n) :
    (∫ y, (if y i then (1 : ℝ) else 0)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)=
      (MutationOneProbability p (Parent i) : ℝ) := by
  rw [← IndependentBitMutationProductLaw]
  have Map := (measurePreserving_eval
    (fun j : Fin n => bernoulliMeasure true false (MutationOneProbability p (Parent j))) i).map_eq
  have IntegralMap := integral_map_of_stronglyMeasurable (measurable_pi_apply i)
    (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).stronglyMeasurable
    (μ := Measure.pi (fun j => bernoulliMeasure true false (MutationOneProbability p (Parent j))))
  rw [Map,integral_bernoulliMeasure] at IntegralMap
  simpa only [Function.comp_apply,ite_true,Bool.false_eq_true,ite_false,smul_eq_mul,mul_one,mul_zero,add_zero]
    using IntegralMap.symm

theorem MutationOneCoordinateMemLp {n : ℕ} (p : I) (Parent : Bits n) (i : Fin n) :
    MemLp (fun y : Bits n => if y i then (1 : ℝ) else 0) 2
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure := by
  apply memLp_of_bounded (a := (0 : ℝ)) (b := 1) _ (measurable_of_finite _).aestronglyMeasurable
  exact ae_of_all _ (fun y => by cases y i <;> norm_num)

/-- Each mutated coordinate has variance p(1-p), whichever parent bit it starts from. -/
theorem MutationOneCoordinateVariance {n : ℕ} (p : I) (Parent : Bits n) (i : Fin n) :
    variance (fun y : Bits n => if y i then (1 : ℝ) else 0)
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure=
      (p : ℝ)*(1-(p : ℝ)) := by
  rw [variance_eq_sub (MutationOneCoordinateMemLp p Parent i)]
  change (∫ y, (if y i then (1 : ℝ) else 0)^2
    ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)-
    (∫ y, (if y i then (1 : ℝ) else 0)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)^2=_
  have Square (y : Bits n) : (if y i then (1 : ℝ) else 0)^2=(if y i then (1 : ℝ) else 0) := by
    cases y i <;> norm_num
  simp_rw [Square]
  rw [MutationOneCoordinateExpectation]
  cases Parent i <;> simp only [MutationOneProbability,ite_true,Bool.false_eq_true,
    ite_false,unitInterval.coe_symm_eq] <;> ring

end
end ECTheoryLib.Analysis.OneMaxMutation
