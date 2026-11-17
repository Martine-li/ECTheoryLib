import ECTheoryLib.Analysis.Linear.RLS.PositiveWeights
import ECTheoryLib.Probability.Processes.FinitePotentialHistory
import ECTheoryLib.Probability.Processes.PathDrift
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Ring

/-!
# Actual weighted fitness drift of positive-linear one-bit RLS

The local integral follows from the uniformly selected coordinate and its
actual accepted decrement. Existing trajectory laws lift it to complete
history and positive-probability potential levels for arbitrary initial PMFs.
No runtime theorem is used to establish drift.
-/
namespace ECTheoryLib.Analysis.RLSLinear
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open ECTheoryLib.Problems.TargetOneMax
open scoped BigOperators
noncomputable section

theorem FitnessDrift {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (x : Bits n) :
    (∫ Next, Score w x - Score w Next ∂(Step PositiveLength w x).toMeasure) =
      Score w x / (n : ℝ) := by
  rw [Step, RLSStepEqUniformUpdate]
  rw [← PMF.toMeasure_map (RLSUpdate (Problems.MinNotWorse (Score w)) x)
    (UniformBitIndex n PositiveLength) (measurable_of_finite _)]
  rw [integral_map_of_stronglyMeasurable (measurable_of_finite _)
    (measurable_of_finite (fun Next : Bits n => Score w x - Score w Next)).stronglyMeasurable]
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  have UniformWeight (i : Fin n) :
      ((UniformBitIndex n PositiveLength) i).toReal = 1 / (n : ℝ) := by
    rw [UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact (one_div (n : ℝ)).symm
  have Average :
      (∑ i : Fin n, ((UniformBitIndex n PositiveLength) i).toReal *
        (Score w x - Score w (RLSUpdate (Problems.MinNotWorse (Score w)) x i))) =
      ∑ i : Fin n, (1 / (n : ℝ)) * (if x i then w i else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [UniformWeight, UpdateScoreDecrease w Positive x i]
  have WeightedOnes : (∑ i : Fin n, if x i then w i else 0) = Score w x := by
    unfold Score
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp
  rw [Average, ← Finset.mul_sum, WeightedOnes]
  ring

/-- The conditioning sigma algebra is the full natural history. -/
theorem FitnessConditionalDrift {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n)) (t : ℕ) :
    (PathMeasure (Step PositiveLength w) Initial)[
      fun Path => Score w (Path t) - Score w (Path (t + 1)) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) t] =ᵐ[PathMeasure (Step PositiveLength w) Initial]
      (fun Path => Score w (Path t) / (n : ℝ)) := by
  classical
  filter_upwards [PathMeasureFinitePotentialConditionalDrift (Step PositiveLength w)
    Initial (Score w) (Finset.univ.image (Score w))
    (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) t] with Path Equal
  rw [Equal, FitnessDrift PositiveLength w Positive]

theorem FitnessStateDrift {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n)) (t : ℕ) (s : ℝ)
    (EventPositive : 0 < (PathMeasure (Step PositiveLength w) Initial)
      (StateEvent (fun t Path => Score w (Path t)) t s)) :
    StateDrift (PathMeasure (Step PositiveLength w) Initial)
      (fun t Path => Score w (Path t)) t s = s / (n : ℝ) := by
  exact PathMeasureStateDrift (Step PositiveLength w) Initial (Score w)
    (fun s => s / (n : ℝ)) (FitnessDrift PositiveLength w Positive) t s EventPositive

/-- Actual zero-score states stay zero under the selected one-bit kernel. -/
theorem StepPreservesScoreZero {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength w x).toMeasure, Score w x = 0 → Score w y = 0 := by
  rw [StepEqHamming PositiveLength w Positive]
  filter_upwards [RLSHamming.StepPreservesZeroHamming PositiveLength (fun _ => false) x]
    with y Preserved
  intro Zero
  apply (ScoreZeroIff w Positive y).mpr
  apply (HammingEqZeroIffEq (fun _ => false) y).mp
  apply Preserved
  exact (HammingEqZeroIffEq (fun _ => false) x).mpr ((ScoreZeroIff w Positive x).mp Zero)

end
end ECTheoryLib.Analysis.RLSLinear

