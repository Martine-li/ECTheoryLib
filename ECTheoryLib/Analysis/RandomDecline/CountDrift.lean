import ECTheoryLib.Analysis.RandomDecline.Model
import ECTheoryLib.Probability.Processes.FinitePotentialHistory

/-! Count drift and its exact conditional law on the actual natural history. -/
namespace ECTheoryLib.Analysis.RandomDecline
open MeasureTheory ECTheoryLib.Probability
noncomputable section

theorem CutoffUnclipped {N : ℕ} (a : ℝ) (s : Fin (N + 1))
    (Within : ⌊a * (s.val : ℝ)⌋₊ ≤ N) : Cutoff a s = ⌊a * (s.val : ℝ)⌋₊ :=
  min_eq_left Within

theorem CutoffClipped {N : ℕ} (a : ℝ) (s : Fin (N + 1))
    (Beyond : N ≤ ⌊a * (s.val : ℝ)⌋₊) : Cutoff a s = N :=
  min_eq_right Beyond

theorem CountDrift {N : ℕ} (a : ℝ) (s : Fin (N + 1)) :
    (∫ y, (s.val : ℝ) - (y.val : ℝ) ∂(Step a s).toMeasure) =
      (s.val : ℝ) - (Cutoff a s : ℝ) / 2 := by
  rw [integral_sub Integrable.of_finite Integrable.of_finite, StepMean]
  simp

theorem CountDriftLower {N : ℕ} {a : ℝ} (Nonnegative : 0 ≤ a) (s : Fin (N + 1)) :
    (1 - a / 2) * (s.val : ℝ) ≤
      ∫ y, (s.val : ℝ) - (y.val : ℝ) ∂(Step a s).toMeasure := by
  rw [CountDrift]
  nlinarith [CutoffRealLe Nonnegative s]

theorem SuccessProbabilityLower {N : ℕ} (a : ℝ) (s : Fin (N + 1)) :
    1 / ((N : ℝ) + 1) ≤ (Step a s).toMeasure.real {y | y.val = 0} := by
  rw [SuccessProbability]
  apply one_div_le_one_div_of_le (by positivity)
  have Bound : (Cutoff a s : ℝ) ≤ N := by exact_mod_cast CutoffLe a s
  linarith

theorem CountConditionalDrift {N : ℕ} (a : ℝ) (Initial : PMF (Fin (N + 1))) (t : ℕ) :
    (PathMeasure (Step a) Initial)[
      fun Path => ((Path t).val : ℝ) - ((Path (t + 1)).val : ℝ) |
      Filtration.piLE (X := fun _ : ℕ => Fin (N + 1)) t] =ᵐ[PathMeasure (Step a) Initial]
      (fun Path => ((Path t).val : ℝ) - (Cutoff a (Path t) : ℝ) / 2) := by
  classical
  filter_upwards [PathMeasureFinitePotentialConditionalDrift (Step a) Initial
    (fun s => (s.val : ℝ)) (Finset.univ.image (fun s : Fin (N + 1) => (s.val : ℝ)))
    (fun s => Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩) t] with Path Equal
  rw [Equal, CountDrift]

end
end ECTheoryLib.Analysis.RandomDecline

