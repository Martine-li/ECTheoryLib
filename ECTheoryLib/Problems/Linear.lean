import ECTheoryLib.Problems.OneMax

/-!
# Real linear objectives on bit strings

Arbitrary signed weights, including zeros. Unit weights recover OneMax.
This objective is independent of mutation, selection and runtime semantics.
-/

namespace ECTheoryLib.Problems.Linear
open scoped BigOperators
noncomputable section

/-- A real linear objective on bit strings. Weights may be negative or zero. -/
def Score {n : ℕ} (Weights : Fin n → ℝ) (x : Bits n) : ℝ :=
  ∑ i, Weights i*(if x i then 1 else 0)

theorem ScoreZeroWeights {n : ℕ} (x : Bits n) : Score (fun _ => 0) x=0 := by simp [Score]
theorem ScoreAllZeros {n : ℕ} (Weights : Fin n → ℝ) : Score Weights (fun _ => false)=0 := by
  simp [Score]
theorem ScoreAllOnes {n : ℕ} (Weights : Fin n → ℝ) : Score Weights (AllOnes n)=∑ i, Weights i := by
  simp [Score,AllOnes]
theorem ScoreUnitWeights {n : ℕ} (x : Bits n) : Score (fun _ => 1) x=(OneMax x : ℝ) := by
  simp [Score,OneMax]

end
end ECTheoryLib.Problems.Linear
