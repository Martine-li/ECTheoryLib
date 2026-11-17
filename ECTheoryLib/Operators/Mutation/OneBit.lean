import ECTheoryLib.Operators.Mutation.BitFlip
import Mathlib.Probability.Distributions.Uniform

namespace ECTheoryLib

/-!
# Uniform one-bit mutation

For positive length, choose one coordinate uniformly and flip it. Every exact
one-bit offspring has probability `1/n`. These are mathematical PMFs; no
executable random-number generator is specified.
-/
noncomputable section

/-- Uniform choice of one of the `n` coordinates; positive length excludes an empty choice. -/
def UniformBitIndex (n : Nat) (PositiveLength : 0 < n) : PMF (Fin n) := by
  
  let FirstIndex : Fin n := ⟨0, PositiveLength⟩
  
  letI : Nonempty (Fin n) := by
    exact ⟨FirstIndex⟩
  exact PMF.uniformOfFintype (Fin n)

/-- Each coordinate has probability `1/n`. -/
@[simp] theorem UniformBitIndexProbability (n : Nat) (PositiveLength : 0 < n)
    (i : Fin n) : UniformBitIndex n PositiveLength i = (n : ENNReal)⁻¹ := by
  
  let : Nonempty (Fin n) := by
    exact ⟨i⟩
  unfold UniformBitIndex
  rw [PMF.uniformOfFintype_apply]
  rw [Fintype.card_fin]

/-- The offspring distribution obtained by flipping one uniformly chosen coordinate. -/
def RandomOneBitMutation {n : Nat} (PositiveLength : 0 < n)
    (x : Bits n) : PMF (Bits n) :=
  
  (UniformBitIndex n PositiveLength).map (fun i => OnebitMutation x i)

end
end ECTheoryLib
