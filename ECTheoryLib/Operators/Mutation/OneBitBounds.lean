import ECTheoryLib.Operators.Mutation.OneBit
import ECTheoryLib.Operators.Mutation.IndependentBitBounds

/-!
# Exact probabilities of one-bit offspring

Coordinate flips are injective as a function of the chosen coordinate. Mapping
the uniform coordinate PMF therefore gives mass `1/n` to each one-bit offspring.
The real-valued version is intended for local expected-progress inequalities.
-/
namespace ECTheoryLib
noncomputable section

/-- Every exact one-bit offspring has probability `1/n` under uniform one-bit mutation. -/
theorem RandomOneBitProbability {n : Nat} (hn : 0 < n) (x : Bits n) (i : Fin n) :
    RandomOneBitMutation hn x (OnebitMutation x i) = (n : ENNReal)⁻¹ := by
  classical
  unfold RandomOneBitMutation
  rw [PMF.map_apply]
  have SameOutcome (j : Fin n) : OnebitMutation x i = OnebitMutation x j ↔ j = i :=
    ⟨fun Equal => (OnebitMutationInjective x Equal).symm, fun Equal => by rw [Equal]⟩
  simp_rw [SameOutcome]
  rw [tsum_eq_single i]
  · exact if_pos rfl |>.trans (UniformBitIndexProbability n hn i)
  · intro j Different
    exact if_neg Different

/-- The finite point mass of each one-bit offspring, expressed as a real probability. -/
theorem RandomOneBitProbabilityReal {n : Nat} (hn : 0 < n) (x : Bits n) (i : Fin n) :
    (RandomOneBitMutation hn x (OnebitMutation x i)).toReal = 1 / (n : ℝ) := by
  rw [RandomOneBitProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

end
end ECTheoryLib
