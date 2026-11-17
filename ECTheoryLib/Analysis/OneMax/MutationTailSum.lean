import ECTheoryLib.Probability.Moments.SignedTailSum
import ECTheoryLib.Operators.Mutation.IndependentBit
import ECTheoryLib.Problems.OneMax

namespace ECTheoryLib.Analysis.OneMaxMutation

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- Signed candidate progress has integral positive values. Subtraction is in
the reals, so deleterious offspring keep their negative increment. -/
private theorem MutationIncrementRange {n : Nat} (Parent Candidate : Bits n) :
    (OneMax Candidate : ℝ) - (OneMax Parent : ℝ) ≤ 0 ∨
      ∃ k : Nat, (OneMax Candidate : ℝ) - (OneMax Parent : ℝ) = (k : ℝ) := by
  rcases le_total (OneMax Candidate) (OneMax Parent) with Nonpositive | Nonnegative
  · exact Or.inl (sub_nonpos.mpr (by exact_mod_cast Nonpositive))
  · exact Or.inr ⟨OneMax Candidate - OneMax Parent, (Nat.cast_sub Nonnegative).symm⟩

/-- The actual independent-bit candidate law has a summable series of signed
OneMax increment tails, equal to the expected positive increment. -/
theorem MutationOneMaxIncrementHasSum {n : Nat} (Rate : ENNReal) (RateBound : Rate ≤ 1)
    (Parent : Bits n) :
    HasSum (fun k : Nat => (IndependentBitMutation Rate RateBound Parent).toMeasure.real
      {Candidate | ((k + 1 : Nat) : ℝ) ≤ (OneMax Candidate : ℝ) - (OneMax Parent : ℝ)})
      (∫ Candidate, max ((OneMax Candidate : ℝ) - (OneMax Parent : ℝ)) 0
        ∂(IndependentBitMutation Rate RateBound Parent).toMeasure) :=
  PositivePartHasSumNatUpperTail _ _ (measurable_of_finite _) Integrable.of_finite
    (ae_of_all _ (MutationIncrementRange Parent))

/-- Book 1.6.1 applied to the actual signed increment, before acceptance or selection. -/
theorem MutationOneMaxIncrementExpectationLeTailSum {n : Nat}
    (Rate : ENNReal) (RateBound : Rate ≤ 1) (Parent : Bits n) :
    (∫ Candidate, (OneMax Candidate : ℝ) - (OneMax Parent : ℝ)
      ∂(IndependentBitMutation Rate RateBound Parent).toMeasure) ≤
      ∑' k : Nat, (IndependentBitMutation Rate RateBound Parent).toMeasure.real
        {Candidate | ((k + 1 : Nat) : ℝ) ≤ (OneMax Candidate : ℝ) - (OneMax Parent : ℝ)} :=
  ExpectedRealLeNatUpperTailSum _ _ (measurable_of_finite _) Integrable.of_finite
    (ae_of_all _ (MutationIncrementRange Parent))

end
end ECTheoryLib.Analysis.OneMaxMutation

