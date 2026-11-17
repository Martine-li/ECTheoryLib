import ECTheoryLib.Operators.Mutation.FixedSize
import ECTheoryLib.Algorithms.RLS

/-!
# Fixed-size local search

One actual proposal/selection iteration with k distinct bit flips. Generic
process infrastructure supplies runs and paths from the kernel. For k=1
the complete transition PMF equals RLSStep, including rejection mass.
-/

namespace ECTheoryLib
noncomputable section

/-- One iteration of k-bit local search: uniformly choose k distinct positions,
flip all of them, then keep the candidate exactly when NotWorse accepts it.
Time counts one proposal/selection iteration. Generic Evolve and PathMeasure
provide the multi-step and trajectory laws from this kernel. -/
def FixedSizeRLSStep {n k : ℕ} (Admissible : k≤n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse] (Parent : Bits n) : PMF (Bits n) :=
  (FixedSizeBitMutation Admissible Parent).map (ElitistSelect NotWorse Parent)

/-- Rejection returns the parent, so it cannot increase observed displacement. -/
theorem ElitistObservedBitDifferenceLe {n m : ℕ} (Observed : Fin m → Fin n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse] (Parent Child : Bits n) :
    ObservedBitDifference Observed Parent (ElitistSelect NotWorse Parent Child)≤
      ObservedBitDifference Observed Parent Child := by
  unfold ElitistSelect
  split_ifs
  · exact le_rfl
  · rw [ObservedBitDifferenceSelf]
    exact Nat.zero_le _

end
end ECTheoryLib

namespace ECTheoryLib
noncomputable section

/-- Equality of complete transition PMFs, including accumulated rejection mass. -/
theorem FixedSizeRLSStepOne {n : ℕ} (PositiveLength : 0<n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse] (Parent : Bits n) :
    FixedSizeRLSStep PositiveLength NotWorse Parent=RLSStep PositiveLength NotWorse Parent := by
  simp only [FixedSizeRLSStep,RLSStep,FixedSizeBitMutationOne]

end
end ECTheoryLib
