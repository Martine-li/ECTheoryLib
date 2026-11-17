import ECTheoryLib.Analysis.BitMutationConcentration
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.Drift

/-!
# Actual EA lower concentration from zero OneMax fitness

The accepted-step law equals the mutation law because every offspring is
accepted at zero fitness. The lower tail cannot be transferred to arbitrary
selected parents: the optimum counterexample is checked separately.
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax
noncomputable section

/-- Every child is accepted at zero OneMax fitness, so the selected EA law
is exactly the mutation law. This identity is specific to these parents. -/
theorem StepFromZeroFitnessEqMutation {n : ℕ} (PositiveLength : 0<n)
    (Parent : Bits n) (ZeroFitness : OneMax Parent=0) :
    Step PositiveLength Parent=StandardBitMutation PositiveLength Parent := by
  unfold Step OnePlusOneEAStep
  have SelectionIdentity : (fun Candidate =>
      ElitistSelect (Problems.MaxNotWorse OneMax) Parent Candidate)=id := by
    funext Candidate
    apply ElitistSelectAccept
    change OneMax Parent≤OneMax Candidate
    rw [ZeroFitness]
    exact Nat.zero_le _
  rw [SelectionIdentity,PMF.map_id]

/-- The actual selected EA from a zero-fitness state has the sharp lower
tail for first-step progress. Selection dependence is removed by proof. -/
theorem StepFromZeroFitnessHammingLowerTail {n : ℕ} (PositiveLength : 0<n)
    (Parent : Bits n) (ZeroFitness : OneMax Parent=0)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Step PositiveLength Parent).toMeasure.real {Next | (Hamming Parent Next : ℝ)≤1-d}≤
      FiniteChernoffLowerBound n 1 d := by
  rw [StepFromZeroFitnessEqMutation PositiveLength Parent ZeroFitness]
  exact BitMutation.StandardMutationHammingFiniteChernoffLower PositiveLength Parent d InUnit

end
end ECTheoryLib.Analysis.EAOneMax
