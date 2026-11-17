import ECTheoryLib.Algorithms.RLS
import ECTheoryLib.Problems.Needle
import ECTheoryLib.Problems.OneMax
import ECTheoryLib.Problems.Comparison

/-!
# Actual RLS on Needle

The target is all ones and the potential counts zero bits. Weak selection
accepts every proposal from the nonoptimal plateau, including moves away
from the target. Only the optimum is absorbing.
-/

namespace ECTheoryLib.Analysis.RLSOnNeedle
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Standard Needle with its isolated optimum at the all-ones bit string. -/
abbrev Fitness {n : ℕ} : Bits n → ℕ := Problems.Needle (AllOnes n)

abbrev IsTarget {n : ℕ} (x : Bits n) : Prop := x = AllOnes n

abbrev Update {n : ℕ} (x : Bits n) (i : Fin n) : Bits n :=
  RLSUpdate (Problems.MaxNotWorse Fitness) x i

def Step {n : ℕ} (PositiveLength : 0 < n) : Transition (Bits n) :=
  RLSStep PositiveLength (Problems.MaxNotWorse Fitness)

/-- Distance to the isolated optimum, rather than the plateau-valued fitness. -/
def Potential {n : ℕ} (x : Bits n) : ℝ := (Problems.OneMax.ZeroCount x : ℝ)

theorem PotentialNonnegative {n : ℕ} (x : Bits n) : 0 ≤ Potential x :=
  Nat.cast_nonneg _

theorem PotentialEqZeroIffTarget {n : ℕ} (x : Bits n) : Potential x = 0 ↔ IsTarget x := by
  rw [Potential, Nat.cast_eq_zero, Problems.OneMax.ZeroCountEqZeroIffAllOnes]

theorem IsTargetIffOptimal {n : ℕ} (x : Bits n) :
    IsTarget x ↔ Problems.IsMaximizer Fitness x :=
  (Problems.Needle.IsOptimalIffEqTarget (AllOnes n) x).symm

/-- Weak elitism accepts every proposal on the nonoptimal plateau, including
neutral moves away from the optimum. -/
theorem UpdateAway {n : ℕ} (x : Bits n) (i : Fin n) (Away : ¬ IsTarget x) :
    Update x i = OnebitMutation x i := by
  have Accepted : Problems.MaxNotWorse Fitness (OnebitMutation x i) x := by
    change Problems.Needle (AllOnes n) x ≤ Problems.Needle (AllOnes n) (OnebitMutation x i)
    rw [Problems.Needle.AwayFromTarget (AllOnes n) x Away]
    exact Nat.zero_le _
  exact ElitistSelectAccept (Problems.MaxNotWorse Fitness) x (OnebitMutation x i) Accepted

/-- The optimum is absorbing under the actual acceptance rule. -/
theorem UpdateAtTarget {n : ℕ} (x : Bits n) (i : Fin n) (AtTarget : IsTarget x) :
    Update x i = x := by
  have Changed : OnebitMutation x i ≠ AllOnes n := by
    rw [← AtTarget]
    exact OnebitMutationChanges x i
  have Rejected : ¬ Problems.MaxNotWorse Fitness (OnebitMutation x i) x := by
    change ¬ Problems.Needle (AllOnes n) x ≤ Problems.Needle (AllOnes n) (OnebitMutation x i)
    rw [Problems.Needle.AwayFromTarget (AllOnes n) _ Changed, AtTarget,
      Problems.Needle.AtTarget]
    omega
  exact ElitistSelectReject (Problems.MaxNotWorse Fitness) x (OnebitMutation x i) Rejected

end
end ECTheoryLib.Analysis.RLSOnNeedle
