import ECTheoryLib.Analysis.Jump.OnePlusOneEA.PhaseGeometry
import ECTheoryLib.Probability.HittingTimes.LevelHittingTime
import ECTheoryLib.Probability.HittingTimes.Expectation

/-!
# Actual Jump phase times and their expectation identity

The first phase ends at first entry into the plateau-or-optimum region. The
remaining duration is measured on the same trajectory. This gives an exact
nonnegative expectation decomposition for arbitrary initial laws, without a
restart assumption or independence of phases. No separate distribution law
for the second phase is assumed. All expectations retain infinity.
-/

namespace ECTheoryLib.Analysis.EAJump
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section


/-- Time after first entry into the plateau-or-optimum region; zero if that region is never reached. -/
def PostPlateauDuration {n : ℕ} (k : ℕ) (Path : ℕ → Bits n) : WithTop ℕ :=
  FirstHittingTime (fun x => x = AllOnes n) Path - FirstHittingTime (Region k) Path

/-- The unique optimum belongs to the phase-boundary region. -/
theorem OptimumInRegion {n : ℕ} (k : ℕ) (x : Bits n) (AtGoal : x = AllOnes n) : Region k x := by
  rw [AtGoal]
  unfold Region
  rw [Problems.Jump.JumpAllOnes]
  exact Nat.le_add_right n k

/-- Pointwise decomposition for any trajectory, including skipped phases and nontermination. -/
theorem RuntimePhaseTimeDecomposition {n : ℕ} (k : ℕ) (Path : ℕ → Bits n) :
    FirstHittingTime (Region k) Path + PostPlateauDuration k Path =
      FirstHittingTime (fun x => x = AllOnes n) Path := by
  exact NestedGoalTimeDecomposition (Region k) (fun x => x = AllOnes n) (OptimumInRegion k) Path

/-- Exact two-phase expected runtime identity under the actual standard EA path measure. -/
theorem RuntimePhaseExpectationDecomposition {n : ℕ} (PositiveLength : 0 < n) (k : ℕ)
    (Initial : PMF (Bits n)) :
    ExpectedHittingTime (Step PositiveLength k) (fun x => x = AllOnes n) Initial =
      ExpectedHittingTime (Step PositiveLength k) (Region k) Initial +
      ∫⁻ Path, ENat.toENNReal (PostPlateauDuration k Path) ∂PathMeasure (Step PositiveLength k) Initial := by
  exact NestedGoalExpectedTimeDecomposition (PathMeasure (Step PositiveLength k) Initial)
    (Region k) (fun x => x = AllOnes n) (Set.to_countable _).measurableSet
    (measurableSet_singleton _) (OptimumInRegion k)

end
end ECTheoryLib.Analysis.EAJump
