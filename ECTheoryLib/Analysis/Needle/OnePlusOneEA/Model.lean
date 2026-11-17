import ECTheoryLib.Algorithms.OnePlusOneEA
import ECTheoryLib.Problems.Needle
import ECTheoryLib.Problems.TargetOneMax
import ECTheoryLib.Probability.PMF.FinitePMF

/-!
# Actual standard-mutation (1+1) EA on Needle

Weak selection accepts every candidate from the nonoptimal plateau; the
optimum is absorbing. Standard independent bit mutation includes zero and
multiple flips. The analysis potential is distance to the all-ones target.
-/

namespace ECTheoryLib.Analysis.EAOnNeedle
open MeasureTheory ECTheoryLib.Probability
noncomputable section

abbrev Fitness {n : ℕ} : Bits n → ℕ := Problems.Needle (AllOnes n)
abbrev IsTarget {n : ℕ} (x : Bits n) : Prop := x=AllOnes n
def Potential {n : ℕ} (x : Bits n) : ℝ := (Problems.OneMax.ZeroCount x : ℝ)
def Step {n : ℕ} (PositiveLength : 0<n) : Transition (Bits n) :=
  OnePlusOneEAStep PositiveLength (Problems.MaxNotWorse Fitness)

theorem PotentialNonnegative {n : ℕ} (x : Bits n) : 0≤Potential x := Nat.cast_nonneg _
theorem PotentialEqZeroIffTarget {n : ℕ} (x : Bits n) : Potential x=0 ↔ IsTarget x := by
  rw [Potential, Nat.cast_eq_zero, Problems.OneMax.ZeroCountEqZeroIffAllOnes]
theorem IsTargetIffOptimal {n : ℕ} (x : Bits n) :
    IsTarget x ↔ Problems.IsMaximizer Fitness x :=
  (Problems.Needle.IsOptimalIffEqTarget (AllOnes n) x).symm

theorem SelectionAway {n : ℕ} (x y : Bits n) (Away : ¬ IsTarget x) :
    ElitistSelect (Problems.MaxNotWorse Fitness) x y=y := by
  apply ElitistSelectAccept
  change Problems.Needle (AllOnes n) x ≤ Problems.Needle (AllOnes n) y
  rw [Problems.Needle.AwayFromTarget _ _ Away]
  exact Nat.zero_le _

theorem SelectionAtTarget {n : ℕ} (x y : Bits n) (Target : IsTarget x) :
    ElitistSelect (Problems.MaxNotWorse Fitness) x y=x := by
  by_cases Same : y=x
  · rw [Same, ElitistSelectAccept _ x x (by exact le_rfl)]
  · apply ElitistSelectReject
    change ¬ Problems.Needle (AllOnes n) x ≤ Problems.Needle (AllOnes n) y
    have Away : y≠AllOnes n := by rw [← Target]; exact Same
    rw [Problems.Needle.AwayFromTarget _ _ Away, Target, Problems.Needle.AtTarget]
    omega

/-- From every plateau state the actual weak-selection kernel is exactly
standard independent bit mutation, including zero and multiple flips. -/
theorem StepAway {n : ℕ} (PositiveLength : 0<n) (x : Bits n) (Away : ¬ IsTarget x) :
    Step PositiveLength x=StandardBitMutation PositiveLength x := by
  have Selected : (fun y => ElitistSelect (Problems.MaxNotWorse Fitness) x y)=id :=
    funext (fun y => SelectionAway x y Away)
  rw [Step, OnePlusOneEAStep, Selected, PMF.map_id]

theorem StepTargetAbsorbing {n : ℕ} (PositiveLength : 0<n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, Potential x≤0 → Potential y≤0 := by
  apply PMFAEOfSupport
  intro y Supported Zero
  have Target := (PotentialEqZeroIffTarget x).mp (le_antisymm Zero (PotentialNonnegative x))
  obtain ⟨Candidate, _Possible, Selected⟩ :=
    (OnePlusOneEAStepSupport PositiveLength (Problems.MaxNotWorse Fitness) x y).mp Supported
  rw [SelectionAtTarget x Candidate Target] at Selected
  rw [← Selected]
  exact Zero

/-- Neutral acceptance does not invalidate the generic Hamming bound. -/
theorem SelectedPotentialJumpBound {n : ℕ} (x Candidate : Bits n) :
    |Potential (ElitistSelect (Problems.MaxNotWorse Fitness) x Candidate)-Potential x| ≤
      (Problems.TargetOneMax.Hamming x Candidate : ℝ) := by
  by_cases Target : IsTarget x
  · rw [SelectionAtTarget x Candidate Target, sub_self, abs_zero]
    exact Nat.cast_nonneg _
  · rw [SelectionAway x Candidate Target]
    exact Problems.TargetOneMax.ZeroCountDifferenceLeHamming x Candidate

end
end ECTheoryLib.Analysis.EAOnNeedle
