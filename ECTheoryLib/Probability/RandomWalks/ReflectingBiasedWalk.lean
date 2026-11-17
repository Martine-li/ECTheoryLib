import ECTheoryLib.Probability.RandomWalks.UnboundedBiasedWalk

/-!
# An unbounded walk that leaves the target

Reuse the upward-biased walk at positive states and reflect zero to one.
Every higher level is actually reachable; there is no absorbing target.
-/

namespace ECTheoryLib.Probability.ReflectingBiasedWalk
open MeasureTheory
noncomputable section

/-- At zero the walk returns to one; at every positive state it moves up
with probability 3/4 and down with probability 1/4. There is no upper cap. -/
def Step (x : ℕ) : PMF ℕ :=
  if x=0 then PMF.pure 1 else UnboundedBiasedWalk.Step x

theorem ZeroLeaves : Step 0=PMF.pure 1 := by simp [Step]

theorem StepAbsoluteJumpBound (x : ℕ) :
    ∀ᵐ (y : ℕ) ∂(Step x).toMeasure, |(y : ℝ)-(x : ℝ)|≤1 := by
  by_cases Zero : x=0
  · rw [Step,if_pos Zero,PMF.toMeasure_pure]
    filter_upwards [ae_eq_dirac (fun y : ℕ => y)] with y Equal
    change y=1 at Equal
    simp [Zero,Equal]
  · rw [Step,if_neg Zero]
    exact UnboundedBiasedWalk.StepAbsoluteJumpBound x

theorem OneStepIncrement (x : ℕ) :
    (∫ y, (y : ℝ)-(x : ℝ) ∂(Step x).toMeasure) = if x=0 then 1 else (1/2 : ℝ) := by
  by_cases Zero : x=0
  · simp [Step,Zero,PMF.toMeasure_pure]
  · rw [Step,if_neg Zero]
    exact UnboundedBiasedWalk.OneStepIncrement x |>.trans (by rw [if_neg Zero,if_neg Zero])

theorem UpwardStepPossible (x : ℕ) : x+1∈(Step x).support := by
  by_cases Zero : x=0
  · simp [Zero,ZeroLeaves]
  · rw [Step,if_neg Zero]
    exact UnboundedBiasedWalk.UpwardStepPossible x (Nat.pos_of_ne_zero Zero)

/-- Arbitrarily high levels are reachable from every initial state,
including zero, under the actual transition kernel. -/
theorem HigherLevelReachable (x t : ℕ) : x+t∈(Evolve Step (PMF.pure x) t).support := by
  induction t with
  | zero => simp [Evolve]
  | succ t Previous =>
    rw [Evolve,PMF.mem_support_bind_iff]
    refine ⟨x+t,Previous,?_⟩
    simpa only [Nat.add_assoc] using UpwardStepPossible (x+t)

end
end ECTheoryLib.Probability.ReflectingBiasedWalk
