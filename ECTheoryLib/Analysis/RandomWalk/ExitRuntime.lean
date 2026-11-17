import ECTheoryLib.Probability.RandomWalks.FiniteBiasedWalk
import ECTheoryLib.Probability.Processes.CountableHistoryConditional
import ECTheoryLib.Probability.Processes.PathDriftBounds
import ECTheoryLib.Tools.Drift.NonabsorbingAdditive

/-!
# Two-sided exit times from a quadratic potential

The exit goal is not absorbing; full-history additive drift justifies stopping.
-/

namespace ECTheoryLib.Analysis.FiniteBiasedWalk
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open scoped unitInterval
noncomputable section

/-- Exit from [1,m-1] is fast even when the linear mean drift is very small. -/
theorem FixedExitRuntimeUpperBound (N m : ℕ) (PositiveM : 0<m) (Capacity : m≤N)
    (ε : I) (SmallBias : (ε : ℝ)*m<1) (x : Fin (N+1)) :
    ExpectedHittingTime (Probability.FiniteBiasedWalk.Step N ε)
      (fun y => y.val=0 ∨ m≤y.val) (PMF.pure x) ≤
      ENNReal.ofReal (Probability.FiniteBiasedWalk.ExitPotential m x/(1-(ε : ℝ)*m)) := by
  classical
  let Step := Probability.FiniteBiasedWalk.Step N ε
  let V := @Probability.FiniteBiasedWalk.ExitPotential m N
  let μ := PathMeasure Step (PMF.pure x)
  let X : ℕ → (ℕ → Fin (N+1)) → ℝ := fun t Path => V (Path t)
  let S : Finset ℝ := insert 0 (Finset.univ.image V)
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | Image
    · rw [Zero]
    · obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp Image
      exact Probability.FiniteBiasedWalk.ExitPotentialNonnegative m y
  have IntegrableV (t : ℕ) := PathMeasureCoordinateIntegrable Step (PMF.pure x) V t
  have Bound := AdditiveDriftUpperBoundNonabsorbing μ X
    (Filtration.piLE (X := fun _ : ℕ => Fin (N+1))) (CountablePathPotentialAdapted V)
    S (1-(ε : ℝ)*m) (by simp [S]) Nonnegative
    (fun t Path => Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Path t,Finset.mem_univ _,rfl⟩))
    (sub_pos.mpr SmallBias) (by
      intro t
      have Conditional := PathMeasureStateConditionalExpectationOfIntegrable Step (PMF.pure x) t
        (fun a b => V a-V b) ((IntegrableV t).sub (IntegrableV (t+1)))
      filter_upwards [Conditional] with Path Equal
      intro Active
      have Interior : (Path t).val≠0 ∧ (Path t).val<m := by
        have NotGoal : ¬((Path t).val=0 ∨ m≤(Path t).val) := by
          intro Hit
          exact Active ((Probability.FiniteBiasedWalk.ExitPotentialZeroIff m PositiveM (Path t)).mpr Hit)
        exact ⟨fun h => NotGoal (Or.inl h),lt_of_not_ge (fun h => NotGoal (Or.inr h))⟩
      change 1-(ε : ℝ)*m≤(μ[fun Path => V (Path t)-V (Path (t+1)) |
        Filtration.piLE (X := fun _ : ℕ => Fin (N+1)) t]) Path
      rw [Equal]
      exact Probability.FiniteBiasedWalk.OneStepExitDriftLowerBound N m Capacity ε (Path t) Interior.1 Interior.2)
  have Mean : ExpectedValue μ (X 0)=V x := PathMeasurePureInitialIntegral Step x V
  rw [Mean] at Bound
  rw [ExpectedHittingTimeEqExpectedZero Step (PMF.pure x) V _
    (Probability.FiniteBiasedWalk.ExitPotentialZeroIff m PositiveM)]
  exact Bound

end
end ECTheoryLib.Analysis.FiniteBiasedWalk
