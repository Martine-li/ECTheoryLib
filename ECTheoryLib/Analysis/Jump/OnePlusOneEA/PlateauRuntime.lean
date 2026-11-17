import ECTheoryLib.Analysis.Jump.OnePlusOneEA.RuntimeBounds
import ECTheoryLib.Tools.Runtime.Geometric

/-!
# Geometric runtime bounds from the Jump plateau

The standard (1+1) EA flips bits independently at rate 1/n and uses the existing
Jump objective and elitist selection. The admissible region consists exactly of
OneMax = n-k and the global optimum, for 1 <= k <= n. Neutral moves within the
plateau are allowed. Time counts transitions after initialization; an optimal
initial state has hitting time zero. This is a single-level distribution bound,
not a distributional analysis of all phases from arbitrary initial states.
-/

namespace ECTheoryLib.Analysis.EAJump
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability ECTheoryLib.Tools.Runtime
open scoped unitInterval
noncomputable section

/-- The exact plateau-to-optimum mutation probability as a probability parameter. -/
def GapParameter {n k : Nat} (PositiveGap : 0 < k) (GapAtMostLength : k ≤ n) : I := by
  have PositiveLength : 0 < n := lt_of_lt_of_le PositiveGap GapAtMostLength
  have PositiveN : (0 : Real) < n := by exact_mod_cast PositiveLength
  have OneLeN : (1 : Real) ≤ n := by exact_mod_cast PositiveLength
  have RateNonnegative : 0 ≤ 1/(n : Real) := by positivity
  have RateAtMostOne : 1/(n : Real) ≤ 1 := (div_le_one PositiveN).mpr OneLeN
  have NonnegativeFailure : 0 ≤ 1-1/(n : Real) := sub_nonneg.mpr RateAtMostOne
  have FailureAtMostOne : 1-1/(n : Real) ≤ 1 := by linarith
  refine ⟨GapProbability n k, (GapProbabilityPositive PositiveGap GapAtMostLength).le, ?_⟩
  unfold GapProbability
  calc
    _ ≤ (1 : Real) * 1 := mul_le_mul (pow_le_one₀ RateNonnegative RateAtMostOne)
      (pow_le_one₀ NonnegativeFailure FailureAtMostOne) (pow_nonneg NonnegativeFailure _) zero_le_one
    _ = 1 := one_mul 1

/-- The global optimum is accepted; its exact mutation mass gives a lower bound on the selected-step success probability. -/
theorem PlateauStepGoalProbability {n k : Nat} (PositiveLength : 0 < n) (PositiveGap : 0 < k)
    (GapAtMostLength : k ≤ n) (x : Bits n) (Inside : Region k x) (NotGoal : x ≠ AllOnes n) :
    GapProbability n k ≤ (Step PositiveLength k x).toMeasure.real {AllOnes n} := by
  have AcceptOptimum : Update k x (AllOnes n) = AllOnes n := by
    apply ElitistSelectAccept
    change Jump k x ≤ Jump k (AllOnes n)
    rw [Problems.Jump.JumpAllOnes]
    exact Problems.Jump.JumpLeMax x
  have PointProbability := PlateauMutationProbability PositiveLength PositiveGap GapAtMostLength x Inside NotGoal
  change _ ≤ ((StandardBitMutation PositiveLength x).map (Update k x)).toMeasure.real {AllOnes n}
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _)]
  calc
    GapProbability n k = (StandardBitMutation PositiveLength x (AllOnes n)).toReal := PointProbability.symm
    _ = (StandardBitMutation PositiveLength x).toMeasure.real {AllOnes n} := by
      rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    _ ≤ _ := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro y IsOptimum
      change y = AllOnes n at IsOptimum
      rw [IsOptimum]
      exact AcceptOptimum

/-- Elitist selection preserves the plateau-or-optimum region along actual paths. -/
theorem PlateauPaths {n k : Nat} (PositiveLength : 0 < n) (Initial : PMF (Bits n))
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Region k x) (t : Nat) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength k) Initial, Region k (Path t) := by
  apply PathMeasurePreservesProperty _ _ _ Initially _ t
  intro x
  exact StepAEUpdate PositiveLength k x (fun y => Region k x -> Region k y)
    (fun y Inside => UpdateRegion k x y Inside)

/-- The optimum is absorbing for the actual selected transition. -/
theorem StepGoalAbsorption {n : Nat} (PositiveLength : 0 < n) (k : Nat) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength k x).toMeasure, x = AllOnes n -> y = AllOnes n :=
  StepAEUpdate PositiveLength k x (fun y => x = AllOnes n -> y = AllOnes n)
    (fun y AtGoal => UpdateGoal k x y AtGoal)

/-- From any random initial state supported on the plateau or optimum, the runtime is dominated by the geometric gap-crossing waiting time. -/
theorem PlateauRuntimeGeometricDomination {n k : Nat} (PositiveLength : 0 < n) (PositiveGap : 0 < k)
    (GapAtMostLength : k ≤ n) (Initial : PMF (Bits n))
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Region k x) :
    StochasticDominated
      ((PathMeasure (Step PositiveLength k) Initial).map (FirstHittingTime (fun x => x = AllOnes n)))
      ((geometricMeasure (GapParameter PositiveGap GapAtMostLength)).map
        (fun j : Nat => ((j+1 : Nat) : WithTop Nat))) := by
  apply PathWaitingGeometricDomination (Step PositiveLength k) Initial (fun x => x = AllOnes n)
    (Region k) (GapParameter PositiveGap GapAtMostLength) (GapProbabilityPositive PositiveGap GapAtMostLength)
    (PlateauPaths PositiveLength Initial Initially) (StepGoalAbsorption PositiveLength k)
  intro x Inside NotGoal
  exact PlateauStepGoalProbability PositiveLength PositiveGap GapAtMostLength x Inside NotGoal

/-- The corresponding expected number of transitions is bounded by the reciprocal gap probability. -/
theorem PlateauExpectedRuntime {n k : Nat} (PositiveLength : 0 < n) (PositiveGap : 0 < k)
    (GapAtMostLength : k ≤ n) (Initial : PMF (Bits n))
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Region k x) :
    ExpectedHittingTime (Step PositiveLength k) (fun x => x = AllOnes n) Initial ≤
      ENNReal.ofReal (1/GapProbability n k) := by
  apply PathWaitingExpectedRuntime (Step PositiveLength k) Initial (fun x => x = AllOnes n)
    (Region k) (GapParameter PositiveGap GapAtMostLength) (GapProbabilityPositive PositiveGap GapAtMostLength)
    (PlateauPaths PositiveLength Initial Initially) (StepGoalAbsorption PositiveLength k)
  intro x Inside NotGoal
  exact PlateauStepGoalProbability PositiveLength PositiveGap GapAtMostLength x Inside NotGoal


/-- The plateau runtime has a geometric tail even when neutral moves change the parent. -/
theorem PlateauRuntimeTail {n k : ℕ} (PositiveLength : 0 < n) (PositiveGap : 0 < k)
    (GapAtMostLength : k ≤ n) (Initial : PMF (Bits n))
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Region k x) (t : ℕ) :
    (PathMeasure (Step PositiveLength k) Initial).real
        {Path | (t : WithTop ℕ) < FirstHittingTime (fun x => x = AllOnes n) Path} ≤
      (1-GapProbability n k)^t := by
  apply PathWaitingSurvivalBound (Step PositiveLength k) Initial (fun x => x = AllOnes n)
    (Region k) (GapParameter PositiveGap GapAtMostLength)
    (PlateauPaths PositiveLength Initial Initially) (StepGoalAbsorption PositiveLength k) _ t
  intro x Inside NotGoal
  exact PlateauStepGoalProbability PositiveLength PositiveGap GapAtMostLength x Inside NotGoal

/-- A fixed plateau state supplies the region premise directly from its number of one-bits. -/
theorem PlateauPureInitial {n k : ℕ} (PositiveGap : 0 < k) (GapAtMostLength : k ≤ n)
    (x : Bits n) (OnPlateau : OneMax x = n-k) :
    ∀ᵐ y ∂(PMF.pure x).toMeasure, Region k y := by
  apply PMFAEOfSupport
  intro y InSupport
  have Equal : y = x := by
    simpa only [PMF.support_pure, Set.mem_singleton_iff] using InSupport
  rw [Equal]
  exact (RegionIff PositiveGap GapAtMostLength x).mpr (Or.inl OnPlateau)

end
end ECTheoryLib.Analysis.EAJump
