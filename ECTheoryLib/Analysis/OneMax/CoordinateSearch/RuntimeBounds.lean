import ECTheoryLib.Algorithms.CoordinateSearch
import ECTheoryLib.Analysis.OneMax.RLS.Model
import ECTheoryLib.Analysis.OneMax.ElitistBitFlip
import ECTheoryLib.Tools.Runtime.LocalDrift

/-!
# Reusing local drift for a new coordinate-selection policy

The supplied policy may distinguish states with the same OneMax value. A common
lower bound on coordinate probabilities suffices for `RuntimeUpperBound`; exact
drift as a function of the potential is not needed. Time counts iterations and
the initial distribution may include optimal states.
-/
namespace ECTheoryLib.Analysis.CoordinateOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- The actual parameterized coordinate-search kernel for OneMax maximization. -/
def Step {n : Nat} (Choice : Bits n → PMF (Fin n)) : Transition (Bits n) :=
  CoordinateSearchStep Choice (Problems.MaxNotWorse OneMax)

/-- An arbitrary coordinate policy has drift equal to the total mass of zero bits. -/
theorem OneStepDrift {n : Nat} (Choice : Bits n → PMF (Fin n)) (x : Bits n) :
    (∫ y, RLSOnOneMax.Potential x - RLSOnOneMax.Potential y ∂(Step Choice x).toMeasure) =
      ∑ i : Fin n, (Choice x i).toReal * (if x i then (0 : ℝ) else 1) := by
  rw [Step, CoordinateSearchStep,
    ← PMF.toMeasure_map (RLSUpdate (Problems.MaxNotWorse OneMax) x) (Choice x)
      (measurable_of_finite _),
    integral_map_of_stronglyMeasurable (measurable_of_finite _)
      (measurable_of_finite
        (fun y : Bits n => RLSOnOneMax.Potential x - RLSOnOneMax.Potential y)).stronglyMeasurable,
    PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _InUniv
  change (Choice x i).toReal *
    (RLSOnOneMax.Potential x - RLSOnOneMax.Potential (RLSOnOneMax.Update x i)) = _
  exact congrArg (fun d => (Choice x i).toReal * d) (OneMax.ElitistBitFlipDecrease x i)

/-- A state-uniform lower bound on each coordinate's probability implies a
multiplicative lower bound on progress. It is allowed to depend on the instance size. -/
theorem OneStepDriftLowerBound {n : Nat} (Choice : Bits n → PMF (Fin n))
    (Delta : ℝ) (ProbabilityLower : ∀ x i, Delta ≤ (Choice x i).toReal) (x : Bits n) :
    Delta * RLSOnOneMax.Potential x ≤
      ∫ y, RLSOnOneMax.Potential x - RLSOnOneMax.Potential y ∂(Step Choice x).toMeasure := by
  rw [OneStepDrift]
  change Delta * (Problems.OneMax.ZeroCount x : ℝ) ≤ _
  rw [← Problems.OneMax.ZeroBitCountAsReal, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _InUniv
  apply mul_le_mul_of_nonneg_right (ProbabilityLower x i)
  cases x i with
  | false => exact zero_le_one
  | true => exact le_rfl

/-- The same logarithmic runtime interface applies to every such policy and initial
PMF. No claim that a biased policy outperforms uniform RLS is made by this bound. -/
theorem RuntimeUpperBound {n : Nat} (Choice : Bits n → PMF (Fin n))
    (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (ProbabilityLower : ∀ x i, Delta ≤ (Choice x i).toReal) (Initial : PMF (Bits n)) :
    ExpectedHittingTime (Step Choice) RLSOnOneMax.IsTarget Initial ≤ ENNReal.ofReal
      (∫ x, MultiplicativeDriftPotential 1 Delta (RLSOnOneMax.ZeroCount x : ℝ)
        ∂Initial.toMeasure) := by
  have ZeroIff : ∀ x : Bits n, RLSOnOneMax.ZeroCount x = 0 ↔ RLSOnOneMax.IsTarget x := by
    intro x
    simpa only [RLSOnOneMax.Potential, Nat.cast_eq_zero] using
      RLSOnOneMax.PotentialEqZeroIffTarget x
  apply Tools.Runtime.MultiplicativeRuntimeUpperBound (Step Choice) Initial
    RLSOnOneMax.ZeroCount RLSOnOneMax.IsTarget (fun _ => True) ZeroIff
  · exact ae_of_all _ (fun _ => trivial)
  · intro x
    exact ae_of_all _ (fun _ _ => trivial)
  · intro x
    have Preserves : ∀ᵐ i ∂(Choice x).toMeasure, True →
        RLSOnOneMax.ZeroCount x = 0 →
          RLSOnOneMax.ZeroCount (RLSOnOneMax.Update x i) = 0 := by
      apply ae_of_all
      intro i _Valid Zero
      have RealZero : RLSOnOneMax.Potential x = 0 := Nat.cast_eq_zero.mpr Zero
      exact Nat.cast_eq_zero.mp (OneMax.ElitistBitFlipPreservesZero x i RealZero)
    change ∀ᵐ y ∂((Choice x).map (RLSOnOneMax.Update x)).toMeasure, _
    rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
    exact (ae_map_iff (measurable_of_finite _).aemeasurable
      (Set.to_countable _).measurableSet).mpr Preserves
  · exact PositiveDelta
  · intro x _Valid _Nonzero
    exact OneStepDriftLowerBound Choice Delta ProbabilityLower x

/-- The concrete half-uniform policy satisfies the coordinate floor in real probabilities. -/
theorem HalfUniformProbabilityLower {n : Nat} (hn : 0 < n)
    (Preferred : Bits n → Fin n) (x : Bits n) (i : Fin n) :
    1 / (2 * (n : ℝ)) ≤ (HalfUniformChoice hn Preferred x i).toReal := by
  have Bound := ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (HalfUniformChoiceProbabilityLower hn Preferred x i)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, mul_inv, one_div] using Bound

/-- A concrete state-dependent policy is accepted by the generic runtime API.
The preferred-coordinate function is unrestricted; the uniform half gives the guarantee. -/
theorem HalfUniformRuntimeUpperBound {n : Nat} (hn : 0 < n)
    (Preferred : Bits n → Fin n) (Initial : PMF (Bits n)) :
    ExpectedHittingTime (Step (HalfUniformChoice hn Preferred)) RLSOnOneMax.IsTarget Initial ≤
      ENNReal.ofReal (∫ x, MultiplicativeDriftPotential 1 (1 / (2 * (n : ℝ)))
        (RLSOnOneMax.ZeroCount x : ℝ) ∂Initial.toMeasure) := by
  exact RuntimeUpperBound (HalfUniformChoice hn Preferred) (1 / (2 * (n : ℝ)))
    (one_div_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr hn)))
    (HalfUniformProbabilityLower hn Preferred) Initial

end
end ECTheoryLib.Analysis.CoordinateOneMax
