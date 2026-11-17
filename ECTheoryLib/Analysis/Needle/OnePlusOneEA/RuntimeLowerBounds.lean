import ECTheoryLib.Analysis.Needle.OnePlusOneEA.Drift
import ECTheoryLib.Tools.Drift.ExponentialMomentNegative
import ECTheoryLib.Probability.Processes.ConditionalTransition
import ECTheoryLib.Probability.Processes.PathInvariant

/-!
# Exponential runtime lower tails for the actual (1+1) EA on Needle

A fixed initial distance at least n/4 yields Pr[T <= t] <= t e exp(-kappa n/4),
where kappa is an explicit positive constant. Every local/path premise is
verified for the actual kernel. Time counts mutation iterations after initialization.
-/

namespace ECTheoryLib.Analysis.EAOnNeedle
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- A positive dimension-independent exponent for the actual standard-mutation EA. -/
def RuntimeExponent : ℝ := AbsoluteMomentDriftExponent (Real.log 2) (1/2) (Real.exp 1)

theorem RuntimeExponentPositive : 0<RuntimeExponent :=
  AbsoluteMomentDriftExponentPositive _ _ _ (Real.log_pos (by norm_num)) (by norm_num) (Real.exp_pos _)

/-- Standard independent bit mutation may make large jumps. The existing
Hamming MGF, rather than a constant jump bound, supplies the negative-drift
tail for its actual weak-selection Needle trajectory. -/
theorem FixedRuntimeExponentialLowerTail {n : ℕ} (PositiveLength : 0<n)
    (InitialState : Bits n) (InitiallyFar : (n : ℝ)/4≤Potential InitialState) (t : ℕ) :
    PathMeasure (Step PositiveLength) (PMF.pure InitialState)
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*Real.exp 1*Real.exp (-RuntimeExponent*((n : ℝ)/4))) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits n) → ℝ := fun j Path => Potential (Path j)
  let S : Finset ℝ := Finset.univ.image (Potential (n := n))
  have Coordinates (j : ℕ) : Measurable (X j) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply j)
  have Values (j : ℕ) (Path : ℕ → Bits n) : X j Path∈S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have Initial : ∀ᵐ Path ∂μ, (n : ℝ)/4≤X 0 Path := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState] with Path AtInitial
    change (n : ℝ)/4≤Potential (Path 0)
    rw [AtInitial]
    exact InitiallyFar
  have Absorbing (j : ℕ) : ∀ᵐ Path ∂μ, X j Path≤0 → X (j+1) Path≤0 :=
    PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
      (fun x y => Potential x≤0 → Potential y≤0) (StepTargetAbsorbing PositiveLength) j
  have Moment (j : ℕ) (s : ℝ) (_Member : s∈S) (_Above : 0<s)
      (Positive : 0<μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun Path => Real.exp (Real.log 2*|X (j+1) Path-X j Path|))
        (StateEvent X j s) ≤ Real.exp 1 := by
    rw [EventConditionalExpectationEqCondIntegral]
    exact PathMeasureConditionalTransitionIntegralUpperBound (Step PositiveLength)
      (PMF.pure InitialState) j {x | Potential x=s}
      (fun x y => Real.exp (Real.log 2*|Potential y-Potential x|)) (Real.exp 1) Positive
      (fun x _ => OneStepAbsoluteExponentialMoment PositiveLength x)
  have Drift (j : ℕ) (s : ℝ) (_Member : s∈S) (Above : 0<s) (Below : s<(n : ℝ)/4)
      (Positive : 0<μ (StateEvent X j s)) : StateDrift μ X j s ≤ -(1/2 : ℝ) := by
    rw [StateDrift, EventConditionalExpectationEqCondIntegral]
    exact PathMeasureConditionalTransitionIntegralUpperBound (Step PositiveLength)
      (PMF.pure InitialState) j {x | Potential x=s} (fun x y => Potential x-Potential y)
      (-(1/2 : ℝ)) Positive (by
        intro x Equal
        change Potential x=s at Equal
        have Away : ¬ IsTarget x := fun Target => by
          have Zero := (PotentialEqZeroIffTarget x).mpr Target
          linarith
        rw [OneStepDriftAway PositiveLength x Away, Equal]
        have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
        have Ratio : 2*s/(n : ℝ)<1/2 := (div_lt_iff₀ PositiveN).mpr (by linarith)
        linarith)
  have Bound := ExponentialMomentNegativeDriftTail μ X S 0 ((n : ℝ)/4) (Real.log 2) (1/2) (Real.exp 1)
    (div_pos (Nat.cast_pos.mpr PositiveLength) (by norm_num)) (Real.log_pos (by norm_num))
    (by norm_num) (Real.exp_pos _) Coordinates Values Initial Absorbing Moment Drift t
  have Hitting (Path : ℕ → Bits n) :
      FirstHittingTime (fun s : ℝ => s≤0) (fun j => X j Path)=FirstHittingTime IsTarget Path := by
    have SameGoal (j : ℕ) : (X j Path≤0) ↔ IsTarget (Path j) := by
      rw [← PotentialEqZeroIffTarget]
      exact ⟨fun Zero => le_antisymm Zero (PotentialNonnegative _), fun Zero => Zero.le⟩
    unfold FirstHittingTime hittingAfter
    change (if ∃ j, 0≤j ∧ X j Path≤0 then
      ((sInf {j : ℕ | 0≤j ∧ X j Path≤0} : ℕ) : WithTop ℕ) else ⊤) =
        if ∃ j, 0≤j ∧ IsTarget (Path j) then
          ((sInf {j : ℕ | 0≤j ∧ IsTarget (Path j)} : ℕ) : WithTop ℕ) else ⊤
    simp only [SameGoal]
  simp_rw [Hitting] at Bound
  rw [sub_zero] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.EAOnNeedle
