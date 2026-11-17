import ECTheoryLib.Tools.Runtime.NonabsorbingGeometricJump
import ECTheoryLib.Analysis.Needle.OnePlusOneEA.ExponentialHorizon

/-!
# First-hitting lower tails for the nonelitist (1,1) EA on Needle

The sole independently mutated offspring replaces the parent at every step.
Time counts mutation iterations, with initialization at zero. Local facts
are reused from the identical pre-optimum (1+1) EA kernel.
-/

namespace ECTheoryLib.Analysis.CommaEAOnNeedle
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

abbrev IsTarget {n : ℕ} : Bits n → Prop := EAOnNeedle.IsTarget
abbrev Potential {n : ℕ} : Bits n → ℝ := EAOnNeedle.Potential

/-- The (1,1) EA replaces its parent by its sole independently mutated
offspring, even if fitness decreases. In particular the optimum is not frozen. -/
def Step {n : ℕ} (PositiveLength : 0<n) : Transition (Bits n) :=
  StandardBitMutation PositiveLength

/-- Until the first optimum, both EA variants use the same mutation law on
the Needle plateau. This equality does not hold at the optimum. -/
theorem StepAway {n : ℕ} (PositiveLength : 0<n) (x : Bits n) (Away : ¬IsTarget x) :
    Step PositiveLength x=EAOnNeedle.Step PositiveLength x :=
  (EAOnNeedle.StepAway PositiveLength x Away).symm

/-- First-hitting lower tail for the actual nonelitist EA. The trajectory
continues after reaching the target and may leave it on the next mutation. -/
theorem FixedRuntimeGeometricJumpLowerTail {n : ℕ} (PositiveLength : 0<n)
    (InitialState : Bits n) (InitiallyFar : (n : ℝ)/4≤Potential InitialState) (t : ℕ) :
    PathMeasure (Step PositiveLength) (PMF.pure InitialState)
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*(6*Real.exp 1)*
        Real.exp (-EAOnNeedle.GeometricRuntimeExponent*((n : ℝ)/4))) := by
  have Initial : ∀ᵐ x ∂(PMF.pure InitialState).toMeasure, (n : ℝ)/4≤Potential x := by
    rw [PMF.toMeasure_pure]
    exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr InitiallyFar
  have Away (x : Bits n) (Above : 0<Potential x) : ¬IsTarget x := fun Target => by
    have Zero := (EAOnNeedle.PotentialEqZeroIffTarget x).mpr Target
    linarith
  have Bound := Tools.Runtime.GeometricJumpRuntimeLowerTailNonabsorbing
    (Step PositiveLength) (PMF.pure InitialState) Potential IsTarget 0 ((n : ℝ)/4) 1 (1/2) (Real.exp 1)
    (div_pos (Nat.cast_pos.mpr PositiveLength) (by norm_num)) (by norm_num) (by norm_num) (Real.exp_pos _)
    (fun x => by
      change EAOnNeedle.Potential x≤0 ↔ EAOnNeedle.IsTarget x
      rw [← EAOnNeedle.PotentialEqZeroIffTarget]
      exact ⟨fun Zero => le_antisymm Zero (EAOnNeedle.PotentialNonnegative _), fun Zero => Zero.le⟩)
    Initial (by
      intro x Above j
      rw [StepAway PositiveLength x (Away x Above)]
      simpa only [show (1 : ℝ)+1=2 by norm_num] using EAOnNeedle.OneStepAbsoluteJumpTail PositiveLength x j)
    (by
      intro x Above Below
      rw [StepAway PositiveLength x (Away x Above), EAOnNeedle.OneStepDriftAway PositiveLength x (Away x Above)]
      have Ratio : 2*Potential x/(n : ℝ)<1/2 :=
        (div_lt_iff₀ (Nat.cast_pos.mpr PositiveLength)).mpr (by linarith)
      linarith) t
  have Constant : GeometricJumpMomentBound 1 (Real.exp 1)=6*Real.exp 1 := by
    dsimp [GeometricJumpMomentBound]
    ring
  simpa only [sub_zero, Constant, EAOnNeedle.GeometricRuntimeExponent] using Bound

/-- Explicit exponential horizon with the same constants as the elitist
variant, despite the lack of target absorption in the actual process. -/
theorem FixedRuntimeExponentialHorizon {n : ℕ} (PositiveLength : 0<n)
    (InitialState : Bits n) (InitiallyFar : (n : ℝ)/4≤Potential InitialState)
    (LargeDimension : 16*Real.log (6*Real.exp 1) ≤ EAOnNeedle.GeometricRuntimeExponent*(n : ℝ))
    (t : ℕ) (TimeBound : (t : ℝ)≤Real.exp (EAOnNeedle.GeometricRuntimeExponent*(n : ℝ)/8)) :
    PathMeasure (Step PositiveLength) (PMF.pure InitialState)
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
        ENNReal.ofReal (Real.exp (-EAOnNeedle.GeometricRuntimeExponent*(n : ℝ)/16)) := by
  have Bound := FixedRuntimeGeometricJumpLowerTail PositiveLength InitialState InitiallyFar t
  have Value := NegativeDriftExponentialHorizonValue (t : ℝ) ((n : ℝ)/4) 1 (6*Real.exp 1)
    EAOnNeedle.GeometricRuntimeExponent EAOnNeedle.GeometricRuntimeExponent
    (div_nonneg (Nat.cast_nonneg n) (by norm_num))
    (by norm_num) (by positivity) (by simp) (by simp only [mul_one]; nlinarith)
    (by convert TimeBound using 1; congr 1; ring)
  have Comparison : (t : ℝ)*(6*Real.exp 1)*Real.exp (-EAOnNeedle.GeometricRuntimeExponent*((n : ℝ)/4)) ≤
      Real.exp (-EAOnNeedle.GeometricRuntimeExponent*(n : ℝ)/16) := by
    convert Value using 1 <;> congr 1 <;> ring
  exact Bound.trans (ENNReal.ofReal_le_ofReal Comparison)

end
end ECTheoryLib.Analysis.CommaEAOnNeedle
