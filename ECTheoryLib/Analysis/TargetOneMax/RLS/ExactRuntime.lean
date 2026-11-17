import ECTheoryLib.Analysis.TargetOneMax.RLS.RuntimeBounds
import ECTheoryLib.Analysis.TargetOneMax.RLS.HarmonicDrift
import ECTheoryLib.Tools.Drift.FiniteMarkovExact

/-!
# Exact harmonic runtime of binary RLS from a fixed state

Doerr, Doerr, and Koetzing (2018), Algorithmica 80:1732–1768, Theorem 6,
pp. 1745–1746, specialized to alphabet size 2.
https://hpi.de/friedrich/docs/publications/2018/Algorithmica_d.pdf

The actual kernel, pure initial law, extended expectation, absorption, and zero
distance boundary are reused. Instead of summing separate level waiting times,
the proof verifies the equivalent unit-drift equation for the harmonic potential
`n H_(Hamming(x,z))` and applies proved additive upper and lower bounds.
Independence between level waiting times is unnecessary. Time counts mutations
after initialization and includes zero for an initially successful state.
-/

namespace ECTheoryLib.Analysis.RLSHamming

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open ECTheoryLib.Problems.TargetOneMax

noncomputable section

/-- The fixed-state logarithmic bound ensures finite expectation, permitting
subsequent recurrence arguments and conversion to real values. -/
theorem FixedRuntimeFinite {n : Nat} (PositiveLength : 0 < n)
    (Target InitialState : Bits n) :
    ExpectedRuntime PositiveLength Target InitialState ≠ ⊤ := by
  by_cases InitialZero : Hamming Target InitialState = 0
  · rw [FixedRuntimeEqZero PositiveLength Target InitialState InitialZero]
    exact ENNReal.zero_ne_top
  · have InitialPositive : 0 < Hamming Target InitialState := Nat.pos_of_ne_zero InitialZero
    have Bound := FixedRuntimeUpperBound PositiveLength Target InitialState InitialPositive
    exact ne_of_lt (lt_of_le_of_lt Bound ENNReal.ofReal_lt_top)

/-- The harmonic potential satisfies the remaining-time equation under the
actual transition kernel. Finite state ensures integrability. -/
theorem HarmonicPotentialBellman {n : Nat} (PositiveLength : 0 < n)
    (Target State : Bits n) (Nonoptimal : Hamming Target State ≠ 0) :
    HarmonicPotential Target State =
      1 + ∫ Next, HarmonicPotential Target Next ∂(Step PositiveLength Target State).toMeasure := by
  have Drift := OneStepHarmonicDrift PositiveLength Target State
  rw [if_neg Nonoptimal] at Drift
  rw [integral_sub (integrable_const _) (Integrable.of_finite),
    integral_const, probReal_univ, one_smul] at Drift
  linarith

/-- Binary specialization of Doerr, Doerr, and Koetzing (2018), Theorem 6:
from distance `k`, the exact extended expected iteration count is `n H_k`,
including `k = 0`. Initialization is not charged as an iteration. -/
theorem FixedRuntimeExact {n : Nat} (PositiveLength : 0 < n)
    (Target InitialState : Bits n) :
    ExpectedRuntime PositiveLength Target InitialState =
      ENNReal.ofReal ((n : ℝ) * (harmonic (Hamming Target InitialState) : ℝ)) := by
  by_cases InitialZero : Hamming Target InitialState = 0
  · rw [FixedRuntimeEqZero PositiveLength Target InitialState InitialZero,
      InitialZero, harmonic_zero, Rat.cast_zero, mul_zero, ENNReal.ofReal_zero]
  · have ZeroIffTarget : ∀ State : Bits n,
        HarmonicPotential Target State = 0 ↔ State = Target := by
      intro State
      rw [HarmonicPotentialEqZeroIff PositiveLength Target State]
      exact HammingEqZeroIffEq Target State
    have LocalDrift : ∀ State : Bits n,
        (∫ Next, HarmonicPotential Target State - HarmonicPotential Target Next
          ∂(Step PositiveLength Target State).toMeasure) =
          if HarmonicPotential Target State = 0 then 0 else (1 : ℝ) := by
      intro State
      rw [OneStepHarmonicDrift PositiveLength Target State]
      simp only [HarmonicPotentialEqZeroIff PositiveLength Target State]
    have Absorbing : ∀ State : Bits n,
        ∀ᵐ Next ∂(Step PositiveLength Target State).toMeasure,
          HarmonicPotential Target State = 0 → HarmonicPotential Target Next = 0 := by
      intro State
      filter_upwards [StepPreservesZeroHamming PositiveLength Target State] with Next Preserves
      intro CurrentZero
      apply (HarmonicPotentialEqZeroIff PositiveLength Target Next).mpr
      exact Preserves ((HarmonicPotentialEqZeroIff PositiveLength Target State).mp CurrentZero)
    have ExactFromDrift := AdditiveRuntimeExactOfLocalDrift
      (Step PositiveLength Target) (HarmonicPotential Target) (fun x => x = Target)
      (HarmonicPotentialNonnegative Target) ZeroIffTarget 1 (by norm_num)
      LocalDrift Absorbing InitialState
    rw [div_one] at ExactFromDrift
    exact ExactFromDrift

/-- Real-valued form of the exact expectation. The proved finiteness excludes
the default real conversion of infinity. -/
theorem FixedRuntimeExactReal {n : Nat} (PositiveLength : 0 < n)
    (Target InitialState : Bits n) :
    (ExpectedRuntime PositiveLength Target InitialState).toReal =
      (n : ℝ) * (harmonic (Hamming Target InitialState) : ℝ) := by
  rw [FixedRuntimeExact PositiveLength Target InitialState]
  exact ENNReal.toReal_ofReal (HarmonicPotentialNonnegative Target InitialState)

end
end ECTheoryLib.Analysis.RLSHamming
