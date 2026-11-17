import ECTheoryLib.Analysis.MultivalOneMax.RLS.HarmonicDrift
import ECTheoryLib.Tools.Drift.FiniteMarkovExact

/-!
# Exact fixed-state runtime of multi-valued RLS

Doerr, Doerr, and Koetzing (2018), Algorithmica 80:1732–1768, Theorem 6,
pp. 1745–1746, for the interval-distance objective.
https://hpi.de/friedrich/docs/publications/2018/Algorithmica_d.pdf

Each iteration uniformly chooses a coordinate and one of its `r-1` different
values, accepting nonincreasing total interval distance. Runtime is the first
target hit on actual trajectories with a pure initial law, counting only
post-initialization iterations. The finite-kernel exact additive-drift bridge
is reused, including distance zero and without assuming finite expectation.
-/

namespace ECTheoryLib.Analysis.RLSMultival

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open ECTheoryLib.Problems.MultivalOneMax

noncomputable section

/-- Extended expected runtime of the actual multi-valued RLS kernel from
a specified fixed initial state. -/
def ExpectedRuntime {n r : Nat} (PositiveLength : 0 < n) (AlphabetSize : 2 ≤ r)
    (Target InitialState : MultiValues n r) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength AlphabetSize Target) (fun x => x = Target)
    (PMF.pure InitialState)

/-- A fixed initial target gives first hitting time zero almost surely. -/
theorem FixedHittingTimeEqZero {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target InitialState : MultiValues n r)
    (InitialZero : Hamming Target InitialState = 0) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength AlphabetSize Target) (PMF.pure InitialState),
      FirstHittingTime (fun x => x = Target) Path = 0 := by
  exact FirstHittingTimeOfPureTarget (Step PositiveLength AlphabetSize Target)
    (fun x => x = Target) InitialState ((HammingEqZeroIffEq Target InitialState).mp InitialZero)

theorem FixedRuntimeEqZero {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target InitialState : MultiValues n r)
    (InitialZero : Hamming Target InitialState = 0) :
    ExpectedRuntime PositiveLength AlphabetSize Target InitialState = 0 := by
  exact ExpectedHittingTimeOfPureTarget (Step PositiveLength AlphabetSize Target)
    (fun x => x = Target) InitialState ((HammingEqZeroIffEq Target InitialState).mp InitialZero)

/-- Doerr, Doerr, and Koetzing (2018), Theorem 6: from initial Hamming
distance `k`, the exact expected mutation-iteration count is `n(r-1)H_k`,
including `k=0`. No finite-expectation premise is assumed. -/
theorem FixedRuntimeExact {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target InitialState : MultiValues n r) :
    ExpectedRuntime PositiveLength AlphabetSize Target InitialState =
      ENNReal.ofReal ((n : ℝ) * ((r - 1 : Nat) : ℝ) *
        (harmonic (Hamming Target InitialState) : ℝ)) := by
  have ZeroIffTarget : ∀ State : MultiValues n r,
      HarmonicPotential Target State = 0 ↔ State = Target := by
    intro State
    rw [HarmonicPotentialEqZeroIff PositiveLength AlphabetSize, HammingEqZeroIffEq]
  have LocalDrift : ∀ State : MultiValues n r,
      (∫ Next, HarmonicPotential Target State - HarmonicPotential Target Next
        ∂(Step PositiveLength AlphabetSize Target State).toMeasure) =
        if HarmonicPotential Target State = 0 then 0 else (1 : ℝ) := by
    intro State
    rw [OneStepHarmonicDrift PositiveLength AlphabetSize Target State]
    simp only [HarmonicPotentialEqZeroIff PositiveLength AlphabetSize Target State]
  have Absorbing : ∀ State : MultiValues n r,
      ∀ᵐ Next ∂(Step PositiveLength AlphabetSize Target State).toMeasure,
        HarmonicPotential Target State = 0 → HarmonicPotential Target Next = 0 := by
    intro State
    filter_upwards [StepPreservesZeroHamming PositiveLength AlphabetSize Target State]
      with Next Preserves
    intro CurrentZero
    apply (HarmonicPotentialEqZeroIff PositiveLength AlphabetSize Target Next).mpr
    exact Preserves ((HarmonicPotentialEqZeroIff PositiveLength AlphabetSize Target State).mp CurrentZero)
  have ExactFromDrift := AdditiveRuntimeExactOfLocalDrift
    (Step PositiveLength AlphabetSize Target) (HarmonicPotential Target) (fun x => x = Target)
    (HarmonicPotentialNonnegative Target) ZeroIffTarget 1 (by norm_num)
    LocalDrift Absorbing InitialState
  rw [div_one] at ExactFromDrift
  simpa only [ExpectedRuntime, HarmonicPotential, RuntimeScale, Nat.cast_mul] using ExactFromDrift

/-- The exact extended-real formula is finite and therefore excludes infinity. -/
theorem FixedRuntimeFinite {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target InitialState : MultiValues n r) :
    ExpectedRuntime PositiveLength AlphabetSize Target InitialState ≠ ⊤ := by
  rw [FixedRuntimeExact PositiveLength AlphabetSize Target InitialState]
  exact ENNReal.ofReal_ne_top

/-- Real-valued exact formula, obtained after proving the extended expectation
finite rather than interpreting infinity through its default real conversion. -/
theorem FixedRuntimeExactReal {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target InitialState : MultiValues n r) :
    (ExpectedRuntime PositiveLength AlphabetSize Target InitialState).toReal =
      (n : ℝ) * ((r - 1 : Nat) : ℝ) * (harmonic (Hamming Target InitialState) : ℝ) := by
  rw [FixedRuntimeExact PositiveLength AlphabetSize Target InitialState]
  apply ENNReal.toReal_ofReal
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Tools.Runtime.HarmonicNonnegative _)

/-- Away from the target, the harmonic potential satisfies the actual
kernel's remaining-time equation. -/
theorem HarmonicPotentialBellman {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target State : MultiValues n r)
    (Nonoptimal : Hamming Target State ≠ 0) :
    HarmonicPotential Target State =
      1 + ∫ Next, HarmonicPotential Target Next ∂(Step PositiveLength AlphabetSize Target State).toMeasure := by
  have Drift := OneStepHarmonicDrift PositiveLength AlphabetSize Target State
  rw [if_neg Nonoptimal] at Drift
  rw [integral_sub (integrable_const _) (Integrable.of_finite),
    integral_const, probReal_univ, one_smul] at Drift
  linarith

end
end ECTheoryLib.Analysis.RLSMultival
