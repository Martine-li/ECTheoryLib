import ECTheoryLib.Analysis.TargetOneMax.RLS.Drift
import ECTheoryLib.Tools.Drift.FiniteMarkov

/-!
# Binary RLS runtime for an arbitrary target and fixed initialization

This specializes the multiplicative upper bound after equation (1) in the proof
of Theorem 6 of Doerr, Doerr, and Koetzing (2018), Algorithmica 80:1732–1768,
p. 1745, to alphabet size 2.
https://hpi.de/friedrich/docs/publications/2018/Algorithmica_d.pdf

Each iteration uniformly flips one coordinate and accepts nonincreasing Hamming
distance. Initialization is explicitly pure. Runtime integrates the first target
hit under the actual trajectory measure, preserving infinity until the bound
proves finiteness. Iterations exclude the initial evaluation.
-/

namespace ECTheoryLib.Analysis.RLSHamming

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open ECTheoryLib.Problems.TargetOneMax

noncomputable section

/-- Extended expected target-hitting time of actual Hamming-minimizing RLS
from a specified fixed state. -/
def ExpectedRuntime {n : Nat} (PositiveLength : 0 < n)
    (Target InitialState : Bits n) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength Target) (fun x => x = Target)
    (PMF.pure InitialState)

/-- Support-level zero preservation implies the almost-sure absorption
premise of the drift interface. -/
theorem StepPreservesZeroHamming {n : Nat} (PositiveLength : 0 < n)
    (Target State : Bits n) :
    ∀ᵐ Next ∂(Step PositiveLength Target State).toMeasure,
      Hamming Target State = 0 → Hamming Target Next = 0 := by
  have SupportMeasurable : MeasurableSet (Step PositiveLength Target State).support := by
    exact (Set.to_countable _).measurableSet
  have Supported : ∀ᵐ Next ∂(Step PositiveLength Target State).toMeasure,
      Next ∈ (Step PositiveLength Target State).support := by
    apply (mem_ae_iff_prob_eq_one SupportMeasurable).mpr
    exact (PMF.toMeasure_apply_eq_one_iff _ SupportMeasurable).mpr (Set.Subset.refl _)
  filter_upwards [Supported] with Next Possible
  intro ParentZero
  have ParentPotentialZero : Potential Target State = 0 :=
    Nat.cast_eq_zero.mpr ParentZero
  exact Nat.cast_eq_zero.mp
    (StepPreservesZero PositiveLength Target State Next ParentPotentialZero Possible)

/-- For positive length and initial Hamming distance `k > 0`, expected
iterations are at most `n(1 + log k)`. Algorithm drift and absorption are
discharged internally. This is the binary upper bound in the proof of
Doerr, Doerr, and Koetzing (2018), Theorem 6, after equation (1). -/
theorem FixedRuntimeUpperBound {n : Nat} (PositiveLength : 0 < n)
    (Target InitialState : Bits n) (InitialPositive : 0 < Hamming Target InitialState) :
    ExpectedRuntime PositiveLength Target InitialState ≤
      ENNReal.ofReal ((n : ℝ) * (1 + Real.log (Hamming Target InitialState : ℝ))) := by
  have LengthPositive : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr PositiveLength
  have LocalDrift : ∀ x : Bits n,
      (∫ y, (Hamming Target x : ℝ) - (Hamming Target y : ℝ)
        ∂(Step PositiveLength Target x).toMeasure) =
        (1 / (n : ℝ)) * (Hamming Target x : ℝ) := by
    intro x
    change (∫ y, Potential Target x - Potential Target y
      ∂(Step PositiveLength Target x).toMeasure) = (1 / (n : ℝ)) * Potential Target x
    rw [OneStepDrift PositiveLength Target x]
    ring
  have Bound := MultiplicativeRuntimeUpperBoundOfExactDrift
    (Step PositiveLength Target) (Hamming Target) (fun x => x = Target)
    (HammingEqZeroIffEq Target) (1 / (n : ℝ)) (one_div_pos.mpr LengthPositive)
    LocalDrift (StepPreservesZeroHamming PositiveLength Target) InitialState InitialPositive
  have BoundValue :
      (1 + Real.log (Hamming Target InitialState : ℝ)) / (1 / (n : ℝ)) =
        (n : ℝ) * (1 + Real.log (Hamming Target InitialState : ℝ)) := by
    rw [one_div, div_inv_eq_mul, mul_comm]
  rw [BoundValue] at Bound
  exact Bound

/-- An initially reached target has first hitting time zero almost surely. -/
theorem FixedHittingTimeEqZero {n : Nat} (PositiveLength : 0 < n)
    (Target InitialState : Bits n) (InitialZero : Hamming Target InitialState = 0) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength Target) (PMF.pure InitialState),
      FirstHittingTime (fun x => x = Target) Path = 0 := by
  exact FirstHittingTimeOfPureTarget (Step PositiveLength Target) (fun x => x = Target)
    InitialState ((HammingEqZeroIffEq Target InitialState).mp InitialZero)

/-- Initially successful runs have zero expected iterations; no runtime
interpretation of `log 0` is needed. -/
theorem FixedRuntimeEqZero {n : Nat} (PositiveLength : 0 < n)
    (Target InitialState : Bits n) (InitialZero : Hamming Target InitialState = 0) :
    ExpectedRuntime PositiveLength Target InitialState = 0 := by
  exact ExpectedHittingTimeOfPureTarget (Step PositiveLength Target) (fun x => x = Target)
    InitialState ((HammingEqZeroIffEq Target InitialState).mp InitialZero)

end
end ECTheoryLib.Analysis.RLSHamming
