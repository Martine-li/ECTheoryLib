import ECTheoryLib.Analysis.OneMax.RLS.RuntimeBounds
import ECTheoryLib.Analysis.TargetOneMax.RLS.ExactRuntime

/-!
# Exact RLS runtime through the OneMax interface

For the all-ones target, the actual Hamming-minimizing kernel equals the existing
OneMax-maximizing kernel. This module proves equivalence of the encoding, kernels,
goals, and expectations, then reuses the arbitrary-target exact formula.
Time counts mutations after initialization, including zero for initial success.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open ECTheoryLib.Probability ECTheoryLib.Problems.TargetOneMax

noncomputable section

/-- Matching against the all-ones target leaves each bit string unchanged. -/
theorem EncodeAllOnes {n : Nat} (State : Bits n) :
    Encode (AllOnes n) State = State := by
  funext i
  unfold Encode AllOnes
  cases State i with
  | false => rfl
  | true => rfl

/-- Hamming distance to all ones equals the zero count in the OneMax interface. -/
theorem HammingAllOnesEqZeroCount {n : Nat} (State : Bits n) :
    Hamming (AllOnes n) State = ZeroCount State := by
  rw [RLSHamming.HammingEqZeroCount, EncodeAllOnes]

/-- The all-ones specialization of the arbitrary-target kernel equals
the actual OneMax RLS kernel. -/
theorem StepEqHammingAllOnes {n : Nat} (PositiveLength : 0 < n) :
    Step PositiveLength = RLSHamming.Step PositiveLength (AllOnes n) := by
  funext State
  have EncodingIsIdentity : (Encode (AllOnes n) : Bits n → Bits n) = id := by
    funext x
    exact EncodeAllOnes x
  have EncodedKernel := RLSHamming.EncodeStep PositiveLength (AllOnes n) State
  rw [EncodingIsIdentity, PMF.map_id] at EncodedKernel
  exact EncodedKernel.symm

/-- The original goal and the all-ones Hamming goal yield the same
expected first hitting time under the actual trajectory law. -/
theorem ExpectedRuntimeEqHammingAllOnes {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) :
    ExpectedRuntime PositiveLength InitialState =
      RLSHamming.ExpectedRuntime PositiveLength (AllOnes n) InitialState := by
  have GoalEquality : (IsTarget (n := n)) = (fun x : Bits n => x = AllOnes n) := by
    funext x
    exact propext (IsTargetIffEqAllOnes x)
  unfold ExpectedRuntime RLSHamming.ExpectedRuntime
  rw [StepEqHammingAllOnes PositiveLength, GoalEquality]

/-- Every fixed initial state has exact expected runtime `n H_k`, where
`k` is its zero count, including zero iterations when `k=0`. This is the
all-ones specialization of Doerr, Doerr, and Koetzing (2018), Theorem 6. -/
theorem FixedRuntimeExact {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) :
    ExpectedRuntime PositiveLength InitialState =
      ENNReal.ofReal ((n : ℝ) * (harmonic (ZeroCount InitialState) : ℝ)) := by
  have Exact := RLSHamming.FixedRuntimeExact PositiveLength (AllOnes n) InitialState
  rw [HammingAllOnesEqZeroCount] at Exact
  rw [ExpectedRuntimeEqHammingAllOnes PositiveLength InitialState]
  exact Exact

end
end ECTheoryLib.Analysis.RLSOnOneMax
