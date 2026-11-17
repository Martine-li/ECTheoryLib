import ECTheoryLib.Problems.TargetOneMax
import ECTheoryLib.Analysis.OneMax.RLS.Drift

/-!
# RLS minimizing Hamming distance to an arbitrary binary target

`Step` is the actual existing RLS kernel with Hamming minimization as its
comparison relation.  Encoding proves its conjugacy to the existing all-ones
OneMax kernel; the integral drift theorem is reused through that conjugacy.
-/

namespace ECTheoryLib.Analysis.RLSHamming

open MeasureTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax

noncomputable section

/-- Instantiate the existing deterministic RLS update with Hamming minimization. -/
abbrev Update {n : Nat} (Target State : Bits n) (i : Fin n) : Bits n :=
  RLSUpdate (Problems.MinNotWorse (Hamming Target)) State i

/-- Instantiate the real RLS transition, rather than defining an encoded algorithm. -/
def Step {n : Nat} (PositiveLength : 0 < n) (Target : Bits n) :
    Transition (Bits n) :=
  RLSStep PositiveLength (Problems.MinNotWorse (Hamming Target))

/-- The natural Hamming count represented as a real potential. -/
def Potential {n : Nat} (Target State : Bits n) : ℝ :=
  (Hamming Target State : ℝ)

theorem HammingEqZeroCount {n : Nat} (Target State : Bits n) :
    Hamming Target State = RLSOnOneMax.ZeroCount (Encode Target State) := by
  exact HammingEqLengthSubOneMax Target State

theorem PotentialEqEncodedPotential {n : Nat} (Target State : Bits n) :
    Potential Target State = RLSOnOneMax.Potential (Encode Target State) := by
  unfold Potential RLSOnOneMax.Potential
  rw [HammingEqZeroCount]

theorem PotentialNonnegative {n : Nat} (Target State : Bits n) :
    0 ≤ Potential Target State := by
  exact Nat.cast_nonneg _

theorem PotentialLeLength {n : Nat} (Target State : Bits n) :
    Potential Target State ≤ (n : ℝ) := by
  exact Nat.cast_le.mpr (HammingLeLength Target State)

theorem PotentialEqZeroIffEq {n : Nat} (Target State : Bits n) :
    Potential Target State = 0 ↔ State = Target := by
  unfold Potential
  rw [Nat.cast_eq_zero, HammingEqZeroIffEq]

/-- Encoding commutes with the existing one-bit mutation operator. -/
theorem EncodeMutation {n : Nat} (Target State : Bits n) (i : Fin n) :
    Encode Target (OnebitMutation State i) =
      OnebitMutation (Encode Target State) i := by
  funext j
  by_cases SamePosition : j = i
  · subst j
    rw [OnebitMutationAt]
    unfold Encode
    rw [OnebitMutationAt]
    cases State i with
    | false =>
        cases Target i with
        | false => rfl
        | true => rfl
    | true =>
        cases Target i with
        | false => rfl
        | true => rfl
  · change decide (OnebitMutation State i j = Target j) =
      OnebitMutation (Encode Target State) i j
    rw [OnebitMutationAway State i j SamePosition]
    rw [OnebitMutationAway (Encode Target State) i j SamePosition]
    rfl

/-- The real Hamming selection rule conjugates to OneMax maximization. -/
theorem EncodeSelection {n : Nat} (Target Parent Candidate : Bits n) :
    Encode Target
      (ElitistSelect (Problems.MinNotWorse (Hamming Target)) Parent Candidate) =
      ElitistSelect (Problems.MaxNotWorse OneMax)
        (Encode Target Parent) (Encode Target Candidate) := by
  have SameComparison := MinNotWorseIffEncodedMaxNotWorse Target Candidate Parent
  by_cases Accept : Problems.MinNotWorse (Hamming Target) Candidate Parent
  · have EncodedAccept := SameComparison.mp Accept
    rw [ElitistSelectAccept _ _ _ Accept,
      ElitistSelectAccept _ _ _ EncodedAccept]
  · have EncodedReject :
        ¬ Problems.MaxNotWorse OneMax (Encode Target Candidate) (Encode Target Parent) := by
      intro EncodedAccept
      exact Accept (SameComparison.mpr EncodedAccept)
    rw [ElitistSelectReject _ _ _ Accept,
      ElitistSelectReject _ _ _ EncodedReject]

/-- Full mutation-and-selection updates commute with encoding. -/
theorem EncodeUpdate {n : Nat} (Target State : Bits n) (i : Fin n) :
    Encode Target (Update Target State i) =
      RLSOnOneMax.Update (Encode Target State) i := by
  unfold Update RLSUpdate
  rw [EncodeSelection, EncodeMutation]
  rfl

/-- Push the real Hamming kernel through encoding to obtain the old OneMax kernel. -/
theorem EncodeStep {n : Nat} (PositiveLength : 0 < n) (Target State : Bits n) :
    (Step PositiveLength Target State).map (Encode Target) =
      RLSOnOneMax.Step PositiveLength (Encode Target State) := by
  rw [Step, RLSStepEqUniformUpdate, PMF.map_comp]
  rw [RLSOnOneMax.Step, RLSStepEqUniformUpdate]
  apply congrArg (fun UpdateFunction : Fin n → Bits n =>
    (UniformBitIndex n PositiveLength).map UpdateFunction)
  funext i
  exact EncodeUpdate Target State i

/-- The integral one-step decrease is exactly the number of wrong bits divided by n. -/
theorem OneStepDrift {n : Nat} (PositiveLength : 0 < n) (Target State : Bits n) :
    (∫ Next, Potential Target State - Potential Target Next
      ∂(Step PositiveLength Target State).toMeasure) =
      Potential Target State / (n : ℝ) := by
  have EncodedDrift := RLSOnOneMax.OneStepDrift PositiveLength (Encode Target State)
  rw [← EncodeStep PositiveLength Target State] at EncodedDrift
  rw [← PMF.toMeasure_map (Encode Target) (Step PositiveLength Target State)
    (measurable_of_finite (Encode Target))] at EncodedDrift
  rw [integral_map_of_stronglyMeasurable (measurable_of_finite (Encode Target))
    (measurable_of_finite
      (fun Next : Bits n => RLSOnOneMax.Potential (Encode Target State) -
        RLSOnOneMax.Potential Next)).stronglyMeasurable] at EncodedDrift
  simp_rw [← PotentialEqEncodedPotential] at EncodedDrift
  exact EncodedDrift

theorem ExpectedDecreaseEqPotentialDivLength {n : Nat}
    (PositiveLength : 0 < n) (Target State : Bits n) :
    ExpectedDecrease (Step PositiveLength Target) (Potential Target) State =
      Potential Target State / (n : ℝ) := by
  have IntegralDrift := OneStepDrift PositiveLength Target State
  rw [PMF.integral_eq_sum] at IntegralDrift
  exact IntegralDrift

/-- Any possible deterministic update preserves zero Hamming potential. -/
theorem UpdatePreservesZero {n : Nat} (Target State : Bits n) (i : Fin n)
    (ParentZero : Potential Target State = 0) :
    Potential Target (Update Target State i) = 0 := by
  rw [PotentialEqEncodedPotential, EncodeUpdate]
  apply RLSOnOneMax.UpdatePreservesZero
  rw [← PotentialEqEncodedPotential]
  exact ParentZero

/-- Zero absorption is verified on the support of the actual Hamming RLS kernel. -/
theorem StepPreservesZero {n : Nat} (PositiveLength : 0 < n)
    (Target State Next : Bits n) (ParentZero : Potential Target State = 0)
    (Possible : Next ∈ (Step PositiveLength Target State).support) :
    Potential Target Next = 0 := by
  rw [Step, RLSStepEqUniformUpdate] at Possible
  obtain ⟨i, _IndexPossible, NextEqualsUpdate⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← NextEqualsUpdate]
  exact UpdatePreservesZero Target State i ParentZero

end
end ECTheoryLib.Analysis.RLSHamming
