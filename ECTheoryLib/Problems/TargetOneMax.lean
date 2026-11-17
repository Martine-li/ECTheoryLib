import ECTheoryLib.Problems.OneMax
import ECTheoryLib.Problems.Comparison
import Mathlib.Data.Nat.Dist

/-!
# Binary OneMax with an arbitrary target

The objective counts coordinates which disagree with the target.  The encoding
records agreement by `true`, so minimizing Hamming distance becomes maximizing
the ordinary OneMax objective.  No algorithm is imported by this problem layer.
-/

namespace ECTheoryLib.Problems.TargetOneMax

/-- The natural number of coordinates which disagree with the target. -/
def Hamming {n : Nat} (Target State : Bits n) : Nat :=
  ∑ i : Fin n, if State i = Target i then 0 else 1

/-- In the binary alphabet, Hamming count is the paper's sum of interval distances. -/
theorem HammingEqBinaryIntervalDistance {n : Nat} (Target State : Bits n) :
    Hamming Target State =
      ∑ i : Fin n, Nat.dist (Bool.toNat (State i)) (Bool.toNat (Target i)) := by
  unfold Hamming
  apply Finset.sum_congr rfl
  intro i _Membership
  cases State i with
  | false =>
      cases Target i with
      | false => rfl
      | true => rfl
  | true =>
      cases Target i with
      | false => rfl
      | true => rfl

/-- Encode agreement with the target as a one bit. -/
def Encode {n : Nat} (Target State : Bits n) : Bits n :=
  fun i => decide (State i = Target i)

theorem EncodeInvolutive {n : Nat} (Target State : Bits n) :
    Encode Target (Encode Target State) = State := by
  funext i
  unfold Encode
  cases State i with
  | false =>
      cases Target i with
      | false => rfl
      | true => rfl
  | true =>
      cases Target i with
      | false => rfl
      | true => rfl

/-- Agreement and disagreement contribute exactly one at each coordinate. -/
theorem HammingAddEncodedOneMax {n : Nat} (Target State : Bits n) :
    Hamming Target State + OneMax (Encode Target State) = n := by
  unfold Hamming OneMax
  rw [← Finset.sum_add_distrib]
  have EachContribution :
      (∑ i : Fin n, ((if State i = Target i then 0 else 1) +
        (if Encode Target State i then 1 else 0 : Nat))) =
        ∑ _i : Fin n, (1 : Nat) := by
    apply Finset.sum_congr rfl
    intro i _Membership
    by_cases Agreement : State i = Target i
    · simp only [Agreement, if_true, Encode, decide_true]
    · simp only [Agreement, if_false, Encode, decide_false, Bool.false_eq_true,
        Nat.add_zero]
  rw [EachContribution, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Nat.nsmul_eq_mul, Nat.mul_one]

theorem HammingEqLengthSubOneMax {n : Nat} (Target State : Bits n) :
    Hamming Target State = n - OneMax (Encode Target State) := by
  have Complement := HammingAddEncodedOneMax Target State
  omega

theorem HammingLeLength {n : Nat} (Target State : Bits n) :
    Hamming Target State ≤ n := by
  rw [HammingEqLengthSubOneMax]
  exact Nat.sub_le n _

theorem HammingEqZeroIffEq {n : Nat} (Target State : Bits n) :
    Hamming Target State = 0 ↔ State = Target := by
  constructor
  · intro CountZero
    have ContributionsZero :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          (if State i = Target i then 0 else 1 : Nat) = 0 := by
      apply (Finset.sum_eq_zero_iff).mp
      exact CountZero
    funext i
    have ContributionZero := ContributionsZero i (Finset.mem_univ i)
    by_contra Disagreement
    rw [if_neg Disagreement] at ContributionZero
    exact Nat.one_ne_zero ContributionZero
  · intro StateEqualsTarget
    subst State
    unfold Hamming
    simp only [if_true, Finset.sum_const_zero]

/-- Hamming minimization and encoded OneMax maximization use the same ordering. -/
theorem MinNotWorseIffEncodedMaxNotWorse {n : Nat}
    (Target Candidate Parent : Bits n) :
    MinNotWorse (Hamming Target) Candidate Parent ↔
      MaxNotWorse OneMax (Encode Target Candidate) (Encode Target Parent) := by
  unfold MinNotWorse MaxNotWorse
  rw [HammingEqLengthSubOneMax, HammingEqLengthSubOneMax]
  have CandidateBound := Problems.OneMax.OneMaxLeN (Encode Target Candidate)
  have ParentBound := Problems.OneMax.OneMaxLeN (Encode Target Parent)
  omega

end ECTheoryLib.Problems.TargetOneMax

namespace ECTheoryLib.Problems.TargetOneMax

/-- A change in the number of zero bits is bounded by the number of changed
coordinates. This is a property of the search points, independent of mutation. -/
theorem ZeroCountDifferenceLeHamming {n : ℕ} (x y : Bits n) :
    |(Problems.OneMax.ZeroCount y : ℝ)-(Problems.OneMax.ZeroCount x : ℝ)| ≤ (Hamming x y : ℝ) := by
  rw [← Problems.OneMax.ZeroBitCountAsReal, ← Problems.OneMax.ZeroBitCountAsReal,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, |(if y i then (0 : ℝ) else 1)-(if x i then 0 else 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, (if y i=x i then (0 : ℝ) else 1) := by
      apply Finset.sum_congr rfl
      intro i _Member
      cases y i with
      | false => cases x i <;> norm_num
      | true => cases x i <;> norm_num
    _ = (Hamming x y : ℝ) := by
      simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]

end ECTheoryLib.Problems.TargetOneMax
