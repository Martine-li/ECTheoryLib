import ECTheoryLib.SearchSpaces.BitString
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Independent bit mutation

Each bit changes independently with probability `Rate`. The point probability is
the product of its coordinate probabilities, so normalization is proved rather
than assumed. Standard bit mutation uses `Rate = 1 / n`, with `n > 0`.
-/

namespace ECTheoryLib

noncomputable section

/-- Probability of one output bit, conditional on the corresponding input bit. -/
def BitMutationProbability (Rate : ENNReal) (Parent Candidate : Bool) : ENNReal :=
  if Candidate = Parent then 1 - Rate else Rate

theorem BitMutationProbabilitySum (Rate : ENNReal) (RateBound : Rate ≤ 1)
    (Parent : Bool) : ∑ Candidate : Bool, BitMutationProbability Rate Parent Candidate = 1 := by
  cases Parent with
  | false =>
      rw [Fintype.sum_bool]
      change Rate + (1 - Rate) = 1
      rw [add_comm]
      exact tsub_add_cancel_of_le RateBound
  | true =>
      rw [Fintype.sum_bool]
      change (1 - Rate) + Rate = 1
      exact tsub_add_cancel_of_le RateBound

/-- Joint probability of an offspring: product over all independently mutated bits. -/
def IndependentBitMutationWeight {n : Nat} (Rate : ENNReal)
    (Parent Candidate : Bits n) : ENNReal :=
  ∏ i : Fin n, BitMutationProbability Rate (Parent i) (Candidate i)

theorem IndependentBitMutationWeightSum {n : Nat} (Rate : ENNReal)
    (RateBound : Rate ≤ 1) (Parent : Bits n) :
    ∑ Candidate : Bits n, IndependentBitMutationWeight Rate Parent Candidate = 1 := by
  unfold IndependentBitMutationWeight
  rw [← Fintype.prod_sum]
  have CoordinateSums : ∀ i : Fin n,
      (∑ Candidate : Bool, BitMutationProbability Rate (Parent i) Candidate) = 1 := by
    intro i
    exact BitMutationProbabilitySum Rate RateBound (Parent i)
  simp only [CoordinateSums, Finset.prod_const_one]

/-- A normalized PMF for independent mutation of every coordinate. -/
def IndependentBitMutation {n : Nat} (Rate : ENNReal) (RateBound : Rate ≤ 1)
    (Parent : Bits n) : PMF (Bits n) :=
  PMF.ofFintype (IndependentBitMutationWeight Rate Parent)
    (IndependentBitMutationWeightSum Rate RateBound Parent)

theorem IndependentBitMutationProbability {n : Nat} (Rate : ENNReal)
    (RateBound : Rate ≤ 1) (Parent Candidate : Bits n) :
    IndependentBitMutation Rate RateBound Parent Candidate =
      ∏ i : Fin n, BitMutationProbability Rate (Parent i) (Candidate i) := by
  rfl

/-- An offspring is possible exactly when every coordinate has positive probability. -/
theorem IndependentBitMutationSupport {n : Nat} (Rate : ENNReal)
    (RateBound : Rate ≤ 1) (Parent Candidate : Bits n) :
    Candidate ∈ (IndependentBitMutation Rate RateBound Parent).support ↔
      ∀ i : Fin n, BitMutationProbability Rate (Parent i) (Candidate i) ≠ 0 := by
  rw [PMF.mem_support_iff, IndependentBitMutationProbability]
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro EveryCoordinate i
    exact EveryCoordinate i (Finset.mem_univ i)
  · intro EveryCoordinate i _Membership
    exact EveryCoordinate i

theorem StandardBitMutationRateBound (n : Nat) (PositiveLength : 0 < n) :
    (n : ENNReal)⁻¹ ≤ 1 := by
  apply ENNReal.inv_le_one.mpr
  have LengthAtLeastOne : 1 ≤ n := PositiveLength
  exact_mod_cast LengthAtLeastOne

/-- Standard bit mutation flips each coordinate independently with probability `1 / n`.
For `n = 1` it always flips the unique bit; otherwise an unchanged offspring is possible. -/
def StandardBitMutation {n : Nat} (PositiveLength : 0 < n)
    (Parent : Bits n) : PMF (Bits n) :=
  IndependentBitMutation (n : ENNReal)⁻¹
    (StandardBitMutationRateBound n PositiveLength) Parent

theorem StandardBitMutationProbability {n : Nat} (PositiveLength : 0 < n)
    (Parent Candidate : Bits n) :
    StandardBitMutation PositiveLength Parent Candidate =
      ∏ i : Fin n,
        if Candidate i = Parent i then 1 - (n : ENNReal)⁻¹ else (n : ENNReal)⁻¹ := by
  rfl

end
end ECTheoryLib
