import ECTheoryLib.Problems.OneMax
import ECTheoryLib.Operators.Mutation.BitFlip

/-!
# OneMax under a single bit flip

Objective identities shared by RLS, EA, Jump, and archive analyses.
No algorithm or runtime theorem is used here.
-/
namespace ECTheoryLib.Analysis.OneMax

/-- Flipping a zero to one increases OneMax by one. -/
theorem OneMaxMutationAtZero {n : Nat}
    (x : Bits n) (i : Fin n) (BitIsZero : x i = false) :
    OneMax (OnebitMutation x i) = OneMax x + 1 := by
  have SplitAt (y : Bits n) :
      OneMax y = (if y i then 1 else 0) +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, (if y j then 1 else 0) := by
    unfold OneMax
    symm
    apply Finset.add_sum_erase (a := i)
    exact Finset.mem_univ i

  have SelectedBitBecomesOne : OnebitMutation x i i = true := by
    calc
      OnebitMutation x i i = !(x i) := by
        unfold OnebitMutation
        rw [if_pos rfl]
      _ = !false := by
        rw [BitIsZero]
      _ = true := by
        rfl

  have OtherBitsUnchanged :
      ∀ j : Fin n, j ≠ i → OnebitMutation x i j = x j := by
    intro j DifferentPosition
    unfold OnebitMutation
    rw [if_neg DifferentPosition]
  have OtherContributionsUnchanged :
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        (if OnebitMutation x i j then 1 else 0 : Nat)) =
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        (if x j then 1 else 0 : Nat) := by
    apply Finset.sum_congr rfl
    intro j Membership
    have DifferentPosition : j ≠ i := by
      exact (Finset.mem_erase.mp Membership).1
    rw [OtherBitsUnchanged j DifferentPosition]

  rw [SplitAt (OnebitMutation x i), SplitAt x]
  rw [SelectedBitBecomesOne, BitIsZero]
  change
    1 + (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      (if OnebitMutation x i j then 1 else 0 : Nat)) =
    (0 + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      (if x j then 1 else 0 : Nat)) + 1
  rw [OtherContributionsUnchanged, Nat.zero_add]
  exact Nat.add_comm 1 _

/-- Flipping a one to zero decreases OneMax by one. The additive equation
avoids truncated subtraction on natural numbers. -/
theorem OneMaxMutationAtOne {n : Nat}
    (x : Bits n) (i : Fin n) (BitIsOne : x i = true) :
    OneMax (OnebitMutation x i) + 1 = OneMax x := by
  have MutatedBitIsZero : OnebitMutation x i i = false := by
    unfold OnebitMutation
    rw [if_pos rfl, BitIsOne]
    rfl
  have ReverseIncrease :
      OneMax (OnebitMutation (OnebitMutation x i) i) = OneMax (OnebitMutation x i) + 1 := by
    exact OneMaxMutationAtZero (OnebitMutation x i) i MutatedBitIsZero
  rw [OnebitMutationTwice] at ReverseIncrease
  exact ReverseIncrease.symm

end ECTheoryLib.Analysis.OneMax
