import ECTheoryLib.SearchSpaces.BitString
import ECTheoryLib.Problems.Basic
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# OneMax maximization

The objective counts one bits. The optimum is `n`, uniquely attained by
`AllOnes n`, including `n = 0`. The results describe the problem independently
of any algorithm or stopping rule.
-/

namespace ECTheoryLib

/-- The number of true coordinates in a binary string. -/
def OneMax {n : Nat} (x : Bits n) : Nat :=
  ∑ i : Fin n, if x i then 1 else 0

namespace Problems.OneMax

/-- Global OneMax optimality among all strings of the same length. -/
def IsOptimal {n : Nat} (x : Bits n) : Prop :=
  IsMaximizer OneMax x


private theorem BitContributionLeOne (b : Bool) :
    (if b then 1 else 0 : Nat) ≤ 1 := by
  cases b with
  | false =>
      change (0 : Nat) ≤ 1
      exact Nat.zero_le 1
  | true =>
      change (1 : Nat) ≤ 1
      exact Nat.le_refl 1

private theorem SumOfOnes (n : Nat) : (∑ _i : Fin n, (1 : Nat)) = n := by
  
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [Fintype.card_fin]
  
  rw [Nat.nsmul_eq_mul]
  rw [Nat.mul_one]

/-- No length-`n` string contains more than `n` one bits. -/
theorem OneMaxLeN {n : Nat} (x : Bits n) : OneMax x ≤ n := by
  have SumBound : OneMax x ≤ ∑ _i : Fin n, (1 : Nat) := by
    unfold OneMax
    apply Finset.sum_le_sum
    intro i _Membership
    exact BitContributionLeOne (x i)
  rw [SumOfOnes] at SumBound
  exact SumBound

/-- The all-ones string attains the objective upper bound. -/
@[simp] theorem OneMaxAllOnes {n : Nat} : OneMax (AllOnes n) = n := by
  
  unfold OneMax
  
  change (∑ _i : Fin n, (1 : Nat)) = n
  exact SumOfOnes n

/-- A string has objective value `n` exactly when all its bits are one. -/
theorem OneMaxEqNIffEqAllOnes {n : Nat} (x : Bits n) :
    OneMax x = n ↔ x = AllOnes n := by
  constructor
  · intro ValueEqualsN
    have EachContributionBound (i : Fin n) (_Membership : i ∈ Finset.univ) :
        (if x i then 1 else 0 : Nat) ≤ 1 := by
      exact BitContributionLeOne (x i)

    have EqualSums :
        (∑ i : Fin n, (if x i then 1 else 0 : Nat)) = ∑ _i : Fin n, (1 : Nat) := by
      change OneMax x = ∑ _i : Fin n, (1 : Nat)
      rw [SumOfOnes]
      exact ValueEqualsN

    -- Equality in the sum bound forces every coordinate contribution to be one.
    have EveryContributionIsOne :
        ∀ i ∈ (Finset.univ : Finset (Fin n)), (if x i then 1 else 0 : Nat) = 1 := by
      apply (Finset.sum_eq_sum_iff_of_le EachContributionBound).mp
      exact EqualSums

    
    funext i
    have ContributionIsOne : (if x i then 1 else 0 : Nat) = 1 := by
      exact EveryContributionIsOne i (Finset.mem_univ i)
    change x i = true
    cases BitValue : x i with
    | false =>
        rw [BitValue] at ContributionIsOne
        change (0 : Nat) = 1 at ContributionIsOne
        
        exact False.elim (Nat.zero_ne_one ContributionIsOne)
    | true =>
        rfl
  · intro StringEqualsAllOnes
    rw [StringEqualsAllOnes]
    exact OneMaxAllOnes

/-- The all-ones string is the unique OneMax maximizer. -/
theorem IsOptimalIffEqAllOnes {n : Nat} (x : Bits n) :
    IsOptimal x ↔ x = AllOnes n := by
  constructor
  · intro Optimal
    have UpperBound : OneMax x ≤ n := by
      exact OneMaxLeN x
    have AtLeastAllOnes : OneMax (AllOnes n) ≤ OneMax x := by
      
      unfold IsOptimal IsMaximizer at Optimal
      exact Optimal (AllOnes n)
    have LowerBound : n ≤ OneMax x := by
      rw [OneMaxAllOnes] at AtLeastAllOnes
      exact AtLeastAllOnes
    have ValueEqualsN : OneMax x = n := by
      exact Nat.le_antisymm UpperBound LowerBound
    exact (OneMaxEqNIffEqAllOnes x).mp ValueEqualsN
  · intro StringEqualsAllOnes
    unfold IsOptimal IsMaximizer
    intro y
    rw [StringEqualsAllOnes]
    rw [OneMaxAllOnes]
    exact OneMaxLeN y

/-- Number of zero bits; the objective bound makes subtraction exact. -/
def ZeroCount {n : Nat} (x : Bits n) : Nat := n - OneMax x

/-- Zero count vanishes exactly at the unique OneMax optimum. -/
theorem ZeroCountEqZeroIffAllOnes {n : Nat} (x : Bits n) :
    ZeroCount x = 0 ↔ x = AllOnes n := by
  unfold ZeroCount
  rw [Nat.sub_eq_zero_iff_le]
  constructor
  · intro LowerBound
    exact (OneMaxEqNIffEqAllOnes x).mp (Nat.le_antisymm (OneMaxLeN x) LowerBound)
  · intro AtOptimum
    rw [AtOptimum, OneMaxAllOnes]

/-- The bound `OneMax x ≤ n` identifies natural zero count with the
ordinary real difference `n - OneMax x`. -/
theorem ZeroCountAsRealDifference {n : Nat} (x : Bits n) :
    (ZeroCount x : ℝ) = (n : ℝ) - (OneMax x : ℝ) := by
  unfold ZeroCount
  exact Nat.cast_sub (OneMaxLeN x)

/-- Summing zero-coordinate indicators gives `n - OneMax x`. -/
theorem ZeroBitCount {n : Nat} (x : Bits n) :
    (∑ i : Fin n, if x i then (0 : Nat) else 1) = n - OneMax x := by
  have ComplementCount :
      OneMax x + (∑ i : Fin n, if x i then (0 : Nat) else 1) = n := by
    unfold OneMax
    rw [← Finset.sum_add_distrib]
    have EachPositionContributesOne :
        (∑ i : Fin n, ((if x i then 1 else 0) + (if x i then 0 else 1))) =
          ∑ _i : Fin n, (1 : Nat) := by
      apply Finset.sum_congr rfl
      intro i _Membership
      cases x i with
      | false => rfl
      | true => rfl
    rw [EachPositionContributesOne]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.nsmul_eq_mul, Nat.mul_one]
  omega

/-- The real sum of zero-coordinate indicators equals the real zero count. -/
theorem ZeroBitCountAsReal {n : Nat} (x : Bits n) :
    (∑ i : Fin n, if x i then (0 : ℝ) else 1) =
      (ZeroCount x : ℝ) := by
  have CastSum :
      (∑ i : Fin n, if x i then (0 : ℝ) else 1) =
        ((∑ i : Fin n, if x i then (0 : Nat) else 1 : Nat) : ℝ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _Membership
    cases x i with
    | false =>
        change (1 : ℝ) = ((1 : Nat) : ℝ)
        exact Nat.cast_one.symm
    | true =>
        change (0 : ℝ) = ((0 : Nat) : ℝ)
        exact Nat.cast_zero.symm
  rw [CastSum, ZeroBitCount]
  rfl

end Problems.OneMax
end ECTheoryLib
