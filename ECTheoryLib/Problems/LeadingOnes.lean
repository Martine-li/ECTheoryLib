import ECTheoryLib.Problems.OneMax
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# LeadingOnes and trailing zeroes

`LeadingOnes` is the greatest length of a prefix consisting entirely of ones.
`TrailingZeroes` is the greatest length of a suffix consisting entirely of zeroes.
The finite maximum definition is executable and includes the empty string.
-/

namespace ECTheoryLib

/-- The first `Length` positions contain only ones. -/
def HasOnePrefix {n : Nat} (x : Bits n) (Length : Nat) : Prop :=
  ∀ i : Fin n, i.val < Length → x i = true

/-- The last `Length` positions contain only zeroes. -/
def HasZeroSuffix {n : Nat} (x : Bits n) (Length : Nat) : Prop :=
  ∀ i : Fin n, n - Length ≤ i.val → x i = false

instance {n : Nat} (x : Bits n) (Length : Nat) : Decidable (HasOnePrefix x Length) :=
  inferInstanceAs (Decidable (∀ i : Fin n, i.val < Length → x i = true))

instance {n : Nat} (x : Bits n) (Length : Nat) : Decidable (HasZeroSuffix x Length) :=
  inferInstanceAs (Decidable (∀ i : Fin n, n - Length ≤ i.val → x i = false))

/-- Length of the longest all-one prefix, between zero and n inclusive. -/
def LeadingOnes {n : Nat} (x : Bits n) : Nat :=
  ((Finset.range (n + 1)).filter (HasOnePrefix x)).sup id

/-- Length of the longest all-zero suffix, between zero and n inclusive. -/
def TrailingZeroes {n : Nat} (x : Bits n) : Nat :=
  ((Finset.range (n + 1)).filter (HasZeroSuffix x)).sup id

/-- Canonical Pareto point: `Length` leading ones followed by zeroes. -/
def PrefixOnes (n Length : Nat) : Bits n :=
  fun i => decide (i.val < Length)

namespace Problems.LeadingOnes

theorem LeadingOnesLeN {n : Nat} (x : Bits n) : LeadingOnes x ≤ n := by
  unfold LeadingOnes
  apply Finset.sup_le
  intro Length Membership
  have InRange : Length < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp Membership).1
  change Length ≤ n
  omega

theorem TrailingZeroesLeN {n : Nat} (x : Bits n) : TrailingZeroes x ≤ n := by
  unfold TrailingZeroes
  apply Finset.sup_le
  intro Length Membership
  have InRange : Length < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp Membership).1
  change Length ≤ n
  omega

theorem PrefixLeLeadingOnes {n Length : Nat} (x : Bits n)
    (LengthBound : Length ≤ n) (Prefix : HasOnePrefix x Length) :
    Length ≤ LeadingOnes x := by
  unfold LeadingOnes
  apply Finset.le_sup (f := id) (b := Length)
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    omega
  · exact Prefix

theorem SuffixLeTrailingZeroes {n Length : Nat} (x : Bits n)
    (LengthBound : Length ≤ n) (Suffix : HasZeroSuffix x Length) :
    Length ≤ TrailingZeroes x := by
  unfold TrailingZeroes
  apply Finset.le_sup (f := id) (b := Length)
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    omega
  · exact Suffix

theorem HasLeadingOnesPrefix {n : Nat} (x : Bits n) : HasOnePrefix x (LeadingOnes x) := by
  have ZeroMember : 0 ∈ (Finset.range (n + 1)).filter (HasOnePrefix x) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.zero_lt_succ n)
    · intro i Impossible
      omega
  have MaximumMember := Finset.sup_mem_of_nonempty (f := id) ⟨0, ZeroMember⟩
  obtain ⟨Length, Membership, MaximumEqualsLength⟩ := MaximumMember
  have Prefix := (Finset.mem_filter.mp Membership).2
  unfold LeadingOnes
  rw [← MaximumEqualsLength]
  exact Prefix

theorem HasTrailingZeroesSuffix {n : Nat} (x : Bits n) : HasZeroSuffix x (TrailingZeroes x) := by
  have ZeroMember : 0 ∈ (Finset.range (n + 1)).filter (HasZeroSuffix x) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.zero_lt_succ n)
    · intro i Impossible
      have IndexBound := i.isLt
      omega
  have MaximumMember := Finset.sup_mem_of_nonempty (f := id) ⟨0, ZeroMember⟩
  obtain ⟨Length, Membership, MaximumEqualsLength⟩ := MaximumMember
  have Suffix := (Finset.mem_filter.mp Membership).2
  unfold TrailingZeroes
  rw [← MaximumEqualsLength]
  exact Suffix

theorem LeadingOnesAllOnes {n : Nat} : LeadingOnes (AllOnes n) = n := by
  apply Nat.le_antisymm (LeadingOnesLeN _)
  apply PrefixLeLeadingOnes _ (Nat.le_refl n)
  intro i _IndexBound
  rfl

theorem LeadingOnesEqNIffEqAllOnes {n : Nat} (x : Bits n) :
    LeadingOnes x = n ↔ x = AllOnes n := by
  constructor
  · intro ValueEqualsN
    have Prefix := HasLeadingOnesPrefix x
    rw [ValueEqualsN] at Prefix
    funext i
    exact Prefix i i.isLt
  · intro EqualsAllOnes
    rw [EqualsAllOnes]
    exact LeadingOnesAllOnes

theorem IsOptimalIffEqAllOnes {n : Nat} (x : Bits n) :
    IsMaximizer LeadingOnes x ↔ x = AllOnes n := by
  constructor
  · intro Optimal
    have LowerBound := Optimal (AllOnes n)
    rw [LeadingOnesAllOnes] at LowerBound
    apply (LeadingOnesEqNIffEqAllOnes x).mp
    exact Nat.le_antisymm (LeadingOnesLeN x) LowerBound
  · intro EqualsAllOnes y
    rw [EqualsAllOnes, LeadingOnesAllOnes]
    exact LeadingOnesLeN y

theorem LeadingOnesAddTrailingZeroesLeN {n : Nat} (x : Bits n) :
    LeadingOnes x + TrailingZeroes x ≤ n := by
  have LeadingBound := LeadingOnesLeN x
  have TrailingBound := TrailingZeroesLeN x
  by_contra Overlap
  have PositiveLeading : 0 < LeadingOnes x := by omega
  let SharedIndex : Fin n := ⟨LeadingOnes x - 1, by omega⟩
  have OneAtIndex : x SharedIndex = true := by
    apply HasLeadingOnesPrefix x SharedIndex
    change LeadingOnes x - 1 < LeadingOnes x
    omega
  have ZeroAtIndex : x SharedIndex = false := by
    apply HasTrailingZeroesSuffix x SharedIndex
    change n - TrailingZeroes x ≤ LeadingOnes x - 1
    omega
  rw [OneAtIndex] at ZeroAtIndex
  cases ZeroAtIndex

theorem LeadingOnesPrefixOnes {n Length : Nat} (LengthBound : Length ≤ n) :
    LeadingOnes (PrefixOnes n Length) = Length := by
  have Prefix : HasOnePrefix (PrefixOnes n Length) Length := by
    intro i IndexBound
    exact decide_eq_true IndexBound
  apply Nat.le_antisymm
  · by_contra TooLong
    have IndexBound : Length < n := by
      have ValueBound := LeadingOnesLeN (PrefixOnes n Length)
      omega
    let FirstZero : Fin n := ⟨Length, IndexBound⟩
    have InLongPrefix : FirstZero.val < LeadingOnes (PrefixOnes n Length) := by
      change Length < LeadingOnes (PrefixOnes n Length)
      omega
    have ValueIsOne := HasLeadingOnesPrefix (PrefixOnes n Length) FirstZero InLongPrefix
    change decide (Length < Length) = true at ValueIsOne
    have ValueIsZero : decide (Length < Length) = false := decide_eq_false (Nat.lt_irrefl Length)
    rw [ValueIsZero] at ValueIsOne
    cases ValueIsOne
  · exact PrefixLeLeadingOnes _ LengthBound Prefix

theorem TrailingZeroesPrefixOnes {n Length : Nat} (LengthBound : Length ≤ n) :
    TrailingZeroes (PrefixOnes n Length) = n - Length := by
  have Suffix : HasZeroSuffix (PrefixOnes n Length) (n - Length) := by
    intro i IndexBound
    apply decide_eq_false
    omega
  have LowerBound : n - Length ≤ TrailingZeroes (PrefixOnes n Length) := by
    exact SuffixLeTrailingZeroes _ (Nat.sub_le n Length) Suffix
  have SumBound := LeadingOnesAddTrailingZeroesLeN (PrefixOnes n Length)
  rw [LeadingOnesPrefixOnes LengthBound] at SumBound
  omega

/-- The canonical prefix string also realizes every possible Hamming weight. -/
theorem OneMaxPrefixOnes {n Length : Nat} (LengthBound : Length ≤ n) :
    OneMax (PrefixOnes n Length) = Length := by
  induction n with
  | zero =>
      have LengthIsZero : Length = 0 := by omega
      subst Length
      unfold OneMax
      exact Finset.sum_empty
  | succ n InductionHypothesis =>
      by_cases FullLength : Length = n + 1
      · have CanonicalIsAllOnes : PrefixOnes (n + 1) Length = AllOnes (n + 1) := by
          funext i
          change decide (i.val < Length) = true
          apply decide_eq_true
          rw [FullLength]
          exact i.isLt
        rw [CanonicalIsAllOnes, OneMax.OneMaxAllOnes]
        exact FullLength.symm
      · have SmallerLengthBound : Length ≤ n := by omega
        have LastBitFalse : ¬ n < Length := by omega
        unfold OneMax
        rw [Fin.sum_univ_castSucc]
        change OneMax (PrefixOnes n Length) +
          (if decide (n < Length) then 1 else 0) = Length
        rw [InductionHypothesis SmallerLengthBound]
        rw [decide_eq_false LastBitFalse]
        exact Nat.add_zero Length

end Problems.LeadingOnes
end ECTheoryLib

namespace ECTheoryLib.Problems.LeadingOnes

/-- A one prefix followed by a zero determines the objective exactly. -/
theorem LeadingOnesEqOfPrefixAndZero {n : ℕ} (x : Bits n) (i : Fin n)
    (Prefix : HasOnePrefix x i.val) (Zero : x i = false) : LeadingOnes x = i.val := by
  have Lower := PrefixLeLeadingOnes x i.isLt.le Prefix
  have Upper : LeadingOnes x ≤ i.val := by
    by_contra Longer
    have AtI := HasLeadingOnesPrefix x i (by omega)
    rw [Zero] at AtI
    cases AtI
  exact le_antisymm Upper Lower

end ECTheoryLib.Problems.LeadingOnes
