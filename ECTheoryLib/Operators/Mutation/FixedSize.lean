import ECTheoryLib.Probability.Sampling.UniformSubset
import ECTheoryLib.Operators.Mutation.OneBit

/-!
# Exactly k uniformly chosen bit flips

Choose a uniform k-element subset, flip its distinct positions once, and
retain the actual PMF. Every proposal differs in exactly k coordinates.
The k=0 law is pure and the k=1 law equals the established one-bit mutation.
-/

namespace ECTheoryLib
open MeasureTheory Set
noncomputable section

/-- Flip each position in a finite set once. A set has no repeated coordinates. -/
def FlipBitSubset {n : ℕ} (Parent : Bits n) (Positions : Finset (Fin n)) : Bits n :=
  fun i => if i∈Positions then !(Parent i) else Parent i

theorem FlipBitSubsetChanged {n : ℕ} (Parent : Bits n) (Positions : Finset (Fin n)) (i : Fin n) :
    FlipBitSubset Parent Positions i ≠ Parent i ↔ i∈Positions := by
  by_cases Inside : i∈Positions <;> cases Bit : Parent i <;> simp [FlipBitSubset,Inside,Bit]

theorem FlipBitSubsetEmpty {n : ℕ} (Parent : Bits n) : FlipBitSubset Parent ∅=Parent := by
  funext i
  simp [FlipBitSubset]

/-- Deterministic singleton compatibility with the established one-bit operator. -/
theorem FlipBitSubsetSingleton {n : ℕ} (Parent : Bits n) (i : Fin n) :
    FlipBitSubset Parent {i}=OnebitMutation Parent i := by
  funext j
  simp [FlipBitSubset,OnebitMutation]

theorem FlipBitSubsetTwice {n : ℕ} (Parent : Bits n) (Positions : Finset (Fin n)) :
    FlipBitSubset (FlipBitSubset Parent Positions) Positions=Parent := by
  funext i
  by_cases Inside : i∈Positions <;> simp [FlipBitSubset,Inside]

/-- Uniformly choose exactly k distinct positions and flip them. The zero-size
proposal, including the empty search space, is valid and leaves the parent unchanged. -/
def FixedSizeBitMutation {n k : ℕ} (Admissible : k≤n) (Parent : Bits n) : PMF (Bits n) :=
  (Probability.UniformSubset.Law n k Admissible).map (FlipBitSubset Parent)

/-- Distance restricted to a specified region. Repeated observations are counted
with their multiplicity; concentration results separately require injectivity. -/
def ObservedBitDifference {n m : ℕ} (Observed : Fin m → Fin n) (Parent Child : Bits n) : ℕ :=
  ∑ j : Fin m, if Child (Observed j) ≠ Parent (Observed j) then 1 else 0

theorem ObservedBitDifferenceSelf {n m : ℕ} (Observed : Fin m → Fin n) (Parent : Bits n) :
    ObservedBitDifference Observed Parent Parent=0 := by
  simp [ObservedBitDifference]

theorem ObservedBitDifferenceFlip {n m : ℕ} (Observed : Fin m → Fin n) (Parent : Bits n)
    (Positions : Finset (Fin n)) :
    ObservedBitDifference Observed Parent (FlipBitSubset Parent Positions)=
      Probability.UniformSubset.ObservedCount Observed Positions := by
  simp only [ObservedBitDifference,Probability.UniformSubset.ObservedCount,FlipBitSubsetChanged]

end
end ECTheoryLib

namespace ECTheoryLib
open MeasureTheory Set
noncomputable section

theorem FixedSizeBitMutationZero {n : ℕ} (Parent : Bits n) :
    FixedSizeBitMutation (Nat.zero_le n) Parent=PMF.pure Parent := by
  have Law : Probability.UniformSubset.Law n 0 (Nat.zero_le n)=PMF.pure ∅ := by
    ext U
    simp [Probability.UniformSubset.Law,PMF.uniformOfFinset_apply,PMF.pure_apply]
  unfold FixedSizeBitMutation
  rw [Law,PMF.pure_map,FlipBitSubsetEmpty]

/-- Choosing one position without replacement is exactly the existing RLS proposal law. -/
theorem FixedSizeBitMutationOne {n : ℕ} (PositiveLength : 0<n) (Parent : Bits n) :
    FixedSizeBitMutation PositiveLength Parent=RandomOneBitMutation PositiveLength Parent := by
  classical
  have Law : Probability.UniformSubset.Law n 1 PositiveLength=
      (UniformBitIndex n PositiveLength).map (fun i => ({i} : Finset (Fin n))) := by
    ext U
    rw [PMF.map_apply]
    by_cases Singleton : U.card=1
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp Singleton
      rw [tsum_eq_single i]
      · simp [Probability.UniformSubset.Law,PMF.uniformOfFinset_apply]
      · intro j Different
        have NotSame : ({i} : Finset (Fin n))≠{j} := by
          intro Same
          exact Different (Finset.singleton_injective Same).symm
        simp only [if_neg NotSame]
    · trans (∑' _i : Fin n, (0 : ENNReal))
      · simp [Probability.UniformSubset.Law,PMF.uniformOfFinset_apply,Singleton]
      · apply tsum_congr
        intro i
        split_ifs with Same
        · exact False.elim (Singleton (by simp [Same]))
        · rfl
  unfold FixedSizeBitMutation RandomOneBitMutation
  rw [Law,PMF.map_comp]
  congr 1
  funext i
  exact FlipBitSubsetSingleton Parent i

end
end ECTheoryLib

namespace ECTheoryLib
open MeasureTheory Set
noncomputable section

theorem ObservedBitDifferenceAllFlip {n : ℕ} (Parent : Bits n) (Positions : Finset (Fin n)) :
    ObservedBitDifference id Parent (FlipBitSubset Parent Positions)=Positions.card := by
  rw [ObservedBitDifferenceFlip]
  simp [Probability.UniformSubset.ObservedCount]

/-- Every possible proposal differs at exactly k coordinates. This is a
support statement about the actual PMF, not just an expected distance. -/
theorem FixedSizeBitMutationDistance {n k : ℕ} (Admissible : k≤n) (Parent Child : Bits n)
    (Possible : Child∈(FixedSizeBitMutation Admissible Parent).support) :
    ObservedBitDifference id Parent Child=k := by
  obtain ⟨Positions,Supported,Equal⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← Equal,ObservedBitDifferenceAllFlip]
  exact (Probability.UniformSubset.Support Admissible Positions).mp Supported

end
end ECTheoryLib
