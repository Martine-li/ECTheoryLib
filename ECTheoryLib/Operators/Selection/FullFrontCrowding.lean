import ECTheoryLib.Operators.Selection.CrowdingDistance
import ECTheoryLib.Operators.Selection.OrderedCrowding
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD

/-!
# Crowding when all population occurrences form one rank

This module connects the actual objective sorting and neighboring-gap calculation
to the ordered-block lemmas. It retains every occurrence index and the existing
index-based objective tie rule. Each represented objective value has a positive
contribution witness, and at most two witnesses per value can have positive
contribution for one objective. Applications must separately prove that the
actual rank front is the whole population.
-/
namespace ECTheoryLib.Operators.Selection
noncomputable section
variable {α : Type*} {m : ℕ}

/-- The actual objective sort applied to all occurrence indices. -/
def FullObjectiveSort (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m) :
    List (Fin Pool.length) :=
  (PopulationIndices Pool).mergeSort (fun a b => decide
    (Fitness Pool[a] i < Fitness Pool[b] i ∨ (Fitness Pool[a] i = Fitness Pool[b] i ∧ a.val ≤ b.val)))

/-- Objective values in sorted order. The default is irrelevant at valid positions. -/
def FullObjectiveValues (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m)
    (Default : Fin Pool.length) (Position : ℕ) : ℚ :=
  Fitness Pool[(FullObjectiveSort Fitness Pool i).getD Position Default] i

theorem FullObjectiveSortLength (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m) :
    (FullObjectiveSort Fitness Pool i).length = Pool.length := by
  simp only [FullObjectiveSort, List.length_mergeSort, PopulationIndices, List.length_ofFn]

/-- Every occurrence appears exactly once in the sorted index list. -/
theorem FullObjectiveSortNodup (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m) :
    (FullObjectiveSort Fitness Pool i).Nodup := by
  apply List.Nodup.mergeSort
  exact List.nodup_ofFn.mpr Function.injective_id

theorem FullObjectiveSortMember (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m)
    (j : Fin Pool.length) : j ∈ FullObjectiveSort Fitness Pool i := by
  apply List.mem_mergeSort.mpr
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- The actual sort is nondecreasing in the objective; its occurrence-index tie
rule is a lexicographic secondary key and therefore defines a total order. -/
theorem FullObjectiveSortOrdered (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m)
    (Default : Fin Pool.length) : OrderedValues Pool.length (FullObjectiveValues Fitness Pool i Default) := by
  let Key : Fin Pool.length → ℚ ×ₗ ℕ := fun j => toLex (Fitness Pool[j] i, j.val)
  let Compare := fun a b : Fin Pool.length => decide
    (Fitness Pool[a] i < Fitness Pool[b] i ∨ (Fitness Pool[a] i = Fitness Pool[b] i ∧ a.val ≤ b.val))
  have KeyIff (a b : Fin Pool.length) : Compare a b = true ↔ Key a ≤ Key b := by
    simp only [Compare, Key, decide_eq_true_eq, Prod.Lex.toLex_le_toLex]
  have Transitive : ∀ a b c, Compare a b = true → Compare b c = true → Compare a c = true := by
    intro a b c AB BC
    exact (KeyIff a c).mpr ((KeyIff a b).mp AB |>.trans ((KeyIff b c).mp BC))
  have Total : ∀ a b, (Compare a b || Compare b a) = true := by
    intro a b
    rw [Bool.or_eq_true]
    rcases le_total (Key a) (Key b) with AB | BA
    · exact Or.inl ((KeyIff a b).mpr AB)
    · exact Or.inr ((KeyIff b a).mpr BA)
  have Sorted := List.pairwise_mergeSort Transitive Total (PopulationIndices Pool)
  intro a b AB BValid
  have AValid : a < (FullObjectiveSort Fitness Pool i).length := by
    rw [FullObjectiveSortLength]
    omega
  have BValidSort : b < (FullObjectiveSort Fitness Pool i).length := by
    rw [FullObjectiveSortLength]
    exact BValid
  unfold FullObjectiveValues
  simp only [List.getD_eq_getElem _ _ AValid, List.getD_eq_getElem _ _ BValidSort]
  rcases lt_or_eq_of_le AB with Strict | Equal
  · have Ordered := List.pairwise_iff_getElem.mp Sorted a b AValid BValidSort Strict
    have Lex := (KeyIff _ _).mp Ordered
    rcases Prod.Lex.toLex_le_toLex.mp Lex with Lower | Same
    · exact Lower.le
    · exact Same.1.le
  · subst b
    exact le_rfl

/-- The actual full-front objective contribution equals the abstract ordered
contribution. Every queried neighbor is within the sorted list in the internal
branch, so its arbitrary default cannot affect this equality. -/
theorem FullObjectiveCrowdingEq (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m)
    (Default j : Fin Pool.length) :
    ObjectiveCrowding Fitness Pool (PopulationIndices Pool) i j =
      OrderedCrowding Pool.length (FullObjectiveValues Fitness Pool i Default)
        ((FullObjectiveSort Fitness Pool i).idxOf j) := by
  let Sorted := FullObjectiveSort Fitness Pool i
  have PositionValid : Sorted.idxOf j < Pool.length := by
    have Bound := List.idxOf_lt_length_iff.mpr (FullObjectiveSortMember Fitness Pool i j)
    simpa only [FullObjectiveSortLength] using Bound
  let At := fun (k : ℕ) (d : Fin Pool.length) => Fitness Pool[Sorted.getD k d] i
  change (if Sorted.idxOf j = 0 ∨ Sorted.idxOf j + 1 ≥ Sorted.length then ⊤ else
    (↑((At (Sorted.idxOf j + 1) j - At (Sorted.idxOf j - 1) j) /
      (At (Sorted.length - 1) j - At 0 j)) : WithTop ℚ)) =
    (if Sorted.idxOf j = 0 ∨ Sorted.idxOf j + 1 ≥ Pool.length then ⊤ else
    (↑((At (Sorted.idxOf j + 1) Default - At (Sorted.idxOf j - 1) Default) /
      (At (Pool.length - 1) Default - At 0 Default)) : WithTop ℚ))
  have Length : Sorted.length = Pool.length := FullObjectiveSortLength Fitness Pool i
  rw [Length]
  by_cases Boundary : Sorted.idxOf j = 0 ∨ Sorted.idxOf j + 1 ≥ Pool.length
  · rw [if_pos Boundary, if_pos Boundary]
  · rw [if_neg Boundary, if_neg Boundary]
    have Same (k : ℕ) (Valid : k < Pool.length) : At k j = At k Default := by
      have InSort : k < Sorted.length := by rw [FullObjectiveSortLength]; exact Valid
      simp only [At, List.getD_eq_getElem _ _ InSort]
    rw [Same (Sorted.idxOf j + 1) (by omega), Same (Sorted.idxOf j - 1) (by omega),
      Same (Pool.length - 1) (by omega), Same 0 (by omega)]

/-- Every objective contribution is nonnegative when its rank front is the whole population. -/
theorem FullObjectiveCrowdingNonnegative (Fitness : α → Fin m → ℚ) (Pool : List α)
    (i : Fin m) (j : Fin Pool.length) :
    0 ≤ ObjectiveCrowding Fitness Pool (PopulationIndices Pool) i j := by
  rw [FullObjectiveCrowdingEq Fitness Pool i j j]
  exact OrderedCrowdingNonnegative (FullObjectiveSortOrdered Fitness Pool i j) _

/-- Positive-contribution occurrences for one objective, retaining index multiplicity. -/
def FullObjectivePositive (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m) :
    Finset (Fin Pool.length) :=
  Finset.univ.filter (fun j => 0 < ObjectiveCrowding Fitness Pool (PopulationIndices Pool) i j)

/-- Positive contributions can occur at no more than twice the number of values
in any finite set containing all objective values of this population. -/
theorem FullObjectivePositiveCard (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m)
    (Default : Fin Pool.length) (Values : Finset ℚ) (Within : ∀ j : Fin Pool.length, Fitness Pool[j] i ∈ Values) :
    (FullObjectivePositive Fitness Pool i).card ≤ 2 * Values.card := by
  let Sorted := FullObjectiveSort Fitness Pool i
  let Value := FullObjectiveValues Fitness Pool i Default
  have DistinctWithin : OrderedDistinctValues Pool.length Value ⊆ Values := by
    intro q Present
    obtain ⟨k, _Valid, rfl⟩ := Finset.mem_image.mp Present
    exact Within (Sorted.getD k Default)
  have ToBoundary : Set.MapsTo Sorted.idxOf (FullObjectivePositive Fitness Pool i : Set (Fin Pool.length))
      (OrderedBoundaryPositions Pool.length Value : Set ℕ) := by
    intro j Present
    have Positive := (Finset.mem_filter.mp Present).2
    rw [FullObjectiveCrowdingEq Fitness Pool i Default j] at Positive
    apply OrderedCrowdingPositiveBoundary (FullObjectiveSortOrdered Fitness Pool i Default) _ _ Positive
    have Bound := List.idxOf_lt_length_iff.mpr (FullObjectiveSortMember Fitness Pool i j)
    simpa only [FullObjectiveSortLength] using Bound
  have Injective : Set.InjOn Sorted.idxOf (FullObjectivePositive Fitness Pool i : Set (Fin Pool.length)) := by
    intro a _ b _ Equal
    have A := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (FullObjectiveSortMember Fitness Pool i a))
    have B := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (FullObjectiveSortMember Fitness Pool i b))
    change (FullObjectiveSort Fitness Pool i).idxOf a = (FullObjectiveSort Fitness Pool i).idxOf b at Equal
    simp only [Equal] at A
    exact A.symm.trans B
  exact (Finset.card_le_card_of_injOn Sorted.idxOf ToBoundary Injective).trans
    ((OrderedBoundaryCard Pool.length Value).trans (Nat.mul_le_mul_left 2 (Finset.card_le_card DistinctWithin)))

/-- Every represented value has a positive-contribution occurrence with the
same objective value. The witness need not be the original duplicate occurrence. -/
theorem FullObjectivePositiveWitness (Fitness : α → Fin m → ℚ) (Pool : List α) (i : Fin m)
    (x : Fin Pool.length) : ∃ j : Fin Pool.length, Fitness Pool[j] i = Fitness Pool[x] i ∧
      0 < ObjectiveCrowding Fitness Pool (PopulationIndices Pool) i j := by
  let Sorted := FullObjectiveSort Fitness Pool i
  let Value := FullObjectiveValues Fitness Pool i x
  have PositionValid : Sorted.idxOf x < Pool.length := by
    have Bound := List.idxOf_lt_length_iff.mpr (FullObjectiveSortMember Fitness Pool i x)
    simpa only [FullObjectiveSortLength] using Bound
  have AtX : Value (Sorted.idxOf x) = Fitness Pool[x] i := by
    change Fitness Pool[Sorted.getD (Sorted.idxOf x) x] i = Fitness Pool[x] i
    have Valid : Sorted.idxOf x < Sorted.length := List.idxOf_lt_length_iff.mpr (FullObjectiveSortMember Fitness Pool i x)
    simp only [List.getD_eq_getElem _ _ Valid,
      List.getElem_idxOf]
  let q : {q // q ∈ OrderedDistinctValues Pool.length Value} :=
    ⟨Fitness Pool[x] i, Finset.mem_image.mpr ⟨Sorted.idxOf x, Finset.mem_range.mpr PositionValid, AtX⟩⟩
  obtain ⟨k, Valid, EqualValue, Positive⟩ := OrderedValuePositiveWitness
    (FullObjectiveSortOrdered Fitness Pool i x) q
  have ValidSort : k < Sorted.length := by rw [FullObjectiveSortLength]; exact Valid
  let j := Sorted[k]
  have PositionJ : Sorted.idxOf j = k := (FullObjectiveSortNodup Fitness Pool i).idxOf_getElem k ValidSort
  refine ⟨j, ?_, ?_⟩
  · change Value k = Fitness Pool[x] i at EqualValue
    change Fitness Pool[Sorted.getD k x] i = Fitness Pool[x] i at EqualValue
    simpa only [List.getD_eq_getElem _ _ ValidSort] using EqualValue
  · rw [FullObjectiveCrowdingEq Fitness Pool i x j, PositionJ]
    exact Positive

end
end ECTheoryLib.Operators.Selection
