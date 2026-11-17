import ECTheoryLib.Operators.Selection.CrowdingDistance
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.Nodup

/-!
# Preservation under ordered truncation

A sorted list retains every preferred item when the capacity accommodates all
preferred items and preference is closed toward the front of the ordering.
The NSGA-II specialization applies to a single nondomination rank and positive
crowding distance. Items are occurrence indices, so duplicates are not merged.
-/
namespace ECTheoryLib.Operators.Selection
noncomputable section

/-- Truncating a duplicate-free sorted list retains every preferred item if
there are at most `Capacity` preferred items and earlier items inherit preference. -/
theorem OrderedTakeRetains {α : Type*} [DecidableEq α] (Items : List α)
    (Relation : α → α → Prop) (Good : Finset α) (Capacity : ℕ)
    (Distinct : Items.Nodup) (Sorted : Items.Pairwise Relation)
    (Closed : ∀ a b, Relation a b → b ∈ Good → a ∈ Good)
    (Fits : Good.card ≤ Capacity) (j : α) (Present : j ∈ Items) (Preferred : j ∈ Good) :
    j ∈ Items.take Capacity := by
  have PositionValid := List.idxOf_lt_length_iff.mpr Present
  let Before := fun i : Fin (Items.idxOf j + 1) => Items[i.val]'(by omega)
  have BeforeGood (i : Fin (Items.idxOf j + 1)) : Before i ∈ Good := by
    by_cases Earlier : i.val < Items.idxOf j
    · have Ordered := List.pairwise_iff_getElem.mp Sorted i.val (Items.idxOf j)
        (by omega) PositionValid Earlier
      simp only [List.getElem_idxOf] at Ordered
      exact Closed _ j Ordered Preferred
    · have Equal : i.val = Items.idxOf j := by omega
      simpa only [Before, Equal, List.getElem_idxOf] using Preferred
  let IntoGood := fun i : Fin (Items.idxOf j + 1) => (⟨Before i, BeforeGood i⟩ : Good)
  have Injective : Function.Injective IntoGood := by
    intro a b Equal
    have Values : Before a = Before b := congrArg Subtype.val Equal
    exact Fin.ext ((Distinct.getElem_inj_iff).mp Values)
  have Size : Items.idxOf j + 1 ≤ Good.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective IntoGood Injective
  exact (List.mem_take_iff_idxOf_lt Present).mpr (by omega)

/-- On a single rank, NSGA-II sorting uses descending crowding distance and
then the supplied permutation priority. This relation is a total preorder. -/
theorem NSGAIISingleRankSorted {α : Type*} {m : ℕ} (Fitness : α → Fin m → ℚ)
    (Pool : List α) (Priority : Equiv.Perm (Fin Pool.length))
    (Rank : ℕ) (SameRank : ∀ j : Fin Pool.length, ParetoRank Fitness Pool Pool[j] = Rank) :
    ((PopulationIndices Pool).mergeSort (NSGAIIBetter Fitness Pool Priority)).Pairwise
      (fun a b => NSGAIIBetter Fitness Pool Priority a b = true) := by
  let Key := fun j : Fin Pool.length =>
    toLex (OrderDual.toDual (CrowdingDistance Fitness Pool j), (Priority j).val)
  have KeyIff (a b : Fin Pool.length) :
      NSGAIIBetter Fitness Pool Priority a b = true ↔ Key a ≤ Key b := by
    simp only [NSGAIIBetter, SameRank, ne_eq, not_true_eq_false, if_false,
      Key, Prod.Lex.toLex_le_toLex, OrderDual.toDual_lt_toDual, OrderDual.toDual_inj]
    by_cases Equal : CrowdingDistance Fitness Pool a = CrowdingDistance Fitness Pool b
    · simp [Equal]
    · simp only [Equal, not_false_eq_true, if_true, decide_eq_true_eq, false_and, or_false]
      exact ⟨fun Bound => lt_of_le_of_ne Bound (Ne.symm Equal), le_of_lt⟩
  apply List.pairwise_mergeSort
  · intro a b c AB BC
    exact (KeyIff a c).mpr (((KeyIff a b).mp AB).trans ((KeyIff b c).mp BC))
  · intro a b
    rw [Bool.or_eq_true]
    rcases le_total (Key a) (Key b) with AB | BA
    · exact Or.inl ((KeyIff a b).mpr AB)
    · exact Or.inr ((KeyIff b a).mpr BA)

/-- If a single rank has at most `Capacity` occurrences with positive crowding
distance, every such occurrence survives for every tie-priority permutation. -/
theorem NSGAIISelectRetainsPositive {α : Type*} {m : ℕ} (Fitness : α → Fin m → ℚ)
    (Pool : List α) (Priority : Equiv.Perm (Fin Pool.length)) (Capacity Rank : ℕ)
    (SameRank : ∀ j : Fin Pool.length, ParetoRank Fitness Pool Pool[j] = Rank)
    (Fits : (Finset.univ.filter (fun j => 0 < CrowdingDistance Fitness Pool j)).card ≤ Capacity)
    (j : Fin Pool.length) (Positive : 0 < CrowdingDistance Fitness Pool j) :
    Pool[j] ∈ NSGAIISelect Fitness Capacity Pool Priority := by
  let Good := Finset.univ.filter (fun j => 0 < CrowdingDistance Fitness Pool j)
  have Closed (a b : Fin Pool.length) (Earlier : NSGAIIBetter Fitness Pool Priority a b = true)
      (Preferred : b ∈ Good) : a ∈ Good := by
    have BPositive := (Finset.mem_filter.mp Preferred).2
    by_cases Equal : CrowdingDistance Fitness Pool a = CrowdingDistance Fitness Pool b
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equal ▸ BPositive⟩
    · have Larger : CrowdingDistance Fitness Pool b ≤ CrowdingDistance Fitness Pool a := by
        simpa only [NSGAIIBetter, SameRank, ne_eq, not_true_eq_false, if_false,
          Equal, not_false_eq_true, if_true, decide_eq_true_eq] using Earlier
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, BPositive.trans_le Larger⟩
  have Present : j ∈ (PopulationIndices Pool).mergeSort (NSGAIIBetter Fitness Pool Priority) := by
    exact List.mem_mergeSort.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have Retained := OrderedTakeRetains _ _ Good Capacity
    (List.Nodup.mergeSort (List.nodup_ofFn.mpr Function.injective_id))
    (NSGAIISingleRankSorted Fitness Pool Priority Rank SameRank) Closed Fits j Present
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Positive⟩)
  exact List.mem_map.mpr ⟨j, Retained, rfl⟩

end
end ECTheoryLib.Operators.Selection
