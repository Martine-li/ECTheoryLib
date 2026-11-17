import ECTheoryLib.Problems.OneMinMax
import ECTheoryLib.Operators.Selection.FullFrontCrowding
import ECTheoryLib.Operators.Selection.OrderedSelection
import ECTheoryLib.Algorithms.NSGAII
import Mathlib.Tactic.FinCases

/-!
# OneMinMax value retention in the actual NSGA-II selection

All occurrences have rank zero. At most four occurrences per objective value
can have positive crowding distance, while every represented value has a positive
witness. Therefore capacity at least `4 * (n + 1)` preserves every represented
value, for every survivor priority permutation. This is the retention mechanism
of Zheng and Doerr (2023), arXiv:2112.08581v7, Lemma 1, specialized to the library's
index-based objective tie order and zero internal contribution for constant
objectives. No assertion is made that every duplicate individual is retained.
-/
namespace ECTheoryLib.Analysis.NSGAIIOneMinMax
open Operators.Selection
noncomputable section

/-- Rational embedding of the maximized OneMinMax objectives `(ones, zeroes)`. -/
def Fitness {n : ℕ} (x : Bits n) (i : Fin 2) : ℚ := ECTheoryLib.OneMinMax x i

/-- No OneMinMax search point strictly dominates another. -/
theorem NoStrictDominance {n : ℕ} (x y : Bits n) : ¬ StrictlyDominates Fitness x y := by
  intro Dominance
  have First := Dominance.1 0
  have Second := Dominance.1 1
  change (OneMax y : ℚ) ≤ (OneMax x : ℚ) at First
  change ((n - OneMax y : ℕ) : ℚ) ≤ ((n - OneMax x : ℕ) : ℚ) at Second
  have A : OneMax y ≤ OneMax x := by exact_mod_cast First
  have B : n - OneMax y ≤ n - OneMax x := by exact_mod_cast Second
  have XBound := Problems.OneMax.OneMaxLeN x
  have YBound := Problems.OneMax.OneMaxLeN y
  have Equal : OneMax x = OneMax y := by omega
  have Same : Fitness x = Fitness y := by
    funext i
    unfold Fitness ECTheoryLib.OneMinMax OneMin
    rw [Equal]
  obtain ⟨i, Strict⟩ := Dominance.2
  rw [congrFun Same i] at Strict
  exact (lt_irrefl _) Strict

/-- Every population occurrence has nondomination rank zero, including duplicates. -/
theorem RankZero {n : ℕ} (Pool : List (Bits n)) (x : Bits n) : ParetoRank Fitness Pool x = 0 :=
  RankDepthOfNondominated Fitness Pool x (fun j => NoStrictDominance Pool[j] x) Pool.length

theorem RankFrontZero {n : ℕ} (Pool : List (Bits n)) :
    RankFront Fitness Pool 0 = PopulationIndices Pool := by
  simp only [RankFront, RankZero, decide_true, List.filter_true]

/-- Crowding distance is the sum of the two full-population objective contributions. -/
theorem CrowdingEq {n : ℕ} (Pool : List (Bits n)) (j : Fin Pool.length) :
    CrowdingDistance Fitness Pool j =
      ObjectiveCrowding Fitness Pool (PopulationIndices Pool) 0 j +
      ObjectiveCrowding Fitness Pool (PopulationIndices Pool) 1 j := by
  simp only [CrowdingDistance, RankZero, RankFrontZero, Fin.sum_univ_two]

/-- The rational objective values all lie in the `n+1` integer levels. -/
theorem ObjectiveWithin {n : ℕ} (Pool : List (Bits n)) (i : Fin 2) (j : Fin Pool.length) :
    Fitness Pool[j] i ∈ (Finset.range (n + 1)).image (fun k : ℕ => (k : ℚ)) := by
  apply Finset.mem_image.mpr
  refine ⟨ECTheoryLib.OneMinMax Pool[j] i, ?_, rfl⟩
  apply Finset.mem_range.mpr
  fin_cases i
  · exact Nat.lt_succ_of_le (Problems.OneMax.OneMaxLeN Pool[j])
  · exact Nat.lt_succ_of_le (Problems.OneMinMax.OneMinLeN Pool[j])

/-- At most `4(n+1)` occurrence indices have positive total crowding distance. -/
theorem PositiveCrowdingCard {n : ℕ} (Pool : List (Bits n)) :
    (Finset.univ.filter (fun j => 0 < CrowdingDistance Fitness Pool j)).card ≤ 4 * (n + 1) := by
  by_cases Empty : Pool.length = 0
  · have NoIndex : IsEmpty (Fin Pool.length) := ⟨fun j => by have := j.isLt; omega⟩
    let := NoIndex
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, Nat.zero_le]
  · let Default : Fin Pool.length := ⟨0, Nat.pos_of_ne_zero Empty⟩
    have Each (i : Fin 2) : (FullObjectivePositive Fitness Pool i).card ≤ 2 * (n + 1) := by
      have Bound := FullObjectivePositiveCard Fitness Pool i Default
        ((Finset.range (n + 1)).image (fun k : ℕ => (k : ℚ))) (ObjectiveWithin Pool i)
      exact Bound.trans (Nat.mul_le_mul_left 2 ((Finset.card_image_le).trans_eq (Finset.card_range _)))
    have Included : Finset.univ.filter (fun j => 0 < CrowdingDistance Fitness Pool j) ⊆
        FullObjectivePositive Fitness Pool 0 ∪ FullObjectivePositive Fitness Pool 1 := by
      intro j Present
      have Positive := (Finset.mem_filter.mp Present).2
      rw [CrowdingEq] at Positive
      by_cases First : 0 < ObjectiveCrowding Fitness Pool (PopulationIndices Pool) 0 j
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, First⟩)
      · have Second : 0 < ObjectiveCrowding Fitness Pool (PopulationIndices Pool) 1 j := by
          by_contra NotPositive
          exact (not_lt_of_ge (add_nonpos (le_of_not_gt First) (le_of_not_gt NotPositive))) Positive
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Second⟩)
    have Count := (Finset.card_le_card Included).trans (Finset.card_union_le _ _)
    have A := Each 0
    have B := Each 1
    omega

/-- Each represented Hamming weight has a positive-crowding occurrence witness. -/
theorem PositiveWeightWitness {n : ℕ} (Pool : List (Bits n)) (x : Fin Pool.length) :
    ∃ j : Fin Pool.length, OneMax Pool[j] = OneMax Pool[x] ∧ 0 < CrowdingDistance Fitness Pool j := by
  obtain ⟨j, Same, Positive⟩ := FullObjectivePositiveWitness Fitness Pool 0 x
  refine ⟨j, ?_, ?_⟩
  · change (OneMax Pool[j] : ℚ) = (OneMax Pool[x] : ℚ) at Same
    exact_mod_cast Same
  · rw [CrowdingEq]
    exact Positive.trans_le (le_add_of_nonneg_right (FullObjectiveCrowdingNonnegative Fitness Pool 1 j))

/-- With capacity at least `4(n+1)`, actual deterministic environmental selection
retains a representative of every input weight, regardless of survivor ties. -/
theorem SelectRetainsWeight {n : ℕ} (Pool : List (Bits n)) (Capacity : ℕ)
    (Room : 4 * (n + 1) ≤ Capacity) (Priority : Equiv.Perm (Fin Pool.length))
    (x : Bits n) (Present : x ∈ Pool) :
    ∃ y ∈ NSGAIISelect Fitness Capacity Pool Priority, OneMax y = OneMax x := by
  obtain ⟨i, Valid, AtX⟩ := List.mem_iff_getElem.mp Present
  obtain ⟨j, Same, Positive⟩ := PositiveWeightWitness Pool ⟨i, Valid⟩
  refine ⟨Pool[j], NSGAIISelectRetainsPositive Fitness Pool Priority Capacity 0
    (fun k => RankZero Pool Pool[k]) ((PositiveCrowdingCard Pool).trans Room) j Positive, ?_⟩
  change OneMax Pool[j] = OneMax Pool[i] at Same
  simpa only [AtX] using Same

/-- Every supported randomized environmental-selection result preserves all
input weights. Randomness in survivor priorities cannot invalidate retention. -/
theorem EnvironmentRetainsWeight {n : ℕ} (Pool Result : List (Bits n)) (Capacity : ℕ)
    (Room : 4 * (n + 1) ≤ Capacity)
    (Possible : Result ∈ (NSGAIIEnvironment Fitness Capacity Pool).support)
    (x : Bits n) (Present : x ∈ Pool) : ∃ y ∈ Result, OneMax y = OneMax x := by
  obtain ⟨Priority, _, Equal⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← Equal]
  exact SelectRetainsWeight Pool Capacity Room Priority x Present

end
end ECTheoryLib.Analysis.NSGAIIOneMinMax
