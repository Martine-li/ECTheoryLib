import ECTheoryLib.Operators.Selection.Population
import Mathlib.Tactic

/-!
# Correctness of nondominated sorting ranks

Strict dominance is transitive and irreflexive. Consequently, every step towards
a dominator strictly decreases the number of dominating population positions.
This gives both a finite bound and a stabilization theorem: the `Pool.length`
iterations in `ParetoRank` compute the full rank, without truncating a chain.

The resulting recurrence is the rank recurrence of nondominated sorting: rank
zero means nondominated, and every other rank is one plus the maximum rank of
its dominators. Ranks start at zero here; the paper starts at one.
Source: Zheng and Doerr, arXiv:2112.08581, Algorithm 1.
-/

namespace ECTheoryLib.Operators.Selection

/-- Dominating positions, retaining separate occurrences of equal genotypes. -/
def DominatorIndices {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) : Finset (Fin Pool.length) :=
  Finset.univ.filter (fun j => StrictlyDominates Fitness Pool[j] x)

theorem DominatorIndicesCardLeLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) :
    (DominatorIndices Fitness Pool x).card ≤ Pool.length := by
  have Bound := Finset.card_le_card (Finset.filter_subset
    (fun j : Fin Pool.length => StrictlyDominates Fitness Pool[j] x) Finset.univ)
  rw [Finset.card_univ, Fintype.card_fin] at Bound
  exact Bound

theorem DominatorIndicesCardStrictDecrease {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) (j : Fin Pool.length)
    (Dominance : StrictlyDominates Fitness Pool[j] x) :
    (DominatorIndices Fitness Pool Pool[j]).card < (DominatorIndices Fitness Pool x).card := by
  have Included : DominatorIndices Fitness Pool Pool[j] ⊆ DominatorIndices Fitness Pool x := by
    intro i Membership
    have DominatesDominator := (Finset.mem_filter.mp Membership).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ i, StrictlyDominatesTransitive Fitness DominatesDominator Dominance⟩
  have DominatorIncluded : j ∈ DominatorIndices Fitness Pool x := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, Dominance⟩
  have DominatorExcluded : j ∉ DominatorIndices Fitness Pool Pool[j] := by
    intro Membership
    exact StrictlyDominatesIrreflexive Fitness Pool[j] (Finset.mem_filter.mp Membership).2
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_of_subset Included).mpr ⟨j, DominatorIncluded, DominatorExcluded⟩

theorem RankDepthLeDominatorCount {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (Depth : Nat) (x : α) :
    RankDepth Fitness Pool Depth x ≤ (DominatorIndices Fitness Pool x).card := by
  induction Depth generalizing x with
  | zero => exact Nat.zero_le _
  | succ Depth Previous =>
      unfold RankDepth
      apply Finset.sup_le
      intro j _Membership
      by_cases Dominance : StrictlyDominates Fitness Pool[j] x
      · rw [if_pos Dominance]
        have SmallerCount := DominatorIndicesCardStrictDecrease Fitness Pool x j Dominance
        have PreviousBound := Previous Pool[j]
        omega
      · rw [if_neg Dominance]
        exact Nat.zero_le _

/-- Once depth exceeds the number of dominators, another round changes nothing. -/
theorem RankDepthStabilizes {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (Depth : Nat) (x : α)
    (EnoughDepth : (DominatorIndices Fitness Pool x).card ≤ Depth) :
    RankDepth Fitness Pool (Depth + 1) x = RankDepth Fitness Pool Depth x := by
  induction Depth generalizing x with
  | zero =>
      apply RankDepthOfNondominated Fitness Pool x
      intro j Dominance
      have SmallerCount := DominatorIndicesCardStrictDecrease Fitness Pool x j Dominance
      omega
  | succ Depth Previous =>
      change Finset.univ.sup (fun j : Fin Pool.length =>
          if StrictlyDominates Fitness Pool[j] x then RankDepth Fitness Pool (Depth + 1) Pool[j] + 1 else 0) =
        Finset.univ.sup (fun j : Fin Pool.length =>
          if StrictlyDominates Fitness Pool[j] x then RankDepth Fitness Pool Depth Pool[j] + 1 else 0)
      apply Finset.sup_congr rfl
      intro j _Membership
      by_cases Dominance : StrictlyDominates Fitness Pool[j] x
      · rw [if_pos Dominance, if_pos Dominance]
        have SmallerCount := DominatorIndicesCardStrictDecrease Fitness Pool x j Dominance
        have EnoughForDominator : (DominatorIndices Fitness Pool Pool[j]).card ≤ Depth := by omega
        rw [Previous Pool[j] EnoughForDominator]
      · rw [if_neg Dominance, if_neg Dominance]

/-- The final rank obeys the exact, untruncated nondominated sorting recurrence. -/
theorem ParetoRankRecurrence {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) :
    ParetoRank Fitness Pool x = Finset.univ.sup (fun j : Fin Pool.length =>
      if StrictlyDominates Fitness Pool[j] x then ParetoRank Fitness Pool Pool[j] + 1 else 0) := by
  have Stable := RankDepthStabilizes Fitness Pool Pool.length x
    (DominatorIndicesCardLeLength Fitness Pool x)
  unfold ParetoRank
  rw [← Stable]
  rfl

theorem ParetoRankStrictlyIncreases {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) (j : Fin Pool.length)
    (Dominance : StrictlyDominates Fitness Pool[j] x) :
    ParetoRank Fitness Pool Pool[j] < ParetoRank Fitness Pool x := by
  rw [ParetoRankRecurrence Fitness Pool x]
  have ContributionBound := Finset.le_sup (s := Finset.univ)
    (f := fun i : Fin Pool.length => if StrictlyDominates Fitness Pool[i] x then
      ParetoRank Fitness Pool Pool[i] + 1 else 0) (Finset.mem_univ j)
  rw [if_pos Dominance] at ContributionBound
  omega

theorem ParetoRankZeroIffNondominated {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) :
    ParetoRank Fitness Pool x = 0 ↔
      ∀ j : Fin Pool.length, ¬ StrictlyDominates Fitness Pool[j] x := by
  constructor
  · intro ZeroRank j Dominance
    have PositiveRank := ParetoRankStrictlyIncreases Fitness Pool x j Dominance
    rw [ZeroRank] at PositiveRank
    omega
  · intro Nondominated
    exact RankDepthOfNondominated Fitness Pool x Nondominated Pool.length

theorem ParetoRankLeLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) :
    ParetoRank Fitness Pool x ≤ Pool.length := by
  have CountBound := DominatorIndicesCardLeLength Fitness Pool x
  have RankBound := RankDepthLeDominatorCount Fitness Pool Pool.length x
  unfold ParetoRank
  omega

/-- A population member itself cannot dominate itself, so its rank is below N. -/
theorem ParetoRankMemberLtLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (j : Fin Pool.length) :
    ParetoRank Fitness Pool Pool[j] < Pool.length := by
  have SelfExcluded : j ∉ DominatorIndices Fitness Pool Pool[j] := by
    intro Membership
    exact StrictlyDominatesIrreflexive Fitness Pool[j] (Finset.mem_filter.mp Membership).2
  have ProperSubset : DominatorIndices Fitness Pool Pool[j] ⊂ Finset.univ := by
    apply (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr
    exact ⟨j, Finset.mem_univ j, SelfExcluded⟩
  have CountBound := Finset.card_lt_card ProperSubset
  rw [Finset.card_univ, Fintype.card_fin] at CountBound
  have RankBound := RankDepthLeDominatorCount Fitness Pool Pool.length Pool[j]
  unfold ParetoRank
  omega

/-- A chain of `Length` dominance edges ending at `x`, with every predecessor in Pool. -/
def HasDominanceChain {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) : Nat → α → Prop
  | 0, _ => True
  | Length + 1, x => ∃ j : Fin Pool.length,
      StrictlyDominates Fitness Pool[j] x ∧ HasDominanceChain Fitness Pool Length Pool[j]

theorem DominanceChainLeDominatorCount {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (Length : Nat) (x : α)
    (Chain : HasDominanceChain Fitness Pool Length x) :
    Length ≤ (DominatorIndices Fitness Pool x).card := by
  induction Length generalizing x with
  | zero => exact Nat.zero_le _
  | succ Length Previous =>
      obtain ⟨j, Dominance, PreviousChain⟩ := Chain
      have SmallerCount := DominatorIndicesCardStrictDecrease Fitness Pool x j Dominance
      have PreviousBound := Previous Pool[j] PreviousChain
      omega

/-- The dynamic program computes exactly the chains whose lengths fit in its depth. -/
theorem DominanceChainIffLeRankDepth {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (Length Depth : Nat) (x : α)
    (FitsDepth : Length ≤ Depth) :
    HasDominanceChain Fitness Pool Length x ↔ Length ≤ RankDepth Fitness Pool Depth x := by
  induction Length generalizing Depth x with
  | zero =>
      constructor
      · intro _Chain
        exact Nat.zero_le _
      · intro _Bound
        exact True.intro
  | succ Length Previous =>
      cases Depth with
      | zero => omega
      | succ Depth =>
          have PreviousFits : Length ≤ Depth := by omega
          change (∃ j : Fin Pool.length, StrictlyDominates Fitness Pool[j] x ∧
              HasDominanceChain Fitness Pool Length Pool[j]) ↔
            Length + 1 ≤ Finset.univ.sup (fun j : Fin Pool.length =>
              if StrictlyDominates Fitness Pool[j] x then RankDepth Fitness Pool Depth Pool[j] + 1 else 0)
          rw [Finset.le_sup_iff (Nat.zero_lt_succ Length)]
          constructor
          · intro Chain
            obtain ⟨j, Dominance, PreviousChain⟩ := Chain
            refine ⟨j, Finset.mem_univ j, ?_⟩
            rw [if_pos Dominance]
            have PreviousBound := (Previous Depth Pool[j] PreviousFits).mp PreviousChain
            omega
          · intro Bound
            obtain ⟨j, _Membership, ContributionBound⟩ := Bound
            by_cases Dominance : StrictlyDominates Fitness Pool[j] x
            · rw [if_pos Dominance] at ContributionBound
              refine ⟨j, Dominance, ?_⟩
              apply (Previous Depth Pool[j] PreviousFits).mpr
              omega
            · rw [if_neg Dominance] at ContributionBound
              omega

/-- The final rank is precisely the maximum feasible dominance-chain length. -/
theorem DominanceChainIffLeParetoRank {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (Length : Nat) (x : α) :
    HasDominanceChain Fitness Pool Length x ↔ Length ≤ ParetoRank Fitness Pool x := by
  constructor
  · intro Chain
    have CountBound := DominanceChainLeDominatorCount Fitness Pool Length x Chain
    have PopulationBound := DominatorIndicesCardLeLength Fitness Pool x
    have FitsDepth : Length ≤ Pool.length := by omega
    exact (DominanceChainIffLeRankDepth Fitness Pool Length Pool.length x FitsDepth).mp Chain
  · intro RankBound
    have PopulationBound := ParetoRankLeLength Fitness Pool x
    have FitsDepth : Length ≤ Pool.length := by omega
    exact (DominanceChainIffLeRankDepth Fitness Pool Length Pool.length x FitsDepth).mpr RankBound

theorem ParetoRankChainExists {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) :
    HasDominanceChain Fitness Pool (ParetoRank Fitness Pool x) x := by
  apply (DominanceChainIffLeParetoRank Fitness Pool _ x).mpr
  exact Nat.le_refl _

end ECTheoryLib.Operators.Selection
