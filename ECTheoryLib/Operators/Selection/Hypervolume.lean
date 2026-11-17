import ECTheoryLib.Operators.Selection.Population
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic

/-!
# Exact rational hypervolume and SMS-EMOA environmental selection

Hypervolume is computed by finite inclusion-exclusion of the boxes from the
reference point to objective vectors. Intersections use coordinate minima;
negative side lengths are clipped to zero. Individuals are indexed by their
list positions, preserving duplicates and their zero individual contributions.

SMS-EMOA discards a uniformly selected minimum contributor in the last dominance
front. Source: Zheng and Doerr, arXiv:2312.10290v4, Section 4.1 and Algorithm 1,
https://arxiv.org/pdf/2312.10290 . This file implements the exact finite formula;
identification with Lebesgue measure is not a theorem of this module.
-/

namespace ECTheoryLib.Operators.Selection

/-- Volume of the intersection of a nonempty subfamily of dominated boxes. -/
def HypervolumeIntersection {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (Subset : Finset (Fin Pool.length)) : ℚ :=
  if NonemptySubset : Subset.Nonempty then
    ∏ i : Fin m,
      max 0 (Subset.inf' NonemptySubset (fun j => Fitness Pool[j] i) - Reference i)
  else 0

/-- Inclusion-exclusion formula for the volume of the union of dominated boxes. -/
def Hypervolume {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (Front : Finset (Fin Pool.length)) : ℚ :=
  ∑ Subset ∈ Front.powerset,
    if Subset.card % 2 = 1 then HypervolumeIntersection Fitness Reference Pool Subset
    else -HypervolumeIntersection Fitness Reference Pool Subset

theorem HypervolumeEmpty {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α) :
    Hypervolume Fitness Reference Pool ∅ = 0 := by
  norm_num [Hypervolume, HypervolumeIntersection]

/-- Losing one occurrence removes only that box; equal occurrences remain. -/
def HypervolumeContribution {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (Front : Finset (Fin Pool.length)) (j : Fin Pool.length) : ℚ :=
  Hypervolume Fitness Reference Pool Front - Hypervolume Fitness Reference Pool (Front.erase j)

/-- Positions in the worst (largest numbered) dominance front. -/
def SMSLastFront {α : Type*} {m : Nat} (Fitness : α → Fin m → ℚ)
    (Pool : List α) : Finset (Fin Pool.length) :=
  let LastRank := Finset.univ.sup (fun j : Fin Pool.length => ParetoRank Fitness Pool Pool[j])
  Finset.univ.filter (fun j => ParetoRank Fitness Pool Pool[j] = LastRank)

theorem SMSLastFrontNonempty {α : Type*} {m : Nat} (Fitness : α → Fin m → ℚ)
    (Pool : List α) (NonemptyPool : 0 < Pool.length) : (SMSLastFront Fitness Pool).Nonempty := by
  let FirstPosition : Fin Pool.length := ⟨0, NonemptyPool⟩
  have AllPositionsNonempty : (Finset.univ : Finset (Fin Pool.length)).Nonempty := by
    exact ⟨FirstPosition, Finset.mem_univ FirstPosition⟩
  obtain ⟨j, jMem, Maximum⟩ := Finset.exists_mem_eq_sup Finset.univ AllPositionsNonempty
    (fun j : Fin Pool.length => ParetoRank Fitness Pool Pool[j])
  refine ⟨j, ?_⟩
  unfold SMSLastFront
  exact Finset.mem_filter.mpr ⟨jMem, Maximum.symm⟩

/-- All tied minima are retained, ready for uniform random removal. -/
def SMSRemovalCandidates {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α) :
    Finset (Fin Pool.length) :=
  let Front := SMSLastFront Fitness Pool
  Front.filter (fun j => ∀ k ∈ Front,
    HypervolumeContribution Fitness Reference Pool Front j ≤
      HypervolumeContribution Fitness Reference Pool Front k)

theorem SMSRemovalCandidatesNonempty {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (NonemptyPool : 0 < Pool.length) : (SMSRemovalCandidates Fitness Reference Pool).Nonempty := by
  have FrontNonempty := SMSLastFrontNonempty Fitness Pool NonemptyPool
  obtain ⟨j, jMem, Minimal⟩ := Finset.exists_min_image (SMSLastFront Fitness Pool)
    (HypervolumeContribution Fitness Reference Pool (SMSLastFront Fitness Pool)) FrontNonempty
  exact ⟨j, Finset.mem_filter.mpr ⟨jMem, Minimal⟩⟩

theorem SMSRemovalCandidateLastFront {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (j : Fin Pool.length) (Candidate : j ∈ SMSRemovalCandidates Fitness Reference Pool) :
    j ∈ SMSLastFront Fitness Pool := by
  exact (Finset.mem_filter.mp Candidate).1

theorem SMSRemovalCandidateMinimal {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (j : Fin Pool.length) (Candidate : j ∈ SMSRemovalCandidates Fitness Reference Pool) :
    ∀ k ∈ SMSLastFront Fitness Pool,
      HypervolumeContribution Fitness Reference Pool (SMSLastFront Fitness Pool) j ≤
        HypervolumeContribution Fitness Reference Pool (SMSLastFront Fitness Pool) k := by
  exact (Finset.mem_filter.mp Candidate).2

noncomputable section

/-- Uniform among tied minimum contributors, not an arbitrary tie selector. -/
def SMSRemovalIndex {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (NonemptyPool : 0 < Pool.length) : PMF (Fin Pool.length) :=
  PMF.uniformOfFinset (SMSRemovalCandidates Fitness Reference Pool)
    (SMSRemovalCandidatesNonempty Fitness Reference Pool NonemptyPool)

theorem SMSRemovalIndexSupport {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (NonemptyPool : 0 < Pool.length) (j : Fin Pool.length) :
    j ∈ (SMSRemovalIndex Fitness Reference Pool NonemptyPool).support ↔
      j ∈ SMSRemovalCandidates Fitness Reference Pool := by
  exact PMF.mem_support_uniformOfFinset_iff _ j

theorem SMSRemovalIndexProbability {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (NonemptyPool : 0 < Pool.length) (j : Fin Pool.length)
    (Candidate : j ∈ SMSRemovalCandidates Fitness Reference Pool) :
    SMSRemovalIndex Fitness Reference Pool NonemptyPool j =
      ((SMSRemovalCandidates Fitness Reference Pool).card : ENNReal)⁻¹ := by
  exact PMF.uniformOfFinset_apply_of_mem _ Candidate

/-- Remove exactly one occurrence; every other occurrence retains its list position order. -/
def SMSEnvironment {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool : List α)
    (NonemptyPool : 0 < Pool.length) : PMF (List α) :=
  (SMSRemovalIndex Fitness Reference Pool NonemptyPool).map (fun j => Pool.eraseIdx j.val)

theorem SMSEnvironmentLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Reference : Fin m → ℚ) (Pool Next : List α)
    (NonemptyPool : 0 < Pool.length)
    (Possible : Next ∈ (SMSEnvironment Fitness Reference Pool NonemptyPool).support) :
    Next.length + 1 = Pool.length := by
  obtain ⟨j, _RemovalPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← Equality]
  exact List.length_eraseIdx_add_one j.isLt

end
end ECTheoryLib.Operators.Selection
