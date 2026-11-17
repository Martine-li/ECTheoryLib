import ECTheoryLib.Operators.Selection.Population
import Mathlib.Algebra.Order.Monoid.WithTop

/-!
# Classical crowding distance and NSGA-II environmental selection

Source: Zheng and Doerr, arXiv:2112.08581, Algorithms 1–3. Occurrences remain
distinct, including identical genotypes. Objective sorting breaks equal-value
ties by position. Survivor ties use a supplied permutation, sampled uniformly
by the randomized interface. Internal contributions of a constant objective are
zero; the first and last positions still have infinite crowding distance.
-/

namespace ECTheoryLib.Operators.Selection

/-- List every occurrence index, preserving genotype multiplicities. -/
def PopulationIndices {α : Type*} (Pool : List α) : List (Fin Pool.length) :=
  List.ofFn (fun j => j)

/-- The occurrence indices belonging to a specified nondomination rank. -/
def RankFront {α : Type*} {m : Nat} (Fitness : α → Fin m → ℚ)
    (Pool : List α) (Rank : Nat) : List (Fin Pool.length) :=
  (PopulationIndices Pool).filter (fun j => decide (ParetoRank Fitness Pool Pool[j] = Rank))

/-- Normalized neighboring objective gap within a rank. Boundary positions
receive infinity; division by a zero objective range gives zero internally. -/
def ObjectiveCrowding {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α)
    (Front : List (Fin Pool.length)) (i : Fin m) (j : Fin Pool.length) : WithTop ℚ :=
  let Sorted := Front.mergeSort (fun a b => decide
    (Fitness Pool[a] i < Fitness Pool[b] i ∨
      (Fitness Pool[a] i = Fitness Pool[b] i ∧ a.val ≤ b.val)))
  let Position := Sorted.idxOf j
  if Position = 0 ∨ Position + 1 ≥ Sorted.length then ⊤
  else
    let First := Sorted.getD 0 j
    let Last := Sorted.getD (Sorted.length - 1) j
    let Previous := Sorted.getD (Position - 1) j
    let Next := Sorted.getD (Position + 1) j
    ((Fitness Pool[Next] i - Fitness Pool[Previous] i) /
      (Fitness Pool[Last] i - Fitness Pool[First] i) : ℚ)

/-- Sum objective contributions using only members of the same nondomination rank. -/
def CrowdingDistance {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (j : Fin Pool.length) : WithTop ℚ :=
  let Front := RankFront Fitness Pool (ParetoRank Fitness Pool Pool[j])
  ∑ i : Fin m, ObjectiveCrowding Fitness Pool Front i j

/-- Prefer lower rank, then larger crowding distance, then the supplied tie priority. -/
def NSGAIIBetter {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α)
    (Priority : Equiv.Perm (Fin Pool.length)) (a b : Fin Pool.length) : Bool :=
  let RankA := ParetoRank Fitness Pool Pool[a]
  let RankB := ParetoRank Fitness Pool Pool[b]
  let DistanceA := CrowdingDistance Fitness Pool a
  let DistanceB := CrowdingDistance Fitness Pool b
  if RankA ≠ RankB then decide (RankA ≤ RankB)
  else if DistanceA ≠ DistanceB then decide (DistanceB ≤ DistanceA)
  else decide ((Priority a).val ≤ (Priority b).val)

/-- Deterministic NSGA-II environmental selection for a fixed tie-priority permutation. -/
def NSGAIISelect {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α)
    (Priority : Equiv.Perm (Fin Pool.length)) : List α :=
  (SelectByOrder Capacity (PopulationIndices Pool)
    (NSGAIIBetter Fitness Pool Priority)).map (fun j => Pool[j])

theorem NSGAIISelectLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α)
    (Priority : Equiv.Perm (Fin Pool.length)) :
    (NSGAIISelect Fitness Capacity Pool Priority).length = min Capacity Pool.length := by
  unfold NSGAIISelect
  rw [List.length_map, SelectByOrderLength]
  unfold PopulationIndices
  rw [List.length_ofFn]

theorem NSGAIISelectMember {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α)
    (Priority : Equiv.Perm (Fin Pool.length)) {x : α}
    (Selected : x ∈ NSGAIISelect Fitness Capacity Pool Priority) : x ∈ Pool := by
  obtain ⟨j, _, ValueEquals⟩ := List.mem_map.mp Selected
  rw [← ValueEquals]
  exact List.getElem_mem j.isLt

noncomputable section

/-- Environmental selection with a uniformly sampled permutation for survivor ties. -/
def NSGAIIEnvironment {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α) : PMF (List α) :=
  (UniformTiePermutation Pool.length).map (NSGAIISelect Fitness Capacity Pool)

theorem NSGAIIEnvironmentLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool Samples : List α)
    (Possible : Samples ∈ (NSGAIIEnvironment Fitness Capacity Pool).support) :
    Samples.length = min Capacity Pool.length := by
  obtain ⟨Priority, _, SamplesEqual⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← SamplesEqual]
  exact NSGAIISelectLength Fitness Capacity Pool Priority

end
end ECTheoryLib.Operators.Selection
