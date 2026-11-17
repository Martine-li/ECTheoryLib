import ECTheoryLib.Operators.Selection.CrowdingDistance
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# SPEA2 strength, density order, and iterative truncation

Source: Zitzler, Laumanns, and Thiele, TIK Report 103 (2001). Raw fitness sums
the strengths of strict dominators. Density is ordered using squared objective
distances: the intended density term is `1/(sigma_k+2)`, and its ordering is
equivalent to decreasing kth-neighbor distance at equal integer raw fitness.
The standard index is `floor(sqrt(|P|+|A|))`; explicit-index variants support
configured capacities. Truncation recomputes complete sorted neighbor-distance
vectors after each deletion. Uniform permutations break complete ties.
Lists retain all genotype occurrences.
-/

namespace ECTheoryLib.Operators.Selection

/-- The number of population occurrences strictly dominated by a given point. -/
def Strength {α : Type*} {m : Nat} (Fitness : α → Fin m → ℚ)
    (Pool : List α) (x : α) : Nat :=
  ((Finset.univ : Finset (Fin Pool.length)).filter
    (fun j => StrictlyDominates Fitness x Pool[j])).card

/-- Sum of the strengths of every strict dominator occurrence; smaller is better. -/
def RawFitness {α : Type*} {m : Nat} (Fitness : α → Fin m → ℚ)
    (Pool : List α) (x : α) : Nat :=
  ∑ j : Fin Pool.length,
    if StrictlyDominates Fitness Pool[j] x then Strength Fitness Pool Pool[j] else 0

theorem RawFitnessOfNondominated {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α)
    (Nondominated : ∀ j : Fin Pool.length, ¬ StrictlyDominates Fitness Pool[j] x) :
    RawFitness Fitness Pool x = 0 := by
  unfold RawFitness
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (Nondominated j)]

/-- A dominated population occurrence has strictly positive raw fitness. -/
theorem RawFitnessPositiveOfDominated {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x j : Fin Pool.length)
    (Dominated : StrictlyDominates Fitness Pool[j] Pool[x]) :
    0 < RawFitness Fitness Pool Pool[x] := by
  have DominatorStrength : 0 < Strength Fitness Pool Pool[j] := by
    unfold Strength
    apply Finset.card_pos.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, Dominated⟩⟩
  have DominatorContribution : Strength Fitness Pool Pool[j] ≤
      RawFitness Fitness Pool Pool[x] := by
    unfold RawFitness
    have TermBound := Finset.single_le_sum
      (fun (i : Fin Pool.length) (_ : i ∈ Finset.univ) => Nat.zero_le
        (if StrictlyDominates Fitness Pool[i] Pool[x] then Strength Fitness Pool Pool[i] else 0))
      (Finset.mem_univ j)
    rw [if_pos Dominated] at TermBound
    exact TermBound
  exact lt_of_lt_of_le DominatorStrength DominatorContribution

/-- Sum of squared rational differences in objective space, preserving exact finite arithmetic. -/
def SquaredObjectiveDistance {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (x y : α) : ℚ :=
  ∑ i : Fin m, (Fitness x i - Fitness y i) ^ 2

/-- Squared kth-neighbor distance, with the self-distance zero included before
indexing. Missing neighbors, including the singleton degenerate case, return zero. -/
def KthSquaredDistance {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) : ℚ :=
  ((Pool.map (SquaredObjectiveDistance Fitness x)).mergeSort
    (fun a b => decide (a ≤ b))).getD (Nat.sqrt Pool.length) 0

/-- Prefer smaller integer raw fitness, then larger kth-neighbor squared distance. Equal scores compare true, so the caller controls the final tie convention. -/
def SPEA2FitnessBetter {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x y : α) : Bool :=
  if RawFitness Fitness Pool x ≠ RawFitness Fitness Pool y then
    decide (RawFitness Fitness Pool x ≤ RawFitness Fitness Pool y)
  else decide (KthSquaredDistance Fitness Pool y ≤ KthSquaredDistance Fitness Pool x)

/-- Explicit neighbor-index variant for configurations such as
`k = floor(sqrt(N + ArchiveSize))`. -/
def KthSquaredDistanceAt {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (NeighborIndex : Nat) (x : α) : ℚ :=
  ((Pool.map (SquaredObjectiveDistance Fitness x)).mergeSort
    (fun a b => decide (a ≤ b))).getD NeighborIndex 0

/-- The same raw-fitness/distance comparison with an explicitly supplied neighbor index instead of the current-pool default. -/
def SPEA2FitnessBetterAt {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (NeighborIndex : Nat) (x y : α) : Bool :=
  if RawFitness Fitness Pool x ≠ RawFitness Fitness Pool y then
    decide (RawFitness Fitness Pool x ≤ RawFitness Fitness Pool y)
  else decide (KthSquaredDistanceAt Fitness Pool NeighborIndex y ≤
    KthSquaredDistanceAt Fitness Pool NeighborIndex x)

/-- Sorted squared distances to all other occurrences. Only the same occurrence
is excluded; duplicate genotypes still contribute zero distances. -/
def NeighborDistances {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (j : Fin Pool.length) : List ℚ :=
  (((PopulationIndices Pool).filter (fun i => decide (i ≠ j))).map
    (fun i => SquaredObjectiveDistance Fitness Pool[j] Pool[i])).mergeSort
    (fun a b => decide (a ≤ b))

/-- Lexicographic non-strict comparison of rational lists, with the shorter prefix considered smaller. Truncation compares complete sorted neighbor-distance vectors. -/
def DistanceLexLE : List ℚ → List ℚ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x = y then DistanceLexLE xs ys else decide (x < y)

/-- Remove the lexicographically smallest complete distance vector first;
fully equal vectors use the supplied permutation priority. -/
def SPEA2RemovalOrder {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α)
    (Priority : Equiv.Perm (Fin Pool.length)) (x y : Fin Pool.length) : Bool :=
  let XDistances := NeighborDistances Fitness Pool x
  let YDistances := NeighborDistances Fitness Pool y
  if XDistances = YDistances then decide ((Priority x).val ≤ (Priority y).val)
  else DistanceLexLE XDistances YDistances

/-- Remove one occurrence having the smallest full neighbor-distance vector, breaking complete ties using the supplied permutation. Positive pool length supplies the required index. -/
def SPEA2RemoveClosest {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (PositiveLength : 0 < Pool.length)
    (Priority : Equiv.Perm (Fin Pool.length)) : List α :=
  let DefaultIndex : Fin Pool.length := ⟨0, PositiveLength⟩
  let Sorted := (PopulationIndices Pool).mergeSort (SPEA2RemovalOrder Fitness Pool Priority)
  Pool.eraseIdx (Sorted.getD 0 DefaultIndex).val

theorem SPEA2RemoveClosestLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (PositiveLength : 0 < Pool.length)
    (Priority : Equiv.Perm (Fin Pool.length)) :
    (SPEA2RemoveClosest Fitness Pool PositiveLength Priority).length = Pool.length - 1 := by
  unfold SPEA2RemoveClosest
  apply List.length_eraseIdx_of_lt
  exact Fin.isLt _

noncomputable section

/-- Iterative truncation recomputing distances after each removal.
Fuel bounds the number of removals; the environment supplies the pool length. -/
def SPEA2Truncate {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) : Nat → List α → PMF (List α)
  | 0, Pool => PMF.pure Pool
  | Fuel + 1, Pool =>
      if TooLarge : Capacity < Pool.length then
        (UniformTiePermutation Pool.length).bind (fun Priority =>
          SPEA2Truncate Fitness Capacity Fuel
            (SPEA2RemoveClosest Fitness Pool (lt_of_le_of_lt (Nat.zero_le _) TooLarge) Priority))
      else PMF.pure Pool

theorem SPEA2TruncateLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity Fuel : Nat) (Pool Next : List α)
    (EnoughFuel : Pool.length ≤ Capacity + Fuel)
    (Possible : Next ∈ (SPEA2Truncate Fitness Capacity Fuel Pool).support) :
    Next.length = min Capacity Pool.length := by
  induction Fuel generalizing Pool Next with
  | zero =>
      have NextEqual : Next = Pool := (PMF.mem_support_pure_iff _ _).mp Possible
      have Fits : Pool.length ≤ Capacity := by omega
      rw [NextEqual, Nat.min_eq_right Fits]
  | succ Fuel Previous =>
      unfold SPEA2Truncate at Possible
      split_ifs at Possible with TooLarge
      · obtain ⟨Priority, _, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
        have RemovedLength := SPEA2RemoveClosestLength Fitness Pool
          (lt_of_le_of_lt (Nat.zero_le _) TooLarge) Priority
        have RemainingFuel :
            (SPEA2RemoveClosest Fitness Pool
              (lt_of_le_of_lt (Nat.zero_le _) TooLarge) Priority).length ≤ Capacity + Fuel := by
          rw [RemovedLength]
          omega
        have NextLength := Previous _ Next RemainingFuel NextPossible
        rw [RemovedLength] at NextLength
        have NewFits : Capacity ≤ Pool.length - 1 := by omega
        rw [Nat.min_eq_left NewFits] at NextLength
        rw [Nat.min_eq_left (Nat.le_of_lt TooLarge)]
        exact NextLength
      · have NextEqual : Next = Pool := (PMF.mem_support_pure_iff _ _).mp Possible
        rw [NextEqual, Nat.min_eq_right (Nat.le_of_not_gt TooLarge)]

/-- If nondominated occurrences exceed capacity, truncate them iteratively;
otherwise fill capacity using raw-fitness and density order. -/
def SPEA2Environment {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α) : PMF (List α) :=
  let Nondominated := Pool.filter (fun x => decide (RawFitness Fitness Pool x = 0))
  if Capacity < Nondominated.length then
    SPEA2Truncate Fitness Capacity Nondominated.length Nondominated
  else
    (UniformTiePermutation Pool.length).map (fun Priority =>
      (SelectByOrder Capacity (PopulationIndices Pool) (fun x y =>
        if RawFitness Fitness Pool Pool[x] = RawFitness Fitness Pool Pool[y] ∧
            KthSquaredDistance Fitness Pool Pool[x] = KthSquaredDistance Fitness Pool Pool[y]
        then decide ((Priority x).val ≤ (Priority y).val)
        else SPEA2FitnessBetter Fitness Pool Pool[x] Pool[y])).map (fun j => Pool[j]))

theorem SPEA2EnvironmentLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool Next : List α)
    (Possible : Next ∈ (SPEA2Environment Fitness Capacity Pool).support) :
    Next.length = min Capacity Pool.length := by
  unfold SPEA2Environment at Possible
  dsimp only at Possible
  split_ifs at Possible with TooMany
  · have TruncatedLength := SPEA2TruncateLength Fitness Capacity _ _ Next
      (Nat.le_add_left _ _) Possible
    have FilterLength : (Pool.filter (fun x => decide (RawFitness Fitness Pool x = 0))).length ≤
        Pool.length := List.length_filter_le _ _
    rw [Nat.min_eq_left (Nat.le_of_lt TooMany)] at TruncatedLength
    rw [Nat.min_eq_left (le_trans (Nat.le_of_lt TooMany) FilterLength)]
    exact TruncatedLength
  · obtain ⟨Priority, _, NextEqual⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
    rw [← NextEqual, List.length_map, SelectByOrderLength]
    unfold PopulationIndices
    rw [List.length_ofFn]

/-- Environmental selection with an explicit neighbor index, permitting the
configured-capacity convention instead of the current candidate count. -/
def SPEA2EnvironmentAt {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity NeighborIndex : Nat) (Pool : List α) : PMF (List α) :=
  let Nondominated := Pool.filter (fun x => decide (RawFitness Fitness Pool x = 0))
  if Capacity < Nondominated.length then
    SPEA2Truncate Fitness Capacity Nondominated.length Nondominated
  else
    (UniformTiePermutation Pool.length).map (fun Priority =>
      (SelectByOrder Capacity (PopulationIndices Pool) (fun x y =>
        if RawFitness Fitness Pool Pool[x] = RawFitness Fitness Pool Pool[y] ∧
            KthSquaredDistanceAt Fitness Pool NeighborIndex Pool[x] =
              KthSquaredDistanceAt Fitness Pool NeighborIndex Pool[y]
        then decide ((Priority x).val ≤ (Priority y).val)
        else SPEA2FitnessBetterAt Fitness Pool NeighborIndex Pool[x] Pool[y])).map (fun j => Pool[j]))

theorem SPEA2EnvironmentAtLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Capacity NeighborIndex : Nat) (Pool Next : List α)
    (Possible : Next ∈ (SPEA2EnvironmentAt Fitness Capacity NeighborIndex Pool).support) :
    Next.length = min Capacity Pool.length := by
  unfold SPEA2EnvironmentAt at Possible
  dsimp only at Possible
  split_ifs at Possible with TooMany
  · have TruncatedLength := SPEA2TruncateLength Fitness Capacity _ _ Next
      (Nat.le_add_left _ _) Possible
    have FilterLength : (Pool.filter (fun x => decide (RawFitness Fitness Pool x = 0))).length ≤
        Pool.length := List.length_filter_le _ _
    rw [Nat.min_eq_left (Nat.le_of_lt TooMany)] at TruncatedLength
    rw [Nat.min_eq_left (le_trans (Nat.le_of_lt TooMany) FilterLength)]
    exact TruncatedLength
  · obtain ⟨Priority, _, NextEqual⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
    rw [← NextEqual, List.length_map, SelectByOrderLength]
    unfold PopulationIndices
    rw [List.length_ofFn]

end
end ECTheoryLib.Operators.Selection
