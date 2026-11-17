import ECTheoryLib.Algorithms.Population
import ECTheoryLib.Operators.Selection.Strength
import ECTheoryLib.Operators.Mutation.IndependentBit
import ECTheoryLib.Probability.Processes.Invariant

/-!
# SPEA2 with discrete mutation

The state records an offspring population and a separate elite archive. Each
generation selects from their union using strength, density, and iterative
truncation, then samples parents from the new archive by binary tournaments
with replacement. Mutation produces as many offspring as the current population;
there is no crossover. Ties retain the first independently sampled tournament
participant. The initial archive is empty.

The neighbor index is `floor(sqrt(N + ArchiveSize))`, based on configured capacities,
so the initially empty archive does not change it. Time counts generations.
This module defines the algorithm and size invariants, not benchmark runtime bounds.
-/

namespace ECTheoryLib

open Operators.Selection

/-- Offspring population and separate elite archive, both as occurrence-preserving lists. The archive is empty at standard initialization. -/
structure SPEA2State (α : Type*) where
  Population : List α
  Archive : List α

noncomputable section

/-- Independent uniform initialization of the configured population size, paired with an empty elite archive. -/
def SPEA2Init (n PopulationSize : Nat) : PMF (SPEA2State (Bits n)) :=
  (PopulationInit n PopulationSize).map (fun Pool => ⟨Pool, []⟩)

theorem SPEA2InitPopulationSize (n PopulationSize : Nat) (State : SPEA2State (Bits n))
    (Possible : State ∈ (SPEA2Init n PopulationSize).support) :
    State.Population.length = PopulationSize ∧ State.Archive = [] := by
  obtain ⟨Pool, PoolPossible, StateEqual⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← StateEqual]
  exact ⟨PopulationInitLength n PopulationSize Pool PoolPossible, rfl⟩

/-- Tournament candidates come from the new archive, while fitness is computed
in the previous combined population. -/
def SPEA2Tournament {α : Type*} [Inhabited α] {m : Nat}
    (Fitness : α → Fin m → ℚ) (Combined Archive : List α) : PMF α :=
  (UniformParent Archive).bind (fun First =>
    (UniformParent Archive).map (fun Second =>
      if SPEA2FitnessBetter Fitness Combined First Second then First else Second))

/-- Binary tournament with an explicit density-neighbor index. Candidates are sampled with replacement from the archive; comparisons use the combined pool, with ties retaining the first draw. -/
def SPEA2TournamentAt {α : Type*} [Inhabited α] {m : Nat}
    (Fitness : α → Fin m → ℚ) (Combined Archive : List α) (NeighborIndex : Nat) : PMF α :=
  (UniformParent Archive).bind (fun First =>
    (UniformParent Archive).map (fun Second =>
      if SPEA2FitnessBetterAt Fitness Combined NeighborIndex First Second then First else Second))

/-- A tournament on a nonempty archive returns an archive member; no default
parent is used in this case. -/
theorem SPEA2TournamentAtMember {α : Type*} [Inhabited α] {m : Nat}
    (Fitness : α → Fin m → ℚ) (Combined Archive : List α) (NeighborIndex : Nat)
    (PositiveArchive : 0 < Archive.length) (Parent : α)
    (Possible : Parent ∈ (SPEA2TournamentAt Fitness Combined Archive NeighborIndex).support) :
    Parent ∈ Archive := by
  obtain ⟨First, FirstPossible, ParentPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
  obtain ⟨Second, SecondPossible, ParentEqual⟩ := (PMF.mem_support_map_iff _ _ _).mp ParentPossible
  split_ifs at ParentEqual
  · rw [← ParentEqual]
    exact UniformParentMember Archive PositiveArchive First FirstPossible
  · rw [← ParentEqual]
    exact UniformParentMember Archive PositiveArchive Second SecondPossible

/-- Select the new archive from population plus archive, then generate the current population's number of offspring using archive tournaments and mutation. The neighbor index uses the configured archive capacity. -/
def SPEA2Step {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ) (ArchiveSize : Nat)
    (State : SPEA2State α) : PMF (SPEA2State α) :=
  let Combined := State.Population ++ State.Archive
  let NeighborIndex := Nat.sqrt (State.Population.length + ArchiveSize)
  (SPEA2EnvironmentAt Fitness ArchiveSize NeighborIndex Combined).bind (fun Archive =>
    (IndependentSamples
      ((SPEA2TournamentAt Fitness Combined Archive NeighborIndex).bind Mutation) State.Population.length).map
      (fun Population => ⟨Population, Archive⟩))

/-- Offspring count is preserved and archive size is bounded by capacity.
When fewer candidates are available, all of them are retained. -/
theorem SPEA2StepSizes {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ) (ArchiveSize : Nat)
    (State Next : SPEA2State α)
    (Possible : Next ∈ (SPEA2Step Mutation Fitness ArchiveSize State).support) :
    Next.Population.length = State.Population.length ∧
      Next.Archive.length = min ArchiveSize (State.Population.length + State.Archive.length) := by
  obtain ⟨Archive, ArchivePossible, NextPossible⟩ :=
    (PMF.mem_support_bind_iff _ _ _).mp Possible
  obtain ⟨Population, PopulationPossible, NextEqual⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp NextPossible
  rw [← NextEqual]
  constructor
  · exact IndependentSamplesLength _ _ _ PopulationPossible
  · have ArchiveLength := SPEA2EnvironmentAtLength Fitness ArchiveSize
      (Nat.sqrt (State.Population.length + ArchiveSize))
      (State.Population ++ State.Archive) Archive ArchivePossible
    rw [List.length_append] at ArchiveLength
    exact ArchiveLength

theorem SPEA2StepArchivePositive {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ) (ArchiveSize : Nat)
    (PositiveArchive : 0 < ArchiveSize) (State Next : SPEA2State α)
    (PositivePopulation : 0 < State.Population.length)
    (Possible : Next ∈ (SPEA2Step Mutation Fitness ArchiveSize State).support) :
    0 < Next.Archive.length := by
  have Size := (SPEA2StepSizes Mutation Fitness ArchiveSize State Next Possible).2
  rw [Size]
  exact lt_min PositiveArchive (lt_of_lt_of_le PositivePopulation (Nat.le_add_right _ _))

/-- Standard bit-string instance with positive length and archive capacity.
Positive capacity supplies a parent whenever the candidate pool is nonempty. -/
def SPEA2StandardBitStep {n m : Nat} (PositiveLength : 0 < n)
    (Fitness : Bits n → Fin m → ℚ) (ArchiveSize : Nat) (_PositiveArchive : 0 < ArchiveSize)
    (State : SPEA2State (Bits n)) : PMF (SPEA2State (Bits n)) :=
  SPEA2Step (StandardBitMutation PositiveLength) Fitness ArchiveSize State

/-- Distribution of both population and archive after the specified number of generations, from the supplied initial full-state law. -/
def SPEA2Run {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ) (ArchiveSize : Nat)
    (Initial : PMF (SPEA2State α)) (Generations : Nat) : PMF (SPEA2State α) :=
  Probability.Evolve (SPEA2Step Mutation Fitness ArchiveSize) Initial Generations

/-- A run from positive-sized initialization preserves population size and
never exceeds the configured archive capacity. -/
theorem SPEA2RunSizes {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ) (ArchiveSize PopulationSize : Nat)
    (Initial : PMF (SPEA2State α))
    (InitialSizes : ∀ State ∈ Initial.support,
      State.Population.length = PopulationSize ∧ State.Archive.length ≤ ArchiveSize)
    (Generations : Nat) (State : SPEA2State α)
    (Possible : State ∈ (SPEA2Run Mutation Fitness ArchiveSize Initial Generations).support) :
    State.Population.length = PopulationSize ∧ State.Archive.length ≤ ArchiveSize := by
  refine Probability.EvolvePreservesProperty (SPEA2Step Mutation Fitness ArchiveSize)
    (fun State => State.Population.length = PopulationSize ∧ State.Archive.length ≤ ArchiveSize)
    Initial InitialSizes ?_ Generations State Possible
  intro Parent ParentSizes Next NextPossible
  have Sizes := SPEA2StepSizes Mutation Fitness ArchiveSize Parent Next NextPossible
  constructor
  · rw [Sizes.1]
    exact ParentSizes.1
  · rw [Sizes.2]
    exact Nat.min_le_left _ _

end
end ECTheoryLib
