import ECTheoryLib.Algorithms.Population
import ECTheoryLib.Probability.Processes.Invariant
import ECTheoryLib.Operators.Selection.ReferenceNiching
import ECTheoryLib.Operators.Mutation.IndependentBit

/-!
# NSGA-III with revised normalization and uniform reproduction

Source: Wietheger–Doerr, arXiv:2211.08202, Algorithms 1–3. The state includes
the population and the actual ideal/worst/extreme normalization history. Parent
positions are sampled uniformly, mutation creates an independent population of
equal size, complete Pareto fronts survive, and the splitting front is selected
by reference niching. No crossover is used in this theoretical mutation variant.
All objectives are maximized; normalization internally negates their coordinates.
This is the usual minimization-normalization adaptation to maximizing objectives,
with the standard perpendicular-distance first-occupant rule; it is not a literal
transcription of the 2023 paper's reference-point-distance wording.
-/

namespace ECTheoryLib.Operators.Selection

/-- Group an already sorted position list into consecutive equal-key fronts. -/
def GroupAdjacentByKey {ι : Type*} (Key : ι → Nat) : List ι → List (List ι)
  | [] => []
  | x :: Rest =>
      match GroupAdjacentByKey Key Rest with
      | [] => [[x]]
      | Front :: Fronts =>
          if Key x = Key (Front.head?.getD x) then (x :: Front) :: Fronts
          else [x] :: Front :: Fronts

theorem GroupAdjacentByKeyFlatten {ι : Type*} (Key : ι → Nat) (Items : List ι) :
    (GroupAdjacentByKey Key Items).flatten = Items := by
  induction Items with
  | nil => rfl
  | cons x Rest Previous =>
      unfold GroupAdjacentByKey
      cases Groups : GroupAdjacentByKey Key Rest with
      | nil =>
          rw [Groups] at Previous
          rw [← Previous]
          rfl
      | cons Front Fronts =>
          rw [Groups] at Previous
          dsimp only
          split_ifs
          · change x :: (Front ++ Fronts.flatten) = x :: Rest
            exact congrArg (List.cons x) Previous
          · change x :: (Front ++ Fronts.flatten) = x :: Rest
            exact congrArg (List.cons x) Previous

/-- Sort occurrence indices by nondomination rank and group adjacent equal ranks into fronts, retaining repeated genotypes. -/
def NSGAIIIRankedFronts {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) : List (List (Fin Pool.length)) :=
  let Rank := fun j : Fin Pool.length => ParetoRank Fitness Pool Pool[j]
  GroupAdjacentByKey Rank ((PopulationIndices Pool).mergeSort (fun a b => decide (Rank a ≤ Rank b)))

theorem NSGAIIIRankedFrontsLength {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) :
    (NSGAIIIRankedFronts Fitness Pool).flatten.length = Pool.length := by
  unfold NSGAIIIRankedFronts
  rw [GroupAdjacentByKeyFlatten, List.length_mergeSort]
  exact List.length_ofFn

/-- Complete fronts plus the first front reaching the remaining capacity.
Exact fill remains critical, so its normalization history is still updated. -/
def NSGAIIIFrontSplit {ι : Type*} : Nat → List (List ι) → List ι × List ι
  | _, [] => ([], [])
  | Capacity, Front :: Fronts =>
      if Front.length < Capacity then
        let Rest := NSGAIIIFrontSplit (Capacity - Front.length) Fronts
        (Front ++ Rest.1, Rest.2)
      else ([], Front)

theorem NSGAIIIFrontSplitCapacity {ι : Type*} (Capacity : Nat) (Fronts : List (List ι)) :
    (NSGAIIIFrontSplit Capacity Fronts).1.length +
      min (Capacity - (NSGAIIIFrontSplit Capacity Fronts).1.length)
        (NSGAIIIFrontSplit Capacity Fronts).2.length =
          min Capacity Fronts.flatten.length := by
  induction Fronts generalizing Capacity with
  | nil => simp only [NSGAIIIFrontSplit, List.flatten_nil, List.length_nil,
      Nat.sub_zero, Nat.min_zero, Nat.zero_add]
  | cons Front Fronts Previous =>
      unfold NSGAIIIFrontSplit
      split_ifs with Fits
      · have RestCapacity := Previous (Capacity - Front.length)
        simp only [List.length_append, List.flatten_cons]
        omega
      · simp only [List.length_nil, Nat.sub_zero, Nat.zero_add, List.flatten_cons, List.length_append]
        omega

/-- Current population together with the historical normalization state. History records ideal and worst coordinates and previous extreme vectors; the population alone is not the complete algorithm state. -/
structure NSGAIIIState (α : Type*) (m : Nat) where
  Population : List α
  History : NSGAIIIHistory m

noncomputable section

/-- Select survivors by complete fronts and reference-based niching at the splitting front. Observe all candidates for history, including later discarded offspring; normalization and association are computed from the stated front sets. -/
def NSGAIIIEnvironment {α : Type*} {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α)
    (History : NSGAIIIHistory m) : PMF (NSGAIIIState α m) :=
  let Fronts := NSGAIIIRankedFronts Fitness Pool
  let Plan := NSGAIIIFrontSplit Capacity Fronts
  let Accepted := Plan.1
  let Critical := Plan.2
  let Needed := Capacity - Accepted.length
  let Observed := Pool.map (MinimizationVector Fitness)
  if Needed = 0 then
    PMF.pure
      { Population := Accepted.map (fun j => Pool[j])
        History := NSGAIIIObserve History Observed }
  else
    let Retained := (Accepted ++ Critical).map (fun j => MinimizationVector Fitness Pool[j])
    let First := (RankFront Fitness Pool 0).map (fun j => MinimizationVector Fitness Pool[j])
    let Normalization := NSGAIIINormalize Parameters History Observed Retained First
    let Normalized := fun j : Fin Pool.length =>
      NSGAIIINormalizedVector Normalization (MinimizationVector Fitness Pool[j])
    (SampleReferenceAssociations References Normalized (Accepted ++ Critical)).bind (fun Association =>
      (ReferenceNiching References Normalized Association Needed Critical Accepted).map (fun Chosen =>
        { Population := (Accepted ++ Chosen).map (fun j => Pool[j]),
          History := Normalization.History }))

/-- Environmental selection fills capacity whenever enough individuals exist. -/
theorem NSGAIIIEnvironmentLength {α : Type*} {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α)
    (History : NSGAIIIHistory m) (Next : NSGAIIIState α m)
    (Possible : Next ∈ (NSGAIIIEnvironment Parameters References Fitness Capacity Pool History).support) :
    Next.Population.length = min Capacity Pool.length := by
  have SplitCapacity := NSGAIIIFrontSplitCapacity Capacity (NSGAIIIRankedFronts Fitness Pool)
  rw [NSGAIIIRankedFrontsLength] at SplitCapacity
  unfold NSGAIIIEnvironment at Possible
  dsimp only at Possible
  split_ifs at Possible with NoNeed
  · have Equality := (PMF.mem_support_pure_iff _ _).mp Possible
    rw [Equality, List.length_map]
    rw [NoNeed, Nat.zero_min, Nat.add_zero] at SplitCapacity
    exact SplitCapacity
  · obtain ⟨Association, _AssociationPossible, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
    obtain ⟨Chosen, ChosenPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp NextPossible
    have ChosenLength := ReferenceNichingLength _ _ Association _ _ _ Chosen ChosenPossible
    rw [← Equality, List.length_map, List.length_append, ChosenLength]
    exact SplitCapacity

theorem NSGAIIIEnvironmentMember {α : Type*} {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α)
    (History : NSGAIIIHistory m) (Next : NSGAIIIState α m)
    (Possible : Next ∈ (NSGAIIIEnvironment Parameters References Fitness Capacity Pool History).support)
    (x : α) (InNext : x ∈ Next.Population) : x ∈ Pool := by
  unfold NSGAIIIEnvironment at Possible
  dsimp only at Possible
  split_ifs at Possible with NoNeed
  · have Equality := (PMF.mem_support_pure_iff _ _).mp Possible
    rw [Equality] at InNext
    obtain ⟨j, _InSelected, ValueEquals⟩ := List.mem_map.mp InNext
    rw [← ValueEquals]
    exact List.getElem_mem j.isLt
  · obtain ⟨Association, _AssociationPossible, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
    obtain ⟨Chosen, _ChosenPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp NextPossible
    rw [← Equality] at InNext
    obtain ⟨j, _InSelected, ValueEquals⟩ := List.mem_map.mp InNext
    rw [← ValueEquals]
    exact List.getElem_mem j.isLt

theorem NSGAIIIEnvironmentHistory {α : Type*} {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α)
    (History : NSGAIIIHistory m) (Next : NSGAIIIState α m)
    (Possible : Next ∈ (NSGAIIIEnvironment Parameters References Fitness Capacity Pool History).support)
    (i : Fin m) : Next.History.Ideal i ≤ History.Ideal i ∧ History.Worst i ≤ Next.History.Worst i := by
  unfold NSGAIIIEnvironment at Possible
  dsimp only at Possible
  split_ifs at Possible with NoNeed
  · have Equality := (PMF.mem_support_pure_iff _ _).mp Possible
    rw [Equality]
    exact ⟨NSGAIIIObserveIdeal History _ i, NSGAIIIObserveWorst History _ i⟩
  · obtain ⟨Association, _AssociationPossible, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
    obtain ⟨Chosen, _ChosenPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp NextPossible
    rw [← Equality]
    exact ⟨NSGAIIIObserveIdeal History (Pool.map (MinimizationVector Fitness)) i,
      NSGAIIIObserveWorst History (Pool.map (MinimizationVector Fitness)) i⟩

/-- Every call selecting a critical front refreshes all extreme vectors.
This includes exact-fill fronts because the split uses a strict comparison. -/
theorem NSGAIIIEnvironmentExtremeCount {α : Type*} {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Fitness : α → Fin m → ℚ) (Capacity : Nat) (Pool : List α)
    (History : NSGAIIIHistory m) (Next : NSGAIIIState α m)
    (CriticalSelection : 0 < Capacity -
      (NSGAIIIFrontSplit Capacity (NSGAIIIRankedFronts Fitness Pool)).1.length)
    (Possible : Next ∈ (NSGAIIIEnvironment Parameters References Fitness Capacity Pool History).support) :
    Next.History.Extremes.length = m := by
  unfold NSGAIIIEnvironment at Possible
  dsimp only at Possible
  split_ifs at Possible with NoNeed
  · rw [NoNeed] at CriticalSelection
    exact False.elim (lt_irrefl 0 CriticalSelection)
  · obtain ⟨Association, _AssociationPossible, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
    obtain ⟨Chosen, _ChosenPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp NextPossible
    rw [← Equality]
    exact List.length_ofFn

end
end ECTheoryLib.Operators.Selection

namespace ECTheoryLib

open Operators.Selection

noncomputable section

/-- Independently initialize the configured number of uniform bit strings and construct their initial normalization history. -/
def NSGAIIIInit (n m Capacity : Nat) (Fitness : Bits n → Fin m → ℚ) :
    PMF (NSGAIIIState (Bits n) m) :=
  (PopulationInit n Capacity).map (fun Pool =>
    { Population := Pool, History := NSGAIIIInitialHistory Fitness Pool })

theorem NSGAIIIInitLength (n m Capacity : Nat) (Fitness : Bits n → Fin m → ℚ)
    (State : NSGAIIIState (Bits n) m) (Possible : State ∈ (NSGAIIIInit n m Capacity Fitness).support) :
    State.Population.length = Capacity := by
  obtain ⟨Pool, PoolPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← Equality]
  exact PopulationInitLength n Capacity Pool PoolPossible

/-- One no-crossover generation with uniform parent occurrences and independent offspring. An empty population preserves its complete state; otherwise the environment updates both population and history. -/
def NSGAIIIStep {α : Type*} [Inhabited α] {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (State : NSGAIIIState α m) : PMF (NSGAIIIState α m) :=
  if State.Population.isEmpty then PMF.pure State
  else
    (IndependentSamples (PopulationOffspring Mutation State.Population) State.Population.length).bind
      (fun Offspring => NSGAIIIEnvironment Parameters References Fitness State.Population.length
        (State.Population ++ Offspring) State.History)

theorem NSGAIIIStepLength {α : Type*} [Inhabited α] {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (State Next : NSGAIIIState α m)
    (Possible : Next ∈ (NSGAIIIStep Parameters References Mutation Fitness State).support) :
    Next.Population.length = State.Population.length := by
  unfold NSGAIIIStep at Possible
  split_ifs at Possible with Empty
  · have Equality := (PMF.mem_support_pure_iff _ _).mp Possible
    rw [Equality]
  · obtain ⟨Offspring, OffspringPossible, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
    have OffspringLength := IndependentSamplesLength _ _ _ OffspringPossible
    have SelectedLength := NSGAIIIEnvironmentLength Parameters References Fitness
      State.Population.length (State.Population ++ Offspring) State.History Next NextPossible
    rw [List.length_append, OffspringLength, Nat.min_eq_left (Nat.le_add_right _ _)] at SelectedLength
    exact SelectedLength

theorem NSGAIIIStepHistory {α : Type*} [Inhabited α] {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (State Next : NSGAIIIState α m)
    (Possible : Next ∈ (NSGAIIIStep Parameters References Mutation Fitness State).support)
    (i : Fin m) : Next.History.Ideal i ≤ State.History.Ideal i ∧
      State.History.Worst i ≤ Next.History.Worst i := by
  unfold NSGAIIIStep at Possible
  split_ifs at Possible with Empty
  · have Equality := (PMF.mem_support_pure_iff _ _).mp Possible
    rw [Equality]
    exact ⟨le_rfl, le_rfl⟩
  · obtain ⟨Offspring, _OffspringPossible, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
    exact NSGAIIIEnvironmentHistory Parameters References Fitness State.Population.length
      (State.Population ++ Offspring) State.History Next NextPossible i

/-- The full-state law after a specified number of NSGA-III generations, retaining normalization history across transitions. -/
def NSGAIIIRun {α : Type*} [Inhabited α] {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (Initial : PMF (NSGAIIIState α m)) (Generations : Nat) : PMF (NSGAIIIState α m) :=
  Probability.Evolve (NSGAIIIStep Parameters References Mutation Fitness) Initial Generations

theorem NSGAIIIRunLength {α : Type*} [Inhabited α] {m : Nat}
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (Initial : PMF (NSGAIIIState α m)) (Capacity : Nat)
    (InitialSize : ∀ State ∈ Initial.support, State.Population.length = Capacity)
    (Generations : Nat) (Next : NSGAIIIState α m)
    (Possible : Next ∈ (NSGAIIIRun Parameters References Mutation Fitness Initial Generations).support) :
    Next.Population.length = Capacity := by
  apply Probability.EvolvePreservesProperty
    (NSGAIIIStep Parameters References Mutation Fitness)
    (fun State => State.Population.length = Capacity) Initial InitialSize
    (Time := Generations) (x := Next) (Possible := Possible)
  intro State StateSize Child ChildPossible
  rw [NSGAIIIStepLength Parameters References Mutation Fitness State Child ChildPossible]
  exact StateSize

/-- Specialize the full-state NSGA-III kernel to independent bit mutation with probability 1/n. -/
def NSGAIIIStandardBitStep {n m : Nat} (PositiveLength : 0 < n)
    (Parameters : NSGAIIINormalizationParameters) (References : ReferenceSystem m)
    (Fitness : Bits n → Fin m → ℚ) (State : NSGAIIIState (Bits n) m) :
    PMF (NSGAIIIState (Bits n) m) :=
  NSGAIIIStep Parameters References (StandardBitMutation PositiveLength) Fitness State

end
end ECTheoryLib
