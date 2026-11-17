import ECTheoryLib.Algorithms.Population
import ECTheoryLib.Operators.Selection.CrowdingDistance
import ECTheoryLib.Operators.Mutation.IndependentBit
import ECTheoryLib.Operators.Mutation.OneBit
import ECTheoryLib.Probability.Processes.Invariant

/-!
# NSGA-II with uniform parents and classical crowding distance

Source: Zheng and Doerr, arXiv:2112.08581, Algorithm 3, uniform-parent variant.
There is no crossover. Each generation samples as many independent offspring as
there are current population occurrences, using the supplied mutation PMF.
Environmental-selection ties use a uniform permutation of occurrence positions.
Time is measured in generations. This module defines the process and its size
invariant; benchmark runtime bounds belong to the analysis layer.
-/

namespace ECTheoryLib

open Operators.Selection

noncomputable section

/-- One generation of the uniform-parent, no-crossover NSGA-II variant. Generate as many offspring as current occurrences, then select that many survivors from the union. The empty population is absorbing. -/
def NSGAIIStep {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (Pool : List α) : PMF (List α) :=
  if Pool.isEmpty then PMF.pure []
  else
    (IndependentSamples (PopulationOffspring Mutation Pool) Pool.length).bind
      (fun Offspring => NSGAIIEnvironment Fitness Pool.length (Pool ++ Offspring))

/-- Every supported successor has the same number of occurrences as its parent population. -/
theorem NSGAIIStepLength {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (Pool Next : List α) (Possible : Next ∈ (NSGAIIStep Mutation Fitness Pool).support) :
    Next.length = Pool.length := by
  unfold NSGAIIStep at Possible
  split_ifs at Possible with Empty
  · have NextEmpty : Next = [] := (PMF.mem_support_pure_iff _ _).mp Possible
    have PoolEmpty : Pool = [] := List.isEmpty_iff.mp Empty
    rw [NextEmpty, PoolEmpty]
  · obtain ⟨Offspring, OffspringPossible, NextPossible⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp Possible
    have OffspringLength : Offspring.length = Pool.length :=
      IndependentSamplesLength _ _ _ OffspringPossible
    have SelectedLength := NSGAIIEnvironmentLength Fitness Pool.length
      (Pool ++ Offspring) Next NextPossible
    rw [List.length_append, OffspringLength, Nat.min_eq_left (Nat.le_add_right _ _)]
      at SelectedLength
    exact SelectedLength

/-- Iterate the actual NSGA-II generation kernel from the supplied initial population distribution. Generations exclude initialization. -/
def NSGAIIRun {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (Initial : PMF (List α)) (Generations : Nat) : PMF (List α) :=
  Probability.Evolve (NSGAIIStep Mutation Fitness) Initial Generations

theorem NSGAIIRunLength {α : Type*} [Inhabited α] {m : Nat}
    (Mutation : α → PMF α) (Fitness : α → Fin m → ℚ)
    (Initial : PMF (List α)) (Capacity : Nat)
    (InitialSize : ∀ Pool ∈ Initial.support, Pool.length = Capacity)
    (Generations : Nat) (Pool : List α)
    (Possible : Pool ∈ (NSGAIIRun Mutation Fitness Initial Generations).support) :
    Pool.length = Capacity := by
  refine Probability.EvolvePreservesProperty (NSGAIIStep Mutation Fitness)
    (fun Pool => Pool.length = Capacity) Initial InitialSize ?_ Generations Pool Possible
  intro Parent ParentSize Next NextPossible
  rw [NSGAIIStepLength Mutation Fitness Parent Next NextPossible, ParentSize]

/-- The standard bit-mutation instance flips each bit independently with probability `1/n`. -/
def NSGAIIStandardBitStep {n m : Nat} (PositiveLength : 0 < n)
    (Fitness : Bits n → Fin m → ℚ) (Pool : List (Bits n)) : PMF (List (Bits n)) :=
  NSGAIIStep (StandardBitMutation PositiveLength) Fitness Pool

/-- The one-bit mutation variant: each offspring flips exactly one uniformly chosen coordinate. -/
def NSGAIIOneBitStep {n m : Nat} (PositiveLength : 0 < n)
    (Fitness : Bits n → Fin m → ℚ) (Pool : List (Bits n)) : PMF (List (Bits n)) :=
  NSGAIIStep (RandomOneBitMutation PositiveLength) Fitness Pool

end
end ECTheoryLib
