import Mathlib.Data.Finset.Image

/-!
# Current coverage of a finite target set

`ObservedValues` records objective values currently represented by a finite
collection of search points. `CoversTargets` concerns simultaneous current
coverage, not historical discovery. An application specifies and proves the
target set; these definitions do not presume that every target is Pareto optimal.
-/
namespace ECTheoryLib.Problems

/-- Objective values represented in the current archive, ignoring duplicate representatives. -/
def ObservedValues {α β : Type*} [DecidableEq β] (Value : α → β)
    (Archive : Finset α) : Finset β := Archive.image Value

/-- Every specified target value currently has a representative in the archive. -/
def CoversTargets {α β : Type*} [DecidableEq β] (Value : α → β)
    (Targets : Finset β) (Archive : Finset α) : Prop :=
  Targets ⊆ ObservedValues Value Archive

/-- Coverage is equivalent to the existence of a current representative for every target. -/
theorem CoversTargetsIff {α β : Type*} [DecidableEq β] (Value : α → β)
    (Targets : Finset β) (Archive : Finset α) :
    CoversTargets Value Targets Archive ↔
      ∀ v ∈ Targets, ∃ x ∈ Archive, Value x = v := by
  simp only [CoversTargets, ObservedValues, Finset.subset_iff, Finset.mem_image]

end ECTheoryLib.Problems
