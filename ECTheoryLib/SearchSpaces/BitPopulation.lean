import ECTheoryLib.SearchSpaces.BitString
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Discrete ordered populations of bit strings

The raw list state retains occurrence order and genotype multiplicities. Its
measurable structure is discrete. All lists form a countable type; an algorithm's
fixed-size invariant is a separate property, not an identification of duplicates.
-/
namespace ECTheoryLib

/-- The discrete sigma-algebra on ordered bit-string populations. -/
instance BitPopulationMeasurableSpace (n : ℕ) : MeasurableSpace (List (Bits n)) := ⊤

/-- Every individual population state is measurable in the discrete sigma-algebra. -/
instance BitPopulationMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (List (Bits n)) := ⟨fun _ => trivial⟩

end ECTheoryLib
