import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Finite multi-valued vectors

Each coordinate belongs to `Fin r`. These search objects carry no objective,
selection rule, or algorithm. The discrete measurable structures and function
space instances are inherited from mathlib.
-/

namespace ECTheoryLib

/-- Length-`n` vectors over the alphabet `0, ..., r-1`. -/
abbrev MultiValues (n r : Nat) := Fin n → Fin r

/-- The search space has `r^n` elements, including the standard empty-vector
and empty-alphabet cases. -/
theorem MultiValuesCard (n r : Nat) : Fintype.card (MultiValues n r) = r ^ n := by
  unfold MultiValues
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- A nonempty alphabet supplies a vector of every length. -/
theorem MultiValuesNonempty (n r : Nat) (PositiveAlphabet : 0 < r) :
    Nonempty (MultiValues n r) := by
  exact ⟨fun _ => ⟨0, PositiveAlphabet⟩⟩

/-- Singletons are measurable under the inherited finite discrete structure. -/
theorem MultiValuesSingletonMeasurable {n r : Nat} (State : MultiValues n r) :
    MeasurableSet ({State} : Set (MultiValues n r)) := by
  exact measurableSet_singleton State

end ECTheoryLib
