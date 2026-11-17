import ECTheoryLib.Operators.Selection.Population
import ECTheoryLib.SearchSpaces.BitString
import ECTheoryLib.Probability.Processes.Transition

/-!
# Independent population initialization and parent sampling

Uniform parent selection samples occurrences, so repeated genotypes receive
probability proportional to multiplicity. The default parent for an empty list
makes the function total; concrete algorithms treat empty populations separately.
Initialization samples the configured number of independent uniform bit strings.
-/

namespace ECTheoryLib

open Operators.Selection

noncomputable section

/-- Sample Capacity independent uniform bit strings as a list. Repeated genotypes remain separate occurrences; capacity zero returns the empty list. -/
def PopulationInit (n Capacity : Nat) : PMF (List (Bits n)) :=
  IndependentSamples (PMF.uniformOfFintype (Bits n)) Capacity

theorem PopulationInitLength (n Capacity : Nat) (Pool : List (Bits n))
    (Possible : Pool ∈ (PopulationInit n Capacity).support) : Pool.length = Capacity := by
  exact IndependentSamplesLength _ Capacity Pool Possible

/-- Uniform sampling of an occurrence. The default value is used only for an empty pool. -/
def UniformParent {α : Type*} [Inhabited α] (Pool : List α) : PMF α :=
  if PositiveLength : 0 < Pool.length then
    letI : Nonempty (Fin Pool.length) := ⟨⟨0, PositiveLength⟩⟩
    (PMF.uniformOfFintype (Fin Pool.length)).map (fun j => Pool[j])
  else PMF.pure default

theorem UniformParentMember {α : Type*} [Inhabited α] (Pool : List α)
    (PositiveLength : 0 < Pool.length) (x : α)
    (Possible : x ∈ (UniformParent Pool).support) : x ∈ Pool := by
  unfold UniformParent at Possible
  rw [dif_pos PositiveLength] at Possible
  obtain ⟨j, _, ValueEqual⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← ValueEqual]
  exact List.getElem_mem j.isLt

/-- Choose a uniform parent occurrence, then sample from its mutation PMF. -/
def PopulationOffspring {α : Type*} [Inhabited α]
    (Mutation : α → PMF α) (Pool : List α) : PMF α :=
  (UniformParent Pool).bind Mutation

end
end ECTheoryLib
