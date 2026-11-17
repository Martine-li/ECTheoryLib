import ECTheoryLib.Operators.Selection.ParetoArchive
import ECTheoryLib.Probability.Processes.Transition

/-!
# Archive search with explicit parent and mutation policies

One iteration chooses a parent, samples an offspring from its mutation PMF, and
performs the existing Pareto archive update. The caller supplies both policies.
This definition is the common transition underlying SEMO and GSEMO; it does not
assume that a supplied parent policy is uniform or supported by the archive.
Applications state any such requirements explicitly.
-/
namespace ECTheoryLib
noncomputable section

/-- Compose a parent PMF, a mutation kernel, and the standard Pareto archive update. -/
def ArchiveSearchStep {α : Type*} [DecidableEq α]
    (Parent : ParetoPopulation α → PMF α) (Mutation : α → PMF α)
    (Dominates : α → α → Prop) [DecidableRel Dominates]
    (P : ParetoPopulation α) : PMF (ParetoPopulation α) :=
  (Parent P).bind (fun x => (Mutation x).map (ParetoPopulationUpdate Dominates P))

/-- Every possible successor is an actual archive update of a supported offspring
from a supported parent. This exposes the model's full transition semantics. -/
theorem ArchiveSearchStepSupport {α : Type*} [DecidableEq α]
    (Parent : ParetoPopulation α → PMF α) (Mutation : α → PMF α)
    (Dominates : α → α → Prop) [DecidableRel Dominates]
    (P Q : ParetoPopulation α) :
    Q ∈ (ArchiveSearchStep Parent Mutation Dominates P).support ↔
      ∃ x ∈ (Parent P).support, ∃ y ∈ (Mutation x).support,
        ParetoPopulationUpdate Dominates P y = Q := by
  unfold ArchiveSearchStep
  rw [PMF.mem_support_bind_iff]
  simp only [PMF.mem_support_map_iff]

end
end ECTheoryLib
