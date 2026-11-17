import ECTheoryLib.Probability.PMF.SupportedSubtype
import ECTheoryLib.Probability.Processes.Transition
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Vector.Basic

/-!
# Fixed-size list population representations

A population is a list with a length proof, equivalent to a function on Fin N.
Occurrences, their order, and repeated genotypes are all retained. Attaching the
length proof to a supported law does not condition or renormalize it. The forget
equations expose exact equality with the supplied raw-list initialization or
transition; runtime statements can therefore remain on that original process.
-/
namespace ECTheoryLib
open Probability
noncomputable section

/-- A list of exactly N occurrences; duplicate individuals remain distinct positions. -/
abbrev FixedPopulation (α : Type*) (N : ℕ) := List.Vector α N

/-- Lossless indexed representation of a fixed-length population. -/
def FixedPopulationEquivFin (α : Type*) (N : ℕ) : FixedPopulation α N ≃ (Fin N → α) :=
  Equiv.vectorEquivFin α N

/-- Regard a law supported on length N as a law on fixed-size populations. -/
def FixedPopulationLaw {α : Type*} (p : PMF (List α)) (N : ℕ)
    (Length : ∀ P ∈ p.support, P.length = N) : PMF (FixedPopulation α N) :=
  SupportedSubtype p (fun P => P.length = N) Length

/-- Forgetting the length proof recovers the supplied raw-list law exactly. -/
theorem FixedPopulationLawForget {α : Type*} (p : PMF (List α)) (N : ℕ)
    (Length : ∀ P ∈ p.support, P.length = N) :
    (FixedPopulationLaw p N Length).map Subtype.val = p :=
  SupportedSubtypeForget p (fun P => P.length = N) Length

/-- Restrict a length-preserving raw-list kernel without changing any transition
probabilities or the ordering and multiplicity of population occurrences. -/
def FixedPopulationStep {α : Type*} (Step : Transition (List α))
    (PreservesLength : ∀ P Q, Q ∈ (Step P).support → Q.length = P.length) (N : ℕ) :
    Transition (FixedPopulation α N) := fun P =>
  FixedPopulationLaw (Step P.val) N (fun Q Possible => (PreservesLength P.val Q Possible).trans P.property)

/-- One fixed-size transition followed by forgetting its length proof is exactly
the original transition from the same ordered list. -/
theorem FixedPopulationStepForget {α : Type*} (Step : Transition (List α))
    (PreservesLength : ∀ P Q, Q ∈ (Step P).support → Q.length = P.length) (N : ℕ)
    (P : FixedPopulation α N) :
    (FixedPopulationStep Step PreservesLength N P).map Subtype.val = Step P.val :=
  FixedPopulationLawForget _ _ _

end
end ECTheoryLib
