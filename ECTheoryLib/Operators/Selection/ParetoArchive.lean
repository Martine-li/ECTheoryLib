import Mathlib.Probability.Distributions.Uniform

/-!
# Pareto archive update

`WeaklyDominates a b` means that `a` is at least as good as `b` in every objective.
This module implements the (G)SEMO convention of rejecting strictly dominated
offspring and replacing all points weakly dominated by an accepted offspring.
Thus a new representative replaces old points with the same objective vector.
The archive is a finite set, so identical decision vectors cannot be duplicated.

The relation is supplied by the application; no particular benchmark is imported.
Source: Horoba and Neumann, GECCO 2008, Algorithm 1,
https://cs.adelaide.edu.au/~frank/papers/gecco_dominance.pdf .
-/

namespace ECTheoryLib

/-- Strict dominance: weak dominance in one direction but not the reverse. -/
abbrev StrictDominates {α : Type*} (WeaklyDominates : α → α → Prop) (a b : α) : Prop :=
  WeaklyDominates a b ∧ ¬ WeaklyDominates b a

/-- Accepted when no existing point strictly dominates the candidate. -/
abbrev ParetoArchiveAccepts {α : Type*} (WeaklyDominates : α → α → Prop)
    (Archive : Finset α) (Candidate : α) : Prop :=
  ∀ Parent ∈ Archive, ¬ StrictDominates WeaklyDominates Parent Candidate

/-- Insert the accepted offspring and remove every point it weakly dominates. -/
def ParetoArchiveUpdate {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) [DecidableRel WeaklyDominates]
    (Archive : Finset α) (Candidate : α) : Finset α :=
  if ParetoArchiveAccepts WeaklyDominates Archive Candidate then
    insert Candidate (Archive.filter (fun Parent => ¬ WeaklyDominates Candidate Parent))
  else Archive

/-- A finite archive has pairwise incomparable objective vectors, including no objective ties. -/
def ParetoArchiveValid {α : Type*} (WeaklyDominates : α → α → Prop)
    (Archive : Finset α) : Prop :=
  ∀ a ∈ Archive, ∀ b ∈ Archive, a ≠ b → ¬ WeaklyDominates a b

theorem ParetoArchiveUpdateAccept {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) [DecidableRel WeaklyDominates]
    (Archive : Finset α) (Candidate : α)
    (Accepted : ParetoArchiveAccepts WeaklyDominates Archive Candidate) :
    ParetoArchiveUpdate WeaklyDominates Archive Candidate =
      insert Candidate (Archive.filter (fun Parent => ¬ WeaklyDominates Candidate Parent)) := by
  unfold ParetoArchiveUpdate
  rw [if_pos Accepted]

theorem ParetoArchiveUpdateReject {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) [DecidableRel WeaklyDominates]
    (Archive : Finset α) (Candidate : α)
    (Rejected : ¬ ParetoArchiveAccepts WeaklyDominates Archive Candidate) :
    ParetoArchiveUpdate WeaklyDominates Archive Candidate = Archive := by
  unfold ParetoArchiveUpdate
  rw [if_neg Rejected]

theorem ParetoArchiveCandidateMem {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) [DecidableRel WeaklyDominates]
    (Archive : Finset α) (Candidate : α)
    (Accepted : ParetoArchiveAccepts WeaklyDominates Archive Candidate) :
    Candidate ∈ ParetoArchiveUpdate WeaklyDominates Archive Candidate := by
  rw [ParetoArchiveUpdateAccept WeaklyDominates Archive Candidate Accepted]
  exact Finset.mem_insert_self Candidate _

theorem ParetoArchiveUpdateMembership {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) [DecidableRel WeaklyDominates]
    (Archive : Finset α) (Candidate z : α)
    (Accepted : ParetoArchiveAccepts WeaklyDominates Archive Candidate) :
    z ∈ ParetoArchiveUpdate WeaklyDominates Archive Candidate ↔
      z = Candidate ∨ (z ∈ Archive ∧ ¬ WeaklyDominates Candidate z) := by
  rw [ParetoArchiveUpdateAccept WeaklyDominates Archive Candidate Accepted]
  rw [Finset.mem_insert, Finset.mem_filter]

theorem ParetoArchiveUpdateNonempty {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) [DecidableRel WeaklyDominates]
    (Archive : Finset α) (Candidate : α) (NonemptyArchive : Archive.Nonempty) :
    (ParetoArchiveUpdate WeaklyDominates Archive Candidate).Nonempty := by
  by_cases Accepted : ParetoArchiveAccepts WeaklyDominates Archive Candidate
  · exact ⟨Candidate, ParetoArchiveCandidateMem WeaklyDominates Archive Candidate Accepted⟩
  · rw [ParetoArchiveUpdateReject WeaklyDominates Archive Candidate Accepted]
    exact NonemptyArchive

/-- The update preserves the pairwise nondominance invariant.
No transitivity assumption is hidden here: acceptance and removal suffice. -/
theorem ParetoArchiveUpdateValid {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) [DecidableRel WeaklyDominates]
    (Archive : Finset α) (Candidate : α)
    (Valid : ParetoArchiveValid WeaklyDominates Archive) :
    ParetoArchiveValid WeaklyDominates
      (ParetoArchiveUpdate WeaklyDominates Archive Candidate) := by
  by_cases Accepted : ParetoArchiveAccepts WeaklyDominates Archive Candidate
  · intro a aMem b bMem Different Dominance
    rw [ParetoArchiveUpdateMembership WeaklyDominates Archive Candidate a Accepted] at aMem
    rw [ParetoArchiveUpdateMembership WeaklyDominates Archive Candidate b Accepted] at bMem
    rcases aMem with aCandidate | aOld
    · rcases bMem with bCandidate | bOld
      · exact Different (aCandidate.trans bCandidate.symm)
      · rw [aCandidate] at Dominance
        exact bOld.2 Dominance
    · rcases bMem with bCandidate | bOld
      · rw [bCandidate] at Dominance
        exact Accepted a aOld.1 ⟨Dominance, aOld.2⟩
      · exact Valid a aOld.1 b bOld.1 Different Dominance
  · rw [ParetoArchiveUpdateReject WeaklyDominates Archive Candidate Accepted]
    exact Valid

theorem ParetoArchiveSingletonValid {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) (x : α) :
    ParetoArchiveValid WeaklyDominates {x} := by
  intro a aMem b bMem Different
  have aEquals : a = x := Finset.mem_singleton.mp aMem
  have bEquals : b = x := Finset.mem_singleton.mp bMem
  exact False.elim (Different (aEquals.trans bEquals.symm))

/-- Algorithm states have nonempty archives, so uniform parent selection is defined. -/
abbrev ParetoPopulation (α : Type*) := {Archive : Finset α // Archive.Nonempty}

/-- Construct a nonempty archive containing one search point. -/
def ParetoPopulationSingleton {α : Type*} [DecidableEq α] (x : α) : ParetoPopulation α :=
  ⟨{x}, Finset.singleton_nonempty x⟩

/-- Apply the existing archive update while retaining the proof that the resulting archive is nonempty. -/
def ParetoPopulationUpdate {α : Type*} [DecidableEq α]
    (WeaklyDominates : α → α → Prop) [DecidableRel WeaklyDominates]
    (Population : ParetoPopulation α) (Candidate : α) : ParetoPopulation α :=
  ⟨ParetoArchiveUpdate WeaklyDominates Population.val Candidate,
    ParetoArchiveUpdateNonempty WeaklyDominates Population.val Candidate Population.property⟩

noncomputable section

/-- Each current archive member has selection probability `1 / |Population|`. -/
def UniformParetoParent {α : Type*} (Population : ParetoPopulation α) : PMF α :=
  PMF.uniformOfFinset Population.val Population.property

theorem UniformParetoParentProbability {α : Type*} (Population : ParetoPopulation α)
    (Parent : α) (Membership : Parent ∈ Population.val) :
    UniformParetoParent Population Parent = (Population.val.card : ENNReal)⁻¹ := by
  exact PMF.uniformOfFinset_apply_of_mem Population.property Membership

theorem UniformParetoParentSupport {α : Type*} (Population : ParetoPopulation α)
    (Parent : α) : Parent ∈ (UniformParetoParent Population).support ↔ Parent ∈ Population.val := by
  exact PMF.mem_support_uniformOfFinset_iff Population.property Parent

end
end ECTheoryLib
