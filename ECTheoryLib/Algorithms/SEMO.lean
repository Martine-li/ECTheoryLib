import ECTheoryLib.Operators.Mutation.OneBit
import ECTheoryLib.Operators.Selection.ParetoArchive
import ECTheoryLib.Probability.Processes.Transition

/-!
# Simple evolutionary multiobjective optimizer

SEMO keeps a nonempty Pareto archive, selects one member uniformly, flips one
uniformly selected bit, and performs the Pareto archive update. The strict
dominance rejection / weak dominance removal convention replaces objective ties.
Initialization is a singleton drawn uniformly from the bitstrings. These are
transition and invariant results, not runtime bounds.
Mutation and initialization source: Doerr, Krejca and Opris, IJCAI 2025,
Section 3.1, https://www.ijcai.org/proceedings/2025/0987.pdf .
-/

namespace ECTheoryLib

noncomputable section

/-- Initialize a singleton archive with one uniformly sampled bit string. -/
def SEMOInit (n : Nat) : PMF (ParetoPopulation (Bits n)) :=
  (PMF.uniformOfFintype (Bits n)).map ParetoPopulationSingleton

/-- One SEMO iteration: uniformly choose a current member, flip one uniformly chosen bit, then perform the supplied Pareto archive update. -/
def SEMOStep {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Population : ParetoPopulation (Bits n)) : PMF (ParetoPopulation (Bits n)) :=
  (UniformParetoParent Population).bind (fun Parent =>
    (RandomOneBitMutation PositiveLength Parent).map
      (ParetoPopulationUpdate WeaklyDominates Population))

theorem SEMOStepSupport {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Population Next : ParetoPopulation (Bits n)) :
    Next ∈ (SEMOStep PositiveLength WeaklyDominates Population).support ↔
      ∃ Parent ∈ Population.val,
        ∃ Candidate ∈ (RandomOneBitMutation PositiveLength Parent).support,
          ParetoPopulationUpdate WeaklyDominates Population Candidate = Next := by
  unfold SEMOStep
  rw [PMF.mem_support_bind_iff]
  simp only [UniformParetoParentSupport, PMF.mem_support_map_iff]

theorem SEMOInitValid {n : Nat} (WeaklyDominates : Bits n → Bits n → Prop)
    (Population : ParetoPopulation (Bits n)) (Possible : Population ∈ (SEMOInit n).support) :
    ParetoArchiveValid WeaklyDominates Population.val := by
  rcases (PMF.mem_support_map_iff _ _ _).mp Possible with ⟨x, _PossibleInitial, Equality⟩
  rw [← Equality]
  exact ParetoArchiveSingletonValid WeaklyDominates x

theorem SEMOStepValid {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Population Next : ParetoPopulation (Bits n))
    (Valid : ParetoArchiveValid WeaklyDominates Population.val)
    (Possible : Next ∈ (SEMOStep PositiveLength WeaklyDominates Population).support) :
    ParetoArchiveValid WeaklyDominates Next.val := by
  rcases (SEMOStepSupport PositiveLength WeaklyDominates Population Next).mp Possible with
    ⟨_Parent, _ParentMembership, Candidate, _MutationPossible, Equality⟩
  rw [← Equality]
  exact ParetoArchiveUpdateValid WeaklyDominates Population.val Candidate Valid

/-- Archive distribution after a fixed number of iterations, using the supplied initial PMF or uniform singleton initialization. -/
def SEMORun {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Steps : Nat) (Initial : PMF (ParetoPopulation (Bits n)) := SEMOInit n) :
    PMF (ParetoPopulation (Bits n)) :=
  Probability.Evolve (SEMOStep PositiveLength WeaklyDominates) Initial Steps

/-- Every reachable archive remains nondominated at every finite iteration. -/
theorem SEMORunValid {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Steps : Nat) (Initial : PMF (ParetoPopulation (Bits n)))
    (InitialValid : ∀ P ∈ Initial.support, ParetoArchiveValid WeaklyDominates P.val)
    (Population : ParetoPopulation (Bits n))
    (Possible : Population ∈ (SEMORun PositiveLength WeaklyDominates Steps Initial).support) :
    ParetoArchiveValid WeaklyDominates Population.val := by
  induction Steps generalizing Population with
  | zero => exact InitialValid Population Possible
  | succ Steps Previous =>
      obtain ⟨ParentPopulation, ParentPossible, StepPossible⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp Possible
      exact SEMOStepValid PositiveLength WeaklyDominates ParentPopulation Population
        (Previous ParentPopulation ParentPossible) StepPossible

/-- Finite-step SEMO law with the supplied archive goal frozen upon first success, including initialization. -/
def SEMORunUntil {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Goal : ParetoPopulation (Bits n) → Prop) [DecidablePred Goal]
    (Steps : Nat) (Initial : PMF (ParetoPopulation (Bits n)) := SEMOInit n) :
    PMF (ParetoPopulation (Bits n)) :=
  Probability.Evolve (Probability.StopAt (SEMOStep PositiveLength WeaklyDominates) Goal)
    Initial Steps

end
end ECTheoryLib
