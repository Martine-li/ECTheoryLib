import ECTheoryLib.Operators.Mutation.IndependentBit
import ECTheoryLib.Algorithms.SEMO

/-!
# Global simple evolutionary multiobjective optimizer

GSEMO differs from SEMO by independently flipping every bit with probability
`1 / n`. Uniform parent selection and archive update are otherwise the same.
The standard singleton uniform initialization can be overridden by an explicit
initial PMF (for example an all-zero singleton in a problem-specific application).
-/

namespace ECTheoryLib

noncomputable section

/-- Uniform singleton-archive initialization, shared with SEMO. -/
def GSEMOInit (n : Nat) : PMF (ParetoPopulation (Bits n)) := SEMOInit n

/-- One GSEMO iteration: uniform archive parent, independent bit mutation at rate 1/n, then the supplied Pareto archive update. -/
def GSEMOStep {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Population : ParetoPopulation (Bits n)) : PMF (ParetoPopulation (Bits n)) :=
  (UniformParetoParent Population).bind (fun Parent =>
    (StandardBitMutation PositiveLength Parent).map
      (ParetoPopulationUpdate WeaklyDominates Population))

theorem GSEMOStepSupport {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Population Next : ParetoPopulation (Bits n)) :
    Next ∈ (GSEMOStep PositiveLength WeaklyDominates Population).support ↔
      ∃ Parent ∈ Population.val,
        ∃ Candidate ∈ (StandardBitMutation PositiveLength Parent).support,
          ParetoPopulationUpdate WeaklyDominates Population Candidate = Next := by
  unfold GSEMOStep
  rw [PMF.mem_support_bind_iff]
  simp only [UniformParetoParentSupport, PMF.mem_support_map_iff]

theorem GSEMOInitValid {n : Nat} (WeaklyDominates : Bits n → Bits n → Prop)
    (Population : ParetoPopulation (Bits n)) (Possible : Population ∈ (GSEMOInit n).support) :
    ParetoArchiveValid WeaklyDominates Population.val := by
  exact SEMOInitValid WeaklyDominates Population Possible

theorem GSEMOStepValid {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Population Next : ParetoPopulation (Bits n))
    (Valid : ParetoArchiveValid WeaklyDominates Population.val)
    (Possible : Next ∈ (GSEMOStep PositiveLength WeaklyDominates Population).support) :
    ParetoArchiveValid WeaklyDominates Next.val := by
  rcases (GSEMOStepSupport PositiveLength WeaklyDominates Population Next).mp Possible with
    ⟨_Parent, _ParentMembership, Candidate, _MutationPossible, Equality⟩
  rw [← Equality]
  exact ParetoArchiveUpdateValid WeaklyDominates Population.val Candidate Valid

/-- The archive distribution after the specified number of iterations, starting from the supplied PMF or the standard singleton law. -/
def GSEMORun {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Steps : Nat) (Initial : PMF (ParetoPopulation (Bits n)) := GSEMOInit n) :
    PMF (ParetoPopulation (Bits n)) :=
  Probability.Evolve (GSEMOStep PositiveLength WeaklyDominates) Initial Steps

theorem GSEMORunValid {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Steps : Nat) (Initial : PMF (ParetoPopulation (Bits n)))
    (InitialValid : ∀ P ∈ Initial.support, ParetoArchiveValid WeaklyDominates P.val)
    (Population : ParetoPopulation (Bits n))
    (Possible : Population ∈ (GSEMORun PositiveLength WeaklyDominates Steps Initial).support) :
    ParetoArchiveValid WeaklyDominates Population.val := by
  induction Steps generalizing Population with
  | zero => exact InitialValid Population Possible
  | succ Steps Previous =>
      obtain ⟨ParentPopulation, ParentPossible, StepPossible⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp Possible
      exact GSEMOStepValid PositiveLength WeaklyDominates ParentPopulation Population
        (Previous ParentPopulation ParentPossible) StepPossible

/-- The finite-step archive law with the supplied goal frozen as soon as it holds, including at initialization. -/
def GSEMORunUntil {n : Nat} (PositiveLength : 0 < n)
    (WeaklyDominates : Bits n → Bits n → Prop) [DecidableRel WeaklyDominates]
    (Goal : ParetoPopulation (Bits n) → Prop) [DecidablePred Goal]
    (Steps : Nat) (Initial : PMF (ParetoPopulation (Bits n)) := GSEMOInit n) :
    PMF (ParetoPopulation (Bits n)) :=
  Probability.Evolve (Probability.StopAt (GSEMOStep PositiveLength WeaklyDominates) Goal)
    Initial Steps

end
end ECTheoryLib
