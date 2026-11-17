import ECTheoryLib.Operators.Mutation.IndependentBit
import ECTheoryLib.Operators.Selection.Hypervolume
import ECTheoryLib.Probability.Processes.Transition

/-!
# SMS-EMOA without crossover

The Algorithm 1 variant of Zheng and Doerr, arXiv:2312.10290v4:
initialize independent uniformly random individuals, select a uniformly random
parent occurrence, apply standard bit mutation, and delete a uniformly random
minimum hypervolume contributor in the last front of the augmented population.
Lists preserve duplicates. Rational objective values and reference coordinates
permit exact finite hypervolume arithmetic. No runtime bound is asserted.
-/

namespace ECTheoryLib

open Operators.Selection

/-- Nonempty list populations; the step preserves their particular length. -/
abbrev SMSEMOAState (n : Nat) := {Population : List (Bits n) // 0 < Population.length}

/-- Appending one offspring and removing one occurrence gives a nonempty population. -/
def SMSEMOAInsertRemove {n : Nat} (Population : SMSEMOAState n) (Candidate : Bits n)
    (j : Fin (Population.val ++ [Candidate]).length) : SMSEMOAState n := by
  refine ⟨(Population.val ++ [Candidate]).eraseIdx j.val, ?_⟩
  have RemovedOne : ((Population.val ++ [Candidate]).eraseIdx j.val).length + 1 =
      (Population.val ++ [Candidate]).length := List.length_eraseIdx_add_one j.isLt
  simp only [List.length_append, List.length_singleton] at RemovedOne
  have PopulationPositive := Population.property
  omega

theorem SMSEMOAInsertRemoveLength {n : Nat} (Population : SMSEMOAState n)
    (Candidate : Bits n) (j : Fin (Population.val ++ [Candidate]).length) :
    (SMSEMOAInsertRemove Population Candidate j).val.length = Population.val.length := by
  have RemovedOne := List.length_eraseIdx_add_one j.isLt
  simp only [List.length_append, List.length_singleton] at RemovedOne
  change ((Population.val ++ [Candidate]).eraseIdx j.val).length = Population.val.length
  omega

noncomputable section

/-- Independent uniform initialization of a population of the requested positive size. -/
def SMSEMOAInit (n Capacity : Nat) (PositiveCapacity : 0 < Capacity) : PMF (SMSEMOAState n) :=
  (IndependentSamples (PMF.uniformOfFintype (Bits n)) Capacity).bindOnSupport
    (fun Population Possible => PMF.pure ⟨Population, by
      rw [IndependentSamplesLength _ Capacity Population Possible]
      exact PositiveCapacity⟩)

theorem SMSEMOAInitLength (n Capacity : Nat) (PositiveCapacity : 0 < Capacity)
    (Population : SMSEMOAState n)
    (Possible : Population ∈ (SMSEMOAInit n Capacity PositiveCapacity).support) :
    Population.val.length = Capacity := by
  obtain ⟨Samples, SamplesPossible, PopulationPossible⟩ :=
    (PMF.mem_support_bindOnSupport_iff _ _).mp Possible
  have Equality := (PMF.mem_support_pure_iff _ _).mp PopulationPossible
  rw [Equality]
  exact IndependentSamplesLength _ Capacity Samples SamplesPossible

/-- Uniform choice among parent occurrences, including multiple copies of one genotype. -/
def SMSEMOAParentIndex {n : Nat} (Population : SMSEMOAState n) :
    PMF (Fin Population.val.length) := by
  letI : Nonempty (Fin Population.val.length) := ⟨⟨0, Population.property⟩⟩
  exact PMF.uniformOfFintype (Fin Population.val.length)

theorem SMSEMOAParentIndexProbability {n : Nat} (Population : SMSEMOAState n)
    (j : Fin Population.val.length) :
    SMSEMOAParentIndex Population j = (Population.val.length : ENNReal)⁻¹ := by
  let : Nonempty (Fin Population.val.length) := ⟨j⟩
  unfold SMSEMOAParentIndex
  rw [PMF.uniformOfFintype_apply, Fintype.card_fin]

/-- SMS environmental selection on the parents and the single offspring. -/
def SMSEMOASurvival {n m : Nat} (Fitness : Bits n → Fin m → ℚ)
    (Reference : Fin m → ℚ) (Population : SMSEMOAState n) (Candidate : Bits n) :
    PMF (SMSEMOAState n) :=
  let Pool := Population.val ++ [Candidate]
  have PoolNonempty : 0 < Pool.length := by
    rw [List.length_append, List.length_singleton]
    omega
  (SMSRemovalIndex Fitness Reference Pool PoolNonempty).map
    (SMSEMOAInsertRemove Population Candidate)

theorem SMSEMOASurvivalLength {n m : Nat} (Fitness : Bits n → Fin m → ℚ)
    (Reference : Fin m → ℚ) (Population Next : SMSEMOAState n) (Candidate : Bits n)
    (Possible : Next ∈ (SMSEMOASurvival Fitness Reference Population Candidate).support) :
    Next.val.length = Population.val.length := by
  obtain ⟨j, _RemovalPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← Equality]
  exact SMSEMOAInsertRemoveLength Population Candidate j

/-- Every removal is a minimum hypervolume contributor of the last front. -/
theorem SMSEMOASurvivalSupport {n m : Nat} (Fitness : Bits n → Fin m → ℚ)
    (Reference : Fin m → ℚ) (Population Next : SMSEMOAState n) (Candidate : Bits n) :
    Next ∈ (SMSEMOASurvival Fitness Reference Population Candidate).support ↔
      ∃ j ∈ SMSRemovalCandidates Fitness Reference (Population.val ++ [Candidate]),
        SMSEMOAInsertRemove Population Candidate j = Next := by
  unfold SMSEMOASurvival
  rw [PMF.mem_support_map_iff]
  simp only [SMSRemovalIndexSupport]

/-- One uniformly selected parent, one independent bit mutation, one hypervolume deletion. -/
def SMSEMOAStep {n m : Nat} (PositiveLength : 0 < n)
    (Fitness : Bits n → Fin m → ℚ) (Reference : Fin m → ℚ)
    (Population : SMSEMOAState n) : PMF (SMSEMOAState n) :=
  (SMSEMOAParentIndex Population).bind (fun j =>
    (StandardBitMutation PositiveLength Population.val[j]).bind
      (SMSEMOASurvival Fitness Reference Population))

theorem SMSEMOAStepLength {n m : Nat} (PositiveLength : 0 < n)
    (Fitness : Bits n → Fin m → ℚ) (Reference : Fin m → ℚ)
    (Population Next : SMSEMOAState n)
    (Possible : Next ∈ (SMSEMOAStep PositiveLength Fitness Reference Population).support) :
    Next.val.length = Population.val.length := by
  obtain ⟨_ParentIndex, _ParentPossible, MutationPossible⟩ :=
    (PMF.mem_support_bind_iff _ _ _).mp Possible
  obtain ⟨Candidate, _CandidatePossible, SurvivalPossible⟩ :=
    (PMF.mem_support_bind_iff _ _ _).mp MutationPossible
  exact SMSEMOASurvivalLength Fitness Reference Population Next Candidate SurvivalPossible

/-- Iterate the SMS-EMOA population kernel from the supplied initial law. Each step is one offspring-generation and environmental-selection iteration. -/
def SMSEMOARun {n m : Nat} (PositiveLength : 0 < n)
    (Fitness : Bits n → Fin m → ℚ) (Reference : Fin m → ℚ)
    (Steps : Nat) (Initial : PMF (SMSEMOAState n)) : PMF (SMSEMOAState n) :=
  Probability.Evolve (SMSEMOAStep PositiveLength Fitness Reference) Initial Steps

/-- A fixed initial size is preserved through every finite number of iterations. -/
theorem SMSEMOARunLength {n m : Nat} (PositiveLength : 0 < n)
    (Fitness : Bits n → Fin m → ℚ) (Reference : Fin m → ℚ)
    (Steps Capacity : Nat) (Initial : PMF (SMSEMOAState n))
    (InitialLength : ∀ P ∈ Initial.support, P.val.length = Capacity)
    (Population : SMSEMOAState n)
    (Possible : Population ∈ (SMSEMOARun PositiveLength Fitness Reference Steps Initial).support) :
    Population.val.length = Capacity := by
  induction Steps generalizing Population with
  | zero => exact InitialLength Population Possible
  | succ Steps Previous =>
      obtain ⟨ParentPopulation, ParentPossible, StepPossible⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp Possible
      rw [SMSEMOAStepLength PositiveLength Fitness Reference ParentPopulation Population StepPossible]
      exact Previous ParentPopulation ParentPossible

end
end ECTheoryLib
