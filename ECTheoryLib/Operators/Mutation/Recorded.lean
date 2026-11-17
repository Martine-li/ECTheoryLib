import ECTheoryLib.Operators.Mutation.IndependentBitCoupling

/-!
# Independent bit mutation with retained proposal records

A policy samples a parent from memory, independent bit mutation samples its
raw candidate, and a deterministic update changes memory while retaining the
sampled parent/candidate pair. The record therefore includes rejected proposals.
PMF projection laws expose the exact record and memory distributions; they do
not identify joint paths with a separately defined algorithm. Any required
history belongs in memory. The initial dummy record is not a mutation call.
-/

namespace ECTheoryLib

open scoped unitInterval

noncomputable section

/-- Memory together with the last sampled parent and its raw candidate. -/
abbrev RecordedMutationState (S : Type*) (n : ℕ) := S × (Bits n × Bits n)

/-- The unrecorded memory transition samples a parent, mutates it, then updates
the memory. If the update performs selection, this is its selected-state law. -/
def MutationMemoryStep {S : Type*} {n : ℕ} (p : I)
    (Parents : S → PMF (Bits n)) (Update : S → Bits n → Bits n → S)
    (s : S) : PMF S :=
  (Parents s).bind (fun Parent =>
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).map
      (fun Candidate => Update s Parent Candidate))

/-- The actual recorded transition; the old record need not be consulted because
any required history belongs in S. The new record precedes no selection filter. -/
def RecordedMutationStep {S : Type*} {n : ℕ} (p : I)
    (Parents : S → PMF (Bits n)) (Update : S → Bits n → Bits n → S)
    (z : RecordedMutationState S n) : PMF (RecordedMutationState S n) :=
  (Parents z.1).bind (fun Parent =>
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).map
      (fun Candidate => (Update z.1 Parent Candidate, (Parent, Candidate))))

/-- Initialization attaches only a dummy record, not a sampled mutation call.
Any later path event must start at coordinate 1 rather than count this record. -/
def RecordedMutationInitial {S : Type*} {n : ℕ}
    (Initial : PMF S) (Dummy : Bits n × Bits n) : PMF (RecordedMutationState S n) :=
  Initial.map (fun s => (s, Dummy))

/-- The recorded parent/candidate marginal is exactly parent sampling followed
by actual mutation, independently of what the memory update accepts or rejects. -/
theorem RecordedMutationStepRecord {S : Type*} {n : ℕ} (p : I)
    (Parents : S → PMF (Bits n)) (Update : S → Bits n → Bits n → S)
    (z : RecordedMutationState S n) :
    (RecordedMutationStep p Parents Update z).map Prod.snd =
      (Parents z.1).bind (fun Parent =>
        (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).map
          (fun Candidate => (Parent, Candidate))) := by
  simp only [RecordedMutationStep, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Forgetting the record recovers the exact memory transition at this step.
This equality alone is not an equality of joint projected path measures. -/
theorem RecordedMutationStepForget {S : Type*} {n : ℕ} (p : I)
    (Parents : S → PMF (Bits n)) (Update : S → Bits n → Bits n → S)
    (z : RecordedMutationState S n) :
    (RecordedMutationStep p Parents Update z).map Prod.fst =
      MutationMemoryStep p Parents Update z.1 := by
  simp only [RecordedMutationStep, MutationMemoryStep, PMF.map_bind,
    PMF.map_comp, Function.comp_def]

/-- The initialization also has the exact unrecorded initial law. -/
theorem RecordedMutationInitialForget {S : Type*} {n : ℕ}
    (Initial : PMF S) (Dummy : Bits n × Bits n) :
    (RecordedMutationInitial Initial Dummy).map Prod.fst = Initial := by
  unfold RecordedMutationInitial
  rw [PMF.map_comp]
  exact PMF.map_id Initial

/-- For the same memory and parent policy, changing the acceptance/update rule
cannot change the recorded raw-proposal law. -/
theorem RecordedMutationRecordIndependentOfUpdate {S : Type*} {n : ℕ} (p : I)
    (Parents : S → PMF (Bits n)) (Update Update' : S → Bits n → Bits n → S)
    (z : RecordedMutationState S n) :
    (RecordedMutationStep p Parents Update z).map Prod.snd =
      (RecordedMutationStep p Parents Update' z).map Prod.snd := by
  rw [RecordedMutationStepRecord, RecordedMutationStepRecord]

end
end ECTheoryLib
