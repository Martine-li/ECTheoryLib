import Mathlib.Init

/-!
Deterministic single-survivor selection with a caller-supplied candidate-to-parent comparison. The relation determines tie acceptance and need not be total; acceptance and rejection equations expose both branches.
-/

namespace ECTheoryLib

/-- Keep the candidate when `NotWorse Candidate Parent` holds, otherwise keep
the parent. The relation receives candidate then parent, whereas the state
arguments here are parent then candidate. The relation need not be total;
weak Pareto comparison rejects incomparable candidates. Tie handling is supplied
by the relation. -/
def ElitistSelect {α : Type*}
    (NotWorse : α → α → Prop) [DecidableRel NotWorse]
    (Parent Candidate : α) : α :=
  if NotWorse Candidate Parent then
    Candidate
  else
    Parent

/-- A candidate satisfying the supplied acceptance relation is selected. -/
theorem ElitistSelectAccept {α : Type*}
    (NotWorse : α → α → Prop) [DecidableRel NotWorse]
    (Parent Candidate : α) (Acceptable : NotWorse Candidate Parent) :
    ElitistSelect NotWorse Parent Candidate = Candidate := by
  unfold ElitistSelect
  rw [if_pos Acceptable]

/-- If the acceptance relation fails, the parent is retained. -/
theorem ElitistSelectReject {α : Type*}
    (NotWorse : α → α → Prop) [DecidableRel NotWorse]
    (Parent Candidate : α) (Unacceptable : ¬ NotWorse Candidate Parent) :
    ElitistSelect NotWorse Parent Candidate = Parent := by
  unfold ElitistSelect
  rw [if_neg Unacceptable]

end ECTheoryLib
