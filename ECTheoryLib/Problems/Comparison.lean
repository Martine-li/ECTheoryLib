import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Fintype.Defs

/-!
# Candidate-to-parent comparison relations

Every relation takes the candidate first and the parent second. Pareto comparisons
allow equal objective vectors; incomparable vectors satisfy neither direction.
All objectives share a direction here; mixed directions need a separate relation.
-/

namespace ECTheoryLib.Problems

/-- Single-objective maximization, accepting ties in objective value. -/
abbrev MaxNotWorse {α β : Type*} [Preorder β]
    (Fitness : α → β) (Candidate Parent : α) : Prop :=
  Fitness Parent ≤ Fitness Candidate

/-- Single-objective minimization, accepting ties in objective value. -/
abbrev MinNotWorse {α β : Type*} [Preorder β]
    (Fitness : α → β) (Candidate Parent : α) : Prop :=
  Fitness Candidate ≤ Fitness Parent

/-- Weak Pareto dominance when all objectives are maximized. -/
abbrev ParetoMaxNotWorse {α β : Type*} {m : Nat} [Preorder β]
    (Fitness : α → Fin m → β) (Candidate Parent : α) : Prop :=
  ∀ i, Fitness Parent i ≤ Fitness Candidate i

/-- Weak Pareto dominance when all objectives are minimized. -/
abbrev ParetoMinNotWorse {α β : Type*} {m : Nat} [Preorder β]
    (Fitness : α → Fin m → β) (Candidate Parent : α) : Prop :=
  ∀ i, Fitness Candidate i ≤ Fitness Parent i

end ECTheoryLib.Problems
