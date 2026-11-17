import ECTheoryLib.Operators.Mutation.BitFlip
import Mathlib.Data.Fin.Tuple.Basic

/-!
# One-bit mutation under head/tail decomposition

Flipping the head changes only the head; flipping a successor coordinate acts
on the corresponding tail coordinate. These identities are independent of
the objective, selection rule, and probability law.
-/

namespace ECTheoryLib

theorem OnebitMutationConsZero {n : ℕ} (b : Bool) (x : Bits n) :
    OnebitMutation (Fin.cons b x) 0 = Fin.cons (!b) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [OnebitMutationAt, Fin.cons_zero, Fin.cons_zero]
  · rw [OnebitMutationAway _ _ _ (Fin.succ_ne_zero j), Fin.cons_succ, Fin.cons_succ]

theorem OnebitMutationConsSucc {n : ℕ} (b : Bool) (x : Bits n) (j : Fin n) :
    OnebitMutation (Fin.cons b x) j.succ = Fin.cons b (OnebitMutation x j) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [OnebitMutationAway _ _ _ (Fin.succ_ne_zero j).symm, Fin.cons_zero, Fin.cons_zero]
  · simp only [OnebitMutation, Fin.succ_inj, Fin.cons_succ]

end ECTheoryLib

