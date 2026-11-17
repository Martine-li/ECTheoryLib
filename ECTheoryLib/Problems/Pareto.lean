import ECTheoryLib.Problems.Comparison
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Pareto optimality for objectives that are all maximized

An optimal point has no strictly dominating feasible point. Equal objective vectors
are allowed at different search points. This differs from `IsMaximizer`.
-/

namespace ECTheoryLib.Problems

/-- Package two maximization objectives in the same format as the comparison API. -/
def BiObjective (First Second : Nat) (i : Fin 2) : Nat :=
  if i = 0 then First else Second

/-- Strict dominance: weak dominance holds, but the reverse comparison fails. -/
def ParetoMaxStrictlyDominates {α β : Type*} {m : Nat} [Preorder β]
    (Fitness : α → Fin m → β) (Candidate Parent : α) : Prop :=
  ParetoMaxNotWorse Fitness Candidate Parent ∧
    ¬ ParetoMaxNotWorse Fitness Parent Candidate

/-- No feasible point strictly dominates this search point. -/
def IsParetoMaximal {α β : Type*} {m : Nat} [Preorder β]
    (Fitness : α → Fin m → β) (x : α) : Prop :=
  ∀ y, ParetoMaxNotWorse Fitness y x → ParetoMaxNotWorse Fitness x y

theorem IsParetoMaximalIffNoStrictDominator {α β : Type*} {m : Nat} [Preorder β]
    (Fitness : α → Fin m → β) (x : α) :
    IsParetoMaximal Fitness x ↔ ∀ y, ¬ ParetoMaxStrictlyDominates Fitness y x := by
  constructor
  · intro Maximal y StrictDominance
    exact StrictDominance.2 (Maximal y StrictDominance.1)
  · intro NoDominator y WeakDominance
    by_contra NoReverse
    exact NoDominator y ⟨WeakDominance, NoReverse⟩

theorem BiObjectiveLeIff (a b c d : Nat) :
    (∀ i, BiObjective a b i ≤ BiObjective c d i) ↔ a ≤ c ∧ b ≤ d := by
  constructor
  · intro CoordinateBounds
    constructor
    · exact CoordinateBounds 0
    · exact CoordinateBounds 1
  · intro Bounds i
    fin_cases i
    · exact Bounds.1
    · exact Bounds.2

end ECTheoryLib.Problems
