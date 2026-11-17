import Mathlib.Order.Defs.PartialOrder

/-!
# Greatest objective values

A maximizer has objective value at least that of every feasible point. For a
partially ordered objective this is stronger than Pareto maximality, which only
excludes strict domination. No algorithm or stopping condition is specified here.
-/

namespace ECTheoryLib.Problems

/-- A feasible point whose objective value is at least that of every feasible point. -/
def IsMaximizer {α β : Type*} [Preorder β] (f : α → β) (x : α) : Prop :=
  
  
  
  
  ∀ y, f y ≤ f x

end ECTheoryLib.Problems
