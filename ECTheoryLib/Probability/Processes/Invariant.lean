import ECTheoryLib.Probability.Processes.Transition

/-!
# Propagation of state invariants through finite-step laws

Initialization and preservation are required only on PMF supports. The result
applies to archive validity, population size, and other reachable-state properties.
It is independent of algorithms and objectives; each composition is normalized
by the PMF construction.
-/

namespace ECTheoryLib.Probability

/-- A property holding on the initial support and preserved by every supported one-step transition holds on the support of every finite-step law. -/
theorem EvolvePreservesProperty {State : Type*} (Step : Transition State)
    (Property : State → Prop) (Initial : PMF State)
    (Initially : ∀ x ∈ Initial.support, Property x)
    (Preserved : ∀ x, Property x → ∀ y ∈ (Step x).support, Property y)
    (Time : Nat) (x : State) (Possible : x ∈ (Evolve Step Initial Time).support) :
    Property x := by
  induction Time generalizing x with
  | zero => exact Initially x Possible
  | succ Time Previous =>
      obtain ⟨Parent, ParentPossible, ChildPossible⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp Possible
      have ParentProperty : Property Parent := Previous Parent ParentPossible
      exact Preserved Parent ParentProperty x ChildPossible

end ECTheoryLib.Probability
