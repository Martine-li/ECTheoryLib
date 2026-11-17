import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# A supported distribution as a subtype distribution

A property holding on every positive-mass outcome can be attached to the sampled
state without conditioning or renormalizing its probabilities. Forgetting that
proof recovers the original PMF exactly. This supplies finite representation
bridges while keeping the original transition law visible.
-/
namespace ECTheoryLib.Probability
noncomputable section

/-- Attach a proved support property to a sample. No mass is discarded. -/
def SupportedSubtype {α : Type*} (p : PMF α) (P : α → Prop)
    (Supported : ∀ x ∈ p.support, P x) : PMF {x // P x} :=
  p.bindOnSupport (fun x hx => PMF.pure ⟨x, Supported x hx⟩)

/-- Forgetting the support proof recovers the original distribution, including
all multiplicities already represented by the sampled values. -/
theorem SupportedSubtypeForget {α : Type*} (p : PMF α) (P : α → Prop)
    (Supported : ∀ x ∈ p.support, P x) :
    (SupportedSubtype p P Supported).map Subtype.val = p := by
  unfold SupportedSubtype PMF.map
  rw [← PMF.bindOnSupport_eq_bind, PMF.bindOnSupport_bindOnSupport]
  simp only [PMF.pure_bindOnSupport, Function.comp_apply, PMF.bindOnSupport_pure]

end
end ECTheoryLib.Probability
