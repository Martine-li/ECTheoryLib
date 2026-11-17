import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Finite PMF expectation rules

These bridges expose the expectation of a composed transition as finite sums.
All real functions on the finite state spaces are integrable. A support property
is also lifted to an almost-sure property, as required by path-level interfaces.
The lower-bound rule counts distinct elementary outcomes and discards only
nonnegative contributions.
-/
namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section

/-- A property holding on every supported state holds almost surely. -/
theorem PMFAEOfSupport {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (P : α → Prop)
    (OnSupport : ∀ x ∈ p.support, P x) : ∀ᵐ x ∂p.toMeasure, P x := by
  rw [ae_iff]
  apply (p.toMeasure_apply_eq_zero_iff (Set.to_countable _).measurableSet).mpr
  exact Set.disjoint_left.mpr (fun x InSupport NotProperty => NotProperty (OnSupport x InSupport))

/-- Total expectation for a finite PMF bind, including signed real integrands. -/
theorem PMFIntegralBind {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    (∫ y, f y ∂(p.bind q).toMeasure) =
      ∑ x, (p x).toReal * (∫ y, f y ∂(q x).toMeasure) := by
  simp only [PMF.integral_eq_sum, smul_eq_mul, PMF.bind_apply, tsum_fintype]
  have FiniteTerms (y : β) : ∀ x ∈ (Finset.univ : Finset α), p x * q x y ≠ ⊤ := by
    intro x _InUniv
    exact ENNReal.mul_ne_top (p.apply_ne_top x) ((q x).apply_ne_top y)
  simp_rw [ENNReal.toReal_sum (FiniteTerms _), ENNReal.toReal_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _InUniv
  apply Finset.sum_congr rfl
  intro y _InUniv
  ring

/-- A deterministic update transforms the integrand rather than the PMF weights. -/
theorem PMFIntegralMap {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (Update : α → β) (f : β → ℝ) :
    (∫ y, f y ∂(p.map Update).toMeasure) = ∫ x, f (Update x) ∂p.toMeasure := by
  rw [← PMF.toMeasure_map Update p (measurable_of_finite _)]
  exact integral_map_of_stronglyMeasurable (measurable_of_finite Update)
    (measurable_of_finite f).stronglyMeasurable

/-- Count pairwise distinct elementary outcomes with a common probability floor.
All omitted outcomes must have nonnegative contribution. -/
theorem PMFIntegralLowerOfInjection {α ι : Type*} [Fintype α] [Fintype ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (f : α → ℝ) (Outcome : ι → α) (Injective : Function.Injective Outcome)
    (Nonnegative : ∀ x, 0 ≤ f x) (Delta : ℝ)
    (ProbabilityLower : ∀ i, Delta ≤ (p (Outcome i)).toReal) :
    Delta * (∑ i, f (Outcome i)) ≤ ∫ x, f x ∂p.toMeasure := by
  classical
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  calc
    Delta * (∑ i, f (Outcome i)) ≤ ∑ i, (p (Outcome i)).toReal * f (Outcome i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (ProbabilityLower i) (Nonnegative (Outcome i)))
    _ = ∑ x ∈ Finset.univ.image Outcome, (p x).toReal * f x := by
      rw [Finset.sum_image (fun i _ j _ Equal => Injective Equal)]
    _ ≤ ∑ x, (p x).toReal * f x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro x _InUniv _Outside
      exact mul_nonneg ENNReal.toReal_nonneg (Nonnegative x)

end
end ECTheoryLib.Probability
