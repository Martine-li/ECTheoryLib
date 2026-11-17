import ECTheoryLib.Probability.StochasticOrder.ExtendedNatSum
import ECTheoryLib.Probability.HittingTimes.GeometricHazard

/-!
# Conditional geometric bounds for finitely many stages

At every positive-probability complete stage history, a success floor is assumed
on each nonnull survival event of the current stage. Stages may be dependent,
skipped (zero), or initially represented by infinite values. The reference law
is an explicit finite product of Mathlib geometric laws, shifted to count trials.

This is the composition step used in Doerr Theorem 1.8.6. Deriving the conditional
stage hazards from arbitrary search histories and fitness-level entry times is
a separate obligation; this module does not assert that bridge.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

open scoped unitInterval

/-- Conditional success floors on full stage histories give an independent geometric sum bound. -/
theorem GeometricStageSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → WithTop ℕ) (MeasurableX : ∀ i, Measurable (X i))
    (n : ℕ) (p : Fin n → I) (Positive : ∀ i, 0 < (p i : ℝ))
    (Hazard : ∀ (t : Fin n) (h : Fin t → WithTop ℕ),
      P (ExtendedNatPrefix X t ⁻¹' {h}) ≠ 0 →
      ∀ s : ℕ, (P[|ExtendedNatPrefix X t ⁻¹' {h}]) {ω | (s : WithTop ℕ) < X t ω} ≠ 0 →
        (p t : ℝ) ≤ ((P[|ExtendedNatPrefix X t ⁻¹' {h}])[|{ω | (s : WithTop ℕ) < X t ω}]).real
          {ω | X t ω ≤ ((s+1 : ℕ) : WithTop ℕ)}) :
    StochasticDominated (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω))
      ((Measure.pi (fun i : Fin n => geometricMeasure (p i))).map
        (fun z : Fin n → ℕ => ∑ i, ((z i+1 : ℕ) : WithTop ℕ))) := by
  let Q := Measure.pi (fun i : Fin n => geometricMeasure (p i))
  let Y : ℕ → (Fin n → ℕ) → WithTop ℕ :=
    fun i z => if Before : i < n then ((z ⟨i, Before⟩+1 : ℕ) : WithTop ℕ) else 0
  have At (i : Fin n) (z : Fin n → ℕ) : Y i z = ((z i+1 : ℕ) : WithTop ℕ) := by
    exact dif_pos i.isLt
  have MeasurableY (i : ℕ) : Measurable (Y i) := measurable_of_countable _
  have IndependentY : iIndepFun (fun i : Fin n => Y i) Q := by
    have Independent := iIndepFun_pi (μ := fun i : Fin n => geometricMeasure (p i)) (fun _i : Fin n =>
      (measurable_of_countable (fun j : ℕ => ((j+1 : ℕ) : WithTop ℕ))).aemeasurable)
    simpa only [Y, dif_pos (Fin.isLt _)] using Independent
  have ReferenceLaw (i : Fin n) : Q.map (Y i) =
      (geometricMeasure (p i)).map (fun j : ℕ => ((j+1 : ℕ) : WithTop ℕ)) := by
    have Coordinate := (measurePreserving_eval (fun j : Fin n => geometricMeasure (p j)) i).map_eq
    rw [← Coordinate, Measure.map_map (measurable_of_countable
      (fun j : ℕ => ((j+1 : ℕ) : WithTop ℕ))) (measurable_of_countable (Function.eval i))]
    congr 1
    funext z
    exact At i z
  have Bound := ExtendedNatSequentialSum P Q X Y MeasurableX MeasurableY n IndependentY (by
    intro t Before h PositiveHistory
    have ConditionalProbability : IsProbabilityMeasure P[|ExtendedNatPrefix X t ⁻¹' {h}] :=
      cond_isProbabilityMeasure PositiveHistory
    rw [ReferenceLaw ⟨t, Before⟩]
    exact WaitingGeometricDomination _ (X t) (MeasurableX t) (p ⟨t, Before⟩)
      (Positive ⟨t, Before⟩) (Hazard ⟨t, Before⟩ h PositiveHistory))
  have ReferenceSum (z : Fin n → ℕ) :
      (∑ i ∈ Finset.range n, Y i z) = ∑ i : Fin n, ((z i+1 : ℕ) : WithTop ℕ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => At i z)
  simpa only [ReferenceSum] using Bound

/-- Finitely many positive success floors imply almost-sure finiteness of the total stage time. -/
theorem GeometricStageSumFiniteAlmostSurely {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → WithTop ℕ) (MeasurableX : ∀ i, Measurable (X i))
    (n : ℕ) (p : Fin n → I) (Positive : ∀ i, 0 < (p i : ℝ))
    (Hazard : ∀ (t : Fin n) (h : Fin t → WithTop ℕ),
      P (ExtendedNatPrefix X t ⁻¹' {h}) ≠ 0 →
      ∀ s : ℕ, (P[|ExtendedNatPrefix X t ⁻¹' {h}]) {ω | (s : WithTop ℕ) < X t ω} ≠ 0 →
        (p t : ℝ) ≤ ((P[|ExtendedNatPrefix X t ⁻¹' {h}])[|{ω | (s : WithTop ℕ) < X t ω}]).real
          {ω | X t ω ≤ ((s+1 : ℕ) : WithTop ℕ)}) :
    ∀ᵐ ω ∂P, (∑ i ∈ Finset.range n, X i ω) ≠ ⊤ := by
  have Bound := GeometricStageSum P X MeasurableX n p Positive Hazard
  have MeasurableSum : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
    Finset.measurable_sum _ (fun i _ => MeasurableX i)
  let Q := Measure.pi (fun i : Fin n => geometricMeasure (p i))
  let Y := fun z : Fin n → ℕ => ∑ i, ((z i+1 : ℕ) : WithTop ℕ)
  have ActualProbability : IsProbabilityMeasure (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω)) :=
    Measure.isProbabilityMeasure_map MeasurableSum.aemeasurable
  have ReferenceProbability : IsProbabilityMeasure (Q.map Y) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable Y).aemeasurable
  have FiniteReference : ∀ᵐ t ∂Q.map Y, t ≠ ⊤ := by
    apply (ae_map_iff (measurable_of_countable Y).aemeasurable (measurableSet_singleton ⊤).compl).mpr
    apply ae_of_all
    intro z
    exact WithTop.sum_ne_top.mpr (fun i _ => WithTop.coe_ne_top)
  have FiniteSum := ExtendedNatFiniteOfDomination _ _ Bound FiniteReference
  exact ae_of_ae_map MeasurableSum.aemeasurable FiniteSum

end
end ECTheoryLib.Probability
