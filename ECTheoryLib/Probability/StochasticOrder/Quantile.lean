import Mathlib.Probability.CDF
import Mathlib.Probability.HasLaw
import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Real quantiles and their full distribution law

Infrastructure for Doerr's Theorem 1.8.10 (p. 31), in *Theory of Evolutionary
Computation*. Mathlib supplies the CDF, its limits and right continuity, order
completeness, Lebesgue measure and HasLaw. Quantile levels lie strictly between
zero and one, avoiding extended-real endpoint values. Probability laws may have
atoms, unbounded support or infinite expectation.

The CDF-based order properties use Mathlib's total CDF definition. The theorem
identifying the resulting law with the input measure explicitly requires that
input to be a probability measure.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
noncomputable section

/-- Probability levels strictly between zero and one. -/
abbrev OpenUnitInterval := {u : ℝ // u ∈ Ioo (0 : ℝ) 1}

/-- Lower quantile of the Mathlib CDF; endpoints are excluded from its domain. -/
def RealQuantile (μ : Measure ℝ) (u : OpenUnitInterval) : ℝ :=
  sInf {x : ℝ | (u : ℝ) ≤ cdf μ x}

/-- The CDF limit at positive infinity supplies a point above the level. -/
theorem QuantileUpperSetNonempty (μ : Measure ℝ) (u : OpenUnitInterval) :
    {x : ℝ | (u : ℝ) ≤ cdf μ x}.Nonempty := by
  have EventuallyAbove : ∀ᶠ x in atTop, (u : ℝ) < cdf μ x :=
    (tendsto_cdf_atTop μ).eventually (lt_mem_nhds u.2.2)
  obtain ⟨x, Above⟩ := EventuallyAbove.exists
  exact ⟨x, Above.le⟩

/-- The CDF limit at negative infinity bounds the upper level set from below. -/
theorem QuantileUpperSetBddBelow (μ : Measure ℝ) (u : OpenUnitInterval) :
    BddBelow {x : ℝ | (u : ℝ) ≤ cdf μ x} := by
  have EventuallyBelow : ∀ᶠ x in atBot, cdf μ x < (u : ℝ) :=
    (tendsto_cdf_atBot μ).eventually (gt_mem_nhds u.2.1)
  obtain ⟨x, Below⟩ := EventuallyBelow.exists
  refine ⟨x, ?_⟩
  intro y Member
  by_contra NotAbove
  have Order : y ≤ x := le_of_lt (lt_of_not_ge NotAbove)
  have Smaller := (monotone_cdf μ Order).trans_lt Below
  exact not_lt_of_ge Member Smaller

/-- Right continuity ensures the quantile attains its upper CDF level set. -/
theorem QuantileCDFLowerBound (μ : Measure ℝ) (u : OpenUnitInterval) :
    (u : ℝ) ≤ cdf μ (RealQuantile μ u) := by
  let S := {x : ℝ | (u : ℝ) ≤ cdf μ x}
  have Nonempty : S.Nonempty := QuantileUpperSetNonempty μ u
  have Bounded : BddBelow S := QuantileUpperSetBddBelow μ u
  have WithinRight : S ⊆ Ici (sInf S) := by
    intro x Member
    exact csInf_le Bounded Member
  have ContinuousAtInf : ContinuousWithinAt (cdf μ) S (sInf S) :=
    ((cdf μ).right_continuous (sInf S)).mono WithinRight
  change (u : ℝ) ≤ cdf μ (sInf S)
  rw [MonotoneOn.map_csInf_of_continuousWithinAt ContinuousAtInf
    ((monotone_cdf μ).monotoneOn S) Nonempty Bounded]
  apply le_csInf (Nonempty.image (cdf μ))
  rintro y ⟨x, Member, rfl⟩
  exact Member

/-- The quantile threshold identity, valid for atomic distributions as well. -/
theorem QuantileLeIffCDF (μ : Measure ℝ) (u : OpenUnitInterval) (x : ℝ) :
    RealQuantile μ u ≤ x ↔ (u : ℝ) ≤ cdf μ x := by
  constructor
  · intro Below
    exact (QuantileCDFLowerBound μ u).trans (monotone_cdf μ Below)
  · intro Above
    exact csInf_le (QuantileUpperSetBddBelow μ u) Above

/-- Quantiles are nondecreasing in the probability level. -/
theorem QuantileMonotone (μ : Measure ℝ) : Monotone (RealQuantile μ) := by
  intro u v Ordered
  apply (QuantileLeIffCDF μ u (RealQuantile μ v)).mpr
  exact le_trans Ordered (QuantileCDFLowerBound μ v)

/-- Measurability follows from Mathlib's theorem for monotone maps. -/
theorem QuantileMeasurable (μ : Measure ℝ) : Measurable (RealQuantile μ) := by
  exact (QuantileMonotone μ).measurable

/-- Lebesgue measure transported to the open unit interval. -/
def OpenUnitUniform : Measure OpenUnitInterval := Measure.comap Subtype.val volume

/-- The open unit interval has Lebesgue measure one. -/
instance OpenUnitUniformProbability : IsProbabilityMeasure OpenUnitUniform := by
  constructor
  unfold OpenUnitUniform
  rw [comap_subtype_coe_apply measurableSet_Ioo volume,
    image_univ, Subtype.range_coe, Real.volume_Ioo]
  norm_num

/-- The uniform lower-tail probability, including thresholds zero and one. -/
theorem OpenUnitUniformLowerTail (a : ℝ) (AtMostOne : a ≤ 1) :
    OpenUnitUniform {u | (u : ℝ) ≤ a} = ENNReal.ofReal a := by
  rcases lt_or_eq_of_le AtMostOne with BelowOne | rfl
  · have ImageEq : Subtype.val '' {u : OpenUnitInterval | (u : ℝ) ≤ a} = Ioc 0 a := by
      ext x
      constructor
      · rintro ⟨u, Below, rfl⟩
        exact ⟨u.2.1, Below⟩
      · intro Member
        exact ⟨⟨x, ⟨Member.1, lt_of_le_of_lt Member.2 BelowOne⟩⟩, Member.2, rfl⟩
    unfold OpenUnitUniform
    rw [comap_subtype_coe_apply measurableSet_Ioo volume, ImageEq,
      Real.volume_Ioc, sub_zero]
  · have WholeSpace : {u : OpenUnitInterval | (u : ℝ) ≤ 1} = univ := by
      apply eq_univ_of_forall
      intro u
      exact u.2.2.le
    rw [WholeSpace, measure_univ, ENNReal.ofReal_one]

/-- The quantile of an open-unit uniform variable has exactly the given law. -/
theorem QuantileHasLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasLaw (RealQuantile μ) μ OpenUnitUniform := by
  have MeasurableQuantile := QuantileMeasurable μ
  have ProbabilityImage : IsProbabilityMeasure (OpenUnitUniform.map (RealQuantile μ)) :=
    Measure.isProbabilityMeasure_map MeasurableQuantile.aemeasurable
  refine ⟨MeasurableQuantile.aemeasurable, ?_⟩
  apply Measure.ext_of_Iic _ μ
  intro x
  rw [Measure.map_apply MeasurableQuantile measurableSet_Iic]
  have EventEq : (RealQuantile μ) ⁻¹' Iic x =
      {u : OpenUnitInterval | (u : ℝ) ≤ cdf μ x} := by
    ext u
    exact QuantileLeIffCDF μ u x
  rw [EventEq, OpenUnitUniformLowerTail (cdf μ x) (cdf_le_one μ x), ofReal_cdf μ x]

end
end ECTheoryLib.Probability
