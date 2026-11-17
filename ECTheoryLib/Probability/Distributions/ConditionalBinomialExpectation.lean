import ECTheoryLib.Probability.Distributions.BinomialConditioning
import ECTheoryLib.Probability.Distributions.BinomialExpectation
import ECTheoryLib.Probability.StochasticOrder.NatStochasticDomination

/-!
# Conditional binomial expectation

Book Lemma 1.7.3, under its necessary positive-conditioning-event convention.
The stronger forced-success domination from E05h yields the mean bound after
integrability is established. Valid zero-parameter cases are included.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- The conditional count is bounded by n almost surely, hence integrable. -/
theorem ConditionalBinomialIntegrable (n k : ℕ) (p : I)
    (PositiveEvent : binomial n p (Ici k) ≠ 0) :
    Integrable (Nat.cast : ℕ → ℝ) (cond (binomial n p) (Ici k)) := by
  have ProbabilityCond : IsProbabilityMeasure (cond (binomial n p) (Ici k)) :=
    cond_isProbabilityMeasure PositiveEvent
  apply Integrable.mono' (integrable_const (n : ℝ))
    (measurable_of_countable _).aestronglyMeasurable
  have OriginalBound : ∀ᵐ j ∂binomial n p, j ≤ n :=
    ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))
  have Bound : ∀ᵐ j ∂cond (binomial n p) (Ici k), j ≤ n :=
    cond_absolutelyContinuous.ae_le OriginalBound
  filter_upwards [Bound] with j Below
  rw [Real.norm_of_nonneg (Nat.cast_nonneg j)]
  exact_mod_cast Below

/-- Extend forced-success domination to all valid endpoint cases. -/
theorem ConditionalBinomialLEForcedOfPositiveEvent (n k : ℕ) (p : I)
    (Threshold : k ≤ n) (PositiveEvent : binomial n p (Ici k) ≠ 0) :
    StochasticDominated (cond (binomial n p) (Ici k))
      ((binomial (n - k) p).map (fun j => j + k)) := by
  by_cases ZeroThreshold : k = 0
  · subst k
    rw [show Ici (0 : ℕ) = univ from Ici_bot, cond_univ, Nat.sub_zero]
    simp only [Nat.add_zero]
    change StochasticDominated (binomial n p) ((binomial n p).map id)
    rw [Measure.map_id]
    exact StochasticDominatedRefl _
  · have PositiveP : 0 < (p : ℝ) := by
      by_contra NotPositive
      have ZeroReal : (p : ℝ) = 0 := le_antisymm (le_of_not_gt NotPositive) p.2.1
      have ZeroP : p = 0 := Subtype.ext ZeroReal
      subst p
      have ZeroLaw : binomial n 0 = Measure.dirac 0 := by
        rw [binomial, setBernoulli_zero, Measure.map_dirac' measurable_ncard]
        rw [Set.ncard_empty]
      apply PositiveEvent
      rw [ZeroLaw]
      have NotMember : (0 : ℕ) ∉ Ici k := by
        simp only [mem_Ici]
        omega
      rw [Measure.dirac_apply' 0 measurableSet_Ici, Set.indicator_of_notMem NotMember]
    exact ConditionalBinomialLEForced n k p Threshold PositiveP PositiveEvent

/-- The exact mean of a count shifted by a fixed number of successes. -/
theorem ShiftedBinomialExpectation (n k : ℕ) (p : I) :
    (∫ j, (j : ℝ) ∂(binomial n p).map (fun j => j + k)) =
      (k : ℝ) + (n : ℝ) * (p : ℝ) := by
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [Nat.cast_add]
  rw [integral_add (integrable_binomial _) (integrable_const _), integral_const,
    probReal_univ, one_smul, BinomialExpectation]
  ring

/-- Book 1.7.3: at most k forced successes plus the mean of n-k fresh trials. -/
theorem ConditionalBinomialExpectationBound (n k : ℕ) (p : I)
    (Threshold : k ≤ n) (PositiveEvent : binomial n p (Ici k) ≠ 0) :
    (∫ j, (j : ℝ) ∂cond (binomial n p) (Ici k)) ≤
      (k : ℝ) + ((n - k : ℕ) : ℝ) * (p : ℝ) := by
  have ProbabilityCond : IsProbabilityMeasure (cond (binomial n p) (Ici k)) :=
    cond_isProbabilityMeasure PositiveEvent
  have ProbabilityShift : IsProbabilityMeasure ((binomial (n - k) p).map (fun j => j + k)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have IntegrableShift : Integrable (Nat.cast : ℕ → ℝ)
      ((binomial (n - k) p).map (fun j => j + k)) := by
    apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr
    exact integrable_binomial _
  have Bound := StochasticDominatedNatIntegralLE _ _
    (ConditionalBinomialLEForcedOfPositiveEvent n k p Threshold PositiveEvent)
    (ConditionalBinomialIntegrable n k p PositiveEvent) IntegrableShift
  rw [ShiftedBinomialExpectation] at Bound
  exact Bound

/-- Both inequalities in the displayed book statement. -/
theorem ConditionalBinomialExpectationBounds (n k : ℕ) (p : I)
    (Threshold : k ≤ n) (PositiveEvent : binomial n p (Ici k) ≠ 0) :
    (∫ j, (j : ℝ) ∂cond (binomial n p) (Ici k)) ≤
        (k : ℝ) + ((n - k : ℕ) : ℝ) * (p : ℝ) ∧
      (k : ℝ) + ((n - k : ℕ) : ℝ) * (p : ℝ) ≤
        (k : ℝ) + ∫ j, (j : ℝ) ∂binomial n p := by
  constructor
  · exact ConditionalBinomialExpectationBound n k p Threshold PositiveEvent
  · rw [BinomialExpectation]
    apply add_le_add_right
    calc
      ((n - k : ℕ) : ℝ) * (p : ℝ) ≤ (n : ℝ) * (p : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ p.2.1
        exact_mod_cast Nat.sub_le n k
      _ = (p : ℝ) * (n : ℝ) := mul_comm _ _

/-- Conditioning a variable and conditioning its law commute. -/
theorem ConditionalBinomialLawOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (n k : ℕ) (p : I)
    (MeasurableX : Measurable X) (Law : HasLaw X (binomial n p) P) :
    HasLaw X (cond (binomial n p) (Ici k)) (cond P {ω | k ≤ X ω}) := by
  refine ⟨MeasurableX.aemeasurable, ?_⟩
  change (cond P (X ⁻¹' Ici k)).map X = _
  rw [ConditionalMap P X MeasurableX (Ici k) measurableSet_Ici, Law.map_eq]

/-- The conditional expectation is a genuine finite expectation. -/
theorem ConditionalBinomialIntegrableOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (n k : ℕ) (p : I)
    (MeasurableX : Measurable X) (Law : HasLaw X (binomial n p) P)
    (PositiveEvent : P {ω | k ≤ X ω} ≠ 0) :
    Integrable (fun ω => (X ω : ℝ)) (cond P {ω | k ≤ X ω}) := by
  have BinomialPositive : binomial n p (Ici k) ≠ 0 := by
    change binomial n p {j | k ≤ j} ≠ 0
    rw [← Law.measure_eq (p := fun j => k ≤ j) measurableSet_Ici]
    exact PositiveEvent
  have ConditionalLaw := ConditionalBinomialLawOfLaw P X n k p MeasurableX Law
  have IntegrableLaw := ConditionalBinomialIntegrable n k p BinomialPositive
  rw [← ConditionalLaw.map_eq] at IntegrableLaw
  exact IntegrableLaw.comp_aemeasurable ConditionalLaw.aemeasurable

/-- Transfer the conditional mean bound to an actual variable on any sample space. -/
theorem ConditionalBinomialExpectationOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (n k : ℕ) (p : I)
    (MeasurableX : Measurable X) (Law : HasLaw X (binomial n p) P)
    (Threshold : k ≤ n) (PositiveEvent : P {ω | k ≤ X ω} ≠ 0) :
    (∫ ω, (X ω : ℝ) ∂cond P {ω | k ≤ X ω}) ≤
      (k : ℝ) + ((n - k : ℕ) : ℝ) * (p : ℝ) := by
  have BinomialPositive : binomial n p (Ici k) ≠ 0 := by
    change binomial n p {j | k ≤ j} ≠ 0
    rw [← Law.measure_eq (p := fun j => k ≤ j) measurableSet_Ici]
    exact PositiveEvent
  have ConditionalLaw := ConditionalBinomialLawOfLaw P X n k p MeasurableX Law
  have IntegralEq := ConditionalLaw.integral_comp (f := (Nat.cast : ℕ → ℝ))
    (measurable_of_countable _).aestronglyMeasurable
  change (∫ ω, (X ω : ℝ) ∂cond P {ω | k ≤ X ω}) =
    ∫ j, (j : ℝ) ∂cond (binomial n p) (Ici k) at IntegralEq
  rw [IntegralEq]
  exact ConditionalBinomialExpectationBound n k p Threshold BinomialPositive

end
end ECTheoryLib.Probability

