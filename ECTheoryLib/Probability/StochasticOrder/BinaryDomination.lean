import ECTheoryLib.Probability.StochasticOrder.StochasticDomination
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Binary laws, success probabilities and stochastic domination

Binary range is required almost surely. Mathlib handles indicator integrals
and measurable maps; no new Bernoulli distribution is defined.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- The three strict-tail regimes of an almost-surely binary probability law. -/
theorem BinaryLawStrictTail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Binary : ∀ᵐ x ∂μ, x = 0 ∨ x = 1) (a : ℝ) :
    μ (Ioi a) = if a < 0 then 1 else if a < 1 then μ {1} else 0 := by
  by_cases Negative : a < 0
  · rw [if_pos Negative, ← measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [Binary] with x Value
    change (a < x) = True
    apply propext
    rcases Value with rfl | rfl
    · exact iff_true_intro Negative
    · exact iff_true_intro (lt_trans Negative zero_lt_one)
  · rw [if_neg Negative]
    by_cases BelowOne : a < 1
    · rw [if_pos BelowOne]
      apply measure_congr
      filter_upwards [Binary] with x Value
      change (a < x) = (x = 1)
      apply propext
      rcases Value with rfl | rfl
      · simp only [zero_ne_one, iff_false]
        exact Negative
      · exact iff_of_true BelowOne rfl
    · rw [if_neg BelowOne, ← measure_empty (μ := μ)]
      apply measure_congr
      filter_upwards [Binary] with x Value
      change (a < x) = False
      apply propext
      rcases Value with rfl | rfl
      · exact iff_false_intro Negative
      · exact iff_false_intro BelowOne

/-- Binary probability laws are ordered exactly by their success masses. -/
theorem BinaryLawStochasticDominatedIff (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Binaryμ : ∀ᵐ x ∂μ, x = 0 ∨ x = 1) (Binaryν : ∀ᵐ x ∂ν, x = 0 ∨ x = 1) :
    StochasticDominated μ ν ↔ μ {1} ≤ ν {1} := by
  rw [StochasticDominatedIffStrictTail]
  constructor
  · intro Ordered
    have Bound := Ordered 0
    rw [BinaryLawStrictTail μ Binaryμ 0, BinaryLawStrictTail ν Binaryν 0] at Bound
    norm_num at Bound
    exact Bound
  · intro SuccessBound a
    rw [BinaryLawStrictTail μ Binaryμ a, BinaryLawStrictTail ν Binaryν a]
    split
    · exact le_rfl
    · split
      · exact SuccessBound
      · exact le_rfl

/-- Success probabilities characterize binary-variable order on different spaces. -/
theorem BinaryVariableStochasticDominatedIff {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (MeasurableX : Measurable X) (MeasurableY : Measurable Y)
    (BinaryX : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) (BinaryY : ∀ᵐ ω ∂Q, Y ω = 0 ∨ Y ω = 1) :
    StochasticDominated (P.map X) (Q.map Y) ↔ P {ω | X ω = 1} ≤ Q {ω | Y ω = 1} := by
  have ProbabilityX : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map MeasurableX.aemeasurable
  have ProbabilityY : IsProbabilityMeasure (Q.map Y) :=
    Measure.isProbabilityMeasure_map MeasurableY.aemeasurable
  have RangeX : ∀ᵐ x ∂P.map X, x = 0 ∨ x = 1 := by
    apply (ae_map_iff MeasurableX.aemeasurable
      ((measurableSet_singleton (0 : ℝ)).union (measurableSet_singleton 1))).mpr
    exact BinaryX
  have RangeY : ∀ᵐ x ∂Q.map Y, x = 0 ∨ x = 1 := by
    apply (ae_map_iff MeasurableY.aemeasurable
      ((measurableSet_singleton (0 : ℝ)).union (measurableSet_singleton 1))).mpr
    exact BinaryY
  rw [BinaryLawStochasticDominatedIff _ _ RangeX RangeY,
    Measure.map_apply MeasurableX (measurableSet_singleton 1),
    Measure.map_apply MeasurableY (measurableSet_singleton 1)]
  rfl

/-- Almost-sure binary range supplies integrability without a separate assumption. -/
theorem BinaryVariableIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (MeasurableX : Measurable X)
    (BinaryX : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) : Integrable X P := by
  apply (integrable_const (1 : ℝ)).mono' MeasurableX.aestronglyMeasurable
  filter_upwards [BinaryX] with ω Value
  rcases Value with Zero | One
  · rw [Zero]
    norm_num
  · rw [One]
    norm_num

/-- The mean of a binary probability variable is its success probability. -/
theorem BinaryVariableMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (MeasurableX : Measurable X)
    (BinaryX : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) :
    (∫ ω, X ω ∂P) = P.real {ω | X ω = 1} := by
  classical
  have IndicatorEq : X =ᵐ[P] Set.indicator {ω | X ω = 1} (fun _ => (1 : ℝ)) := by
    filter_upwards [BinaryX] with ω Value
    rcases Value with Zero | One
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | X ω = 1} by
        rw [mem_ofPred_eq, Zero]
        exact zero_ne_one), Zero]
    · rw [Set.indicator_of_mem (show ω ∈ {ω | X ω = 1} from One), One]
  rw [integral_congr_ae IndicatorEq,
    integral_indicator_const (1 : ℝ) (measurableSet_eq_fun MeasurableX measurable_const),
    smul_eq_mul, mul_one]

end
end ECTheoryLib.Probability
