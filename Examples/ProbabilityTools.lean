import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Direct Mathlib calls for elementary probability and expectation tools used in Chapter 1. See docs/SOURCE_NOTES.md or docs/COVERAGE.md for source relations. -/




open MeasureTheory

-- Lemma 1.4.1; this same upstream result is used by multiplicative drift tails.
example (x : ℝ) : 1 + x ≤ Real.exp x := by
  rw [add_comm]
  exact Real.add_one_le_exp x

-- Lemma 1.5.1: no independence or event-disjointness is required.
example {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Events : ι → Set Ω) (Indices : Finset ι) :
    μ (⋃ i ∈ Indices, Events i) ≤ ∑ i ∈ Indices, μ (Events i) := by
  exact measure_biUnion_finset_le Indices Events

-- Lemma 1.6.4: signed coefficients and dependent random variables are allowed.
example {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Indices : Finset ι) (Coefficient : ι → ℝ) (X : ι → Ω → ℝ)
    (FiniteMeans : ∀ i ∈ Indices, Integrable (X i) μ) :
    (∫ ω, ∑ i ∈ Indices, Coefficient i * X i ω ∂μ) =
      ∑ i ∈ Indices, Coefficient i * ∫ ω, X i ω ∂μ := by
  rw [integral_finsetSum Indices (fun i hi => (FiniteMeans i hi).const_mul (Coefficient i))]
  apply Finset.sum_congr rfl
  intro i _hi
  exact integral_const_mul (Coefficient i) (X i)

-- Lemma 1.6.7: both displayed forms, with a genuine finite positive mean.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Nonnegative : ∀ᵐ ω ∂μ, 0 ≤ X ω) (FiniteMean : Integrable X μ)
    (PositiveMean : 0 < ∫ ω, X ω ∂μ) (Threshold : ℝ) (PositiveThreshold : 0 < Threshold) :
    μ.real {ω | Threshold * (∫ a, X a ∂μ) ≤ X ω} ≤ 1 / Threshold ∧
      μ.real {ω | Threshold ≤ X ω} ≤ (∫ a, X a ∂μ) / Threshold := by
  have Markov : ∀ a : ℝ, 0 < a → μ.real {ω | a ≤ X ω} ≤ (∫ ω, X ω ∂μ) / a := by
    intro a PositiveA
    apply (le_div_iff₀ PositiveA).mpr
    have Bound := mul_meas_ge_le_integral_of_nonneg Nonnegative FiniteMean a
    rw [mul_comm] at Bound
    exact Bound
  constructor
  · have Bound := Markov (Threshold * (∫ a, X a ∂μ)) (mul_pos PositiveThreshold PositiveMean)
    have Normalize : (∫ a, X a ∂μ) / (Threshold * (∫ a, X a ∂μ)) = 1 / Threshold := by
      field_simp
    rw [Normalize] at Bound
    exact Bound
  · exact Markov Threshold PositiveThreshold

-- Corollary 1.6.8: the extended nonnegative integral keeps infinite means.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ENNReal) (MeasurableX : AEMeasurable X μ) :
    μ {ω | 1 ≤ X ω} ≤ ∫⁻ ω, X ω ∂μ := by
  have Bound := mul_meas_ge_le_lintegral₀ MeasurableX 1
  rw [one_mul] at Bound
  exact Bound
