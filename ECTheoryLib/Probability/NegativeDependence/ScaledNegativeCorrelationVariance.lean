import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationFiniteVariance
import ECTheoryLib.Probability.Concentration.ScaledVarianceChernoff

/-!
# Negative-correlation variance tails at a positive centered scale

The variance parts of Doerr 1.10.23/24 apply here to same-sample ordered
affine indicators with all-subset one/zero-negative correlation. Scaling
by b > 0 reuses the unit-scale finite bound and Mathlib variance identities.
The variance parameter is the sum of actual marginal variances, not the
variance of the total. Closed endpoints and zero variance are retained.
Zero scale is handled by the existing separate deterministic theorems.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Same-sample ordered affine indicators, all-subset one-negative correlation,
and a positive centered upper scale. The variance parameter is the sum of the
actual marginal variances, not the variance of the sum. -/
theorem OneNegativeCorrelationFiniteVarianceUpperScaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events)
    (a c : Fin n → ℝ) (Ordered : ∀ i, a i ≤ c i)
    (b : ℝ) (PositiveScale : 0 < b)
    (Upper : ∀ i, ∀ᵐ ω ∂P,
      a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω ≤
        (∫ w, a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) w ∂P) + b)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (∫ w, ∑ i,
        (a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) w) ∂P) + d ≤
      ∑ i, (a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω)} ≤
      ScaledVarianceFiniteUpperBound n b
        (∑ i, variance (fun ω =>
          a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω) P) d := by
  let X := fun i ω => a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω
  have Identity (i : Fin n) (ω : Ω) :
      a i / b + (c i / b - a i / b) * (Events i).indicator (fun _ => (1 : ℝ)) ω =
        X i ω / b := by
    dsimp only [X]
    ring
  have OrderedScaled (i : Fin n) : a i / b ≤ c i / b :=
    (div_le_div_iff_of_pos_right PositiveScale).mpr (Ordered i)
  have UpperScaled (i : Fin n) : ∀ᵐ ω ∂P,
      a i / b + (c i / b - a i / b) * (Events i).indicator (fun _ => (1 : ℝ)) ω ≤
        (∫ w, a i / b + (c i / b - a i / b) *
          (Events i).indicator (fun _ => (1 : ℝ)) w ∂P) + 1 := by
    simp_rw [Identity, integral_div]
    filter_upwards [Upper i] with ω Bound
    change X i ω ≤ (∫ w, X i w ∂P) + b at Bound
    rw [div_le_iff₀ PositiveScale]
    field_simp
    linarith
  have Bound := OneNegativeCorrelationFiniteVarianceUpper P Events MeasurableEvents Correlated
    (fun i => a i / b) (fun i => c i / b) OrderedScaled UpperScaled (d / b)
    (div_nonneg NonnegativeDeviation PositiveScale.le)
  simp_rw [Identity] at Bound
  have Variance (i : Fin n) :
      variance (fun ω => X i ω / b) P = variance (X i) P / b ^ 2 := by
    simp only [div_eq_mul_inv, variance_mul_const, inv_pow]
  have Event : {ω | (∫ w, ∑ i, X i w / b ∂P) + d / b ≤ ∑ i, X i ω / b} =
      {ω | (∫ w, ∑ i, X i w ∂P) + d ≤ ∑ i, X i ω} := by
    simp only [← Finset.sum_div, integral_div, ← add_div,
      div_le_div_iff_of_pos_right PositiveScale]
  rw [Event] at Bound
  simp only [Variance, ← Finset.sum_div] at Bound
  exact Bound

/-- Lower tails use all-subset zero-negative correlation of the same Events.
Negation uses their complements; it does not assume independence or merely
matching marginal laws. -/
theorem ZeroNegativeCorrelationFiniteVarianceLowerScaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events)
    (a c : Fin n → ℝ) (Ordered : ∀ i, a i ≤ c i)
    (b : ℝ) (PositiveScale : 0 < b)
    (Lower : ∀ i, ∀ᵐ ω ∂P,
      (∫ w, a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) w ∂P) - b ≤
        a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω)
    (d : ℝ) (NonnegativeDeviation : 0 ≤ d) :
    P.real {ω | (∑ i,
        (a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω)) ≤
      (∫ w, ∑ i, (a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) w) ∂P) - d} ≤
      ScaledVarianceFiniteUpperBound n b
        (∑ i, variance (fun ω =>
          a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω) P) d := by
  have UpperNeg (i : Fin n) : ∀ᵐ ω ∂P,
      -c i + (-a i - -c i) * (Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω ≤
        (∫ w, -c i + (-a i - -c i) * (Events i)ᶜ.indicator (fun _ => (1 : ℝ)) w ∂P) + b := by
    simp_rw [NegatedAffineIndicator, integral_neg]
    filter_upwards [Lower i] with ω Bound
    linarith
  have Bound := OneNegativeCorrelationFiniteVarianceUpperScaled P (fun i => (Events i)ᶜ)
    (fun i => (MeasurableEvents i).compl) Correlated (fun i => -c i) (fun i => -a i)
    (fun i => neg_le_neg (Ordered i)) b PositiveScale UpperNeg d NonnegativeDeviation
  simp_rw [NegatedAffineIndicator, Finset.sum_neg_distrib, integral_neg, variance_fun_neg] at Bound
  have Event : {ω | -(∫ w, ∑ i,
        (a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) w) ∂P) + d ≤
      -(∑ i, (a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω))} =
      {ω | (∑ i, (a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) ω)) ≤
        (∫ w, ∑ i, (a i + (c i - a i) * (Events i).indicator (fun _ => (1 : ℝ)) w) ∂P) - d} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rwa [Event] at Bound

end
end ECTheoryLib.Probability
