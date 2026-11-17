import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The geometric waiting-time convention

Doerr, Lemma 1.6.3 (p. 17), counts trials up to and including the first success.
Mathlib's `geometricMeasure p` counts failures before that success. We reuse that
measure and apply `Nat.succ`; no new probability distribution is defined.

The success probability is positive. Mathlib defines its zero-parameter measure
as a Dirac mass for convenience, so that endpoint has no waiting-time meaning.
Integrability is proved before the real integral is used as an expectation.
-/

namespace ECTheoryLib.Probability

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

private theorem GeometricWaitingHasSum (p : I) (PositiveProbability : 0 < (p : ℝ)) :
    HasSum (fun n : ℕ => ((1 - (p : ℝ)) ^ n * p) * ((n : ℝ) + 1)) (1 / (p : ℝ)) := by
  have FailureNorm : ‖1 - (p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.2.2)]
    linarith
  have WeightedSeries :=
    (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 FailureNorm).mul_right (p : ℝ)
  have SeriesTerms :
      (fun n : ℕ => ((n + 1).choose 1 : ℝ) * (1 - (p : ℝ)) ^ n * p) =
        (fun n : ℕ => ((1 - (p : ℝ)) ^ n * p) * ((n : ℝ) + 1)) := by
    funext n
    rw [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    ring
  rw [SeriesTerms] at WeightedSeries
  have SeriesValue : (1 / (1 - (1 - (p : ℝ))) ^ (1 + 1)) * p = 1 / (p : ℝ) := by
    field_simp
    ring
  rw [SeriesValue] at WeightedSeries
  exact WeightedSeries

/-- The shifted geometric count has a genuine finite first moment. -/
theorem GeometricWaitingIntegrable (p : I) (PositiveProbability : 0 < (p : ℝ)) :
    Integrable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) (geometricMeasure p) := by
  have Nonzero : p ≠ 0 := by
    intro Zero
    have : (p : ℝ) = 0 := congrArg Subtype.val Zero
    linarith
  rw [integrable_geometricMeasure_iff Nonzero]
  have WeightedSummable := (GeometricWaitingHasSum p PositiveProbability).summable
  apply WeightedSummable.congr
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_one]

/-- Lemma 1.6.3: the expected number of trials, including the successful trial. -/
theorem GeometricWaitingExpectation (p : I) (PositiveProbability : 0 < (p : ℝ)) :
    (∫ n : ℕ, ((n + 1 : ℕ) : ℝ) ∂geometricMeasure p) = 1 / (p : ℝ) := by
  have Nonzero : p ≠ 0 := by
    intro Zero
    have : (p : ℝ) = 0 := congrArg Subtype.val Zero
    linarith
  have IntegralSeries := hasSum_integral_geometricMeasure Nonzero
    (GeometricWaitingIntegrable p PositiveProbability)
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one] at IntegralSeries
  simp only [Nat.cast_add, Nat.cast_one]
  exact IntegralSeries.unique (GeometricWaitingHasSum p PositiveProbability)

/-- Every random variable with the shifted geometric law is integrable. -/
theorem GeometricWaitingIntegrableOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℕ) (p : I) (PositiveProbability : 0 < (p : ℝ))
    (WaitingLaw : HasLaw X ((geometricMeasure p).map Nat.succ) μ) :
    Integrable (fun ω => (X ω : ℝ)) μ := by
  have ShiftedIntegrable :
      Integrable (fun n : ℕ => (n : ℝ)) ((geometricMeasure p).map Nat.succ) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    exact GeometricWaitingIntegrable p PositiveProbability
  rw [← WaitingLaw.map_eq] at ShiftedIntegrable
  exact ShiftedIntegrable.comp_aemeasurable WaitingLaw.aemeasurable

/-- The waiting-time formula transfers to any random variable with the shifted law.
An application must establish this law; a one-step success probability alone does
not establish independent repeated trials. -/
theorem GeometricWaitingExpectationOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℕ) (p : I) (PositiveProbability : 0 < (p : ℝ))
    (WaitingLaw : HasLaw X ((geometricMeasure p).map Nat.succ) μ) :
    (∫ ω, (X ω : ℝ) ∂μ) = 1 / (p : ℝ) := by
  have Transfer := WaitingLaw.integral_comp
    (f := fun n : ℕ => (n : ℝ)) (by fun_prop)
  change (∫ ω, (X ω : ℝ) ∂μ) =
    ∫ n : ℕ, (n : ℝ) ∂(geometricMeasure p).map Nat.succ at Transfer
  rw [Transfer, integral_map (by fun_prop) (by fun_prop)]
  exact GeometricWaitingExpectation p PositiveProbability

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
noncomputable section

/-- A lower exponential estimate for surviving independent Bernoulli trials.
It follows from Mathlib's logarithmic inequality, without defining a new law. -/
theorem BernoulliFailurePowerExponentialLower (p : ℝ) (BelowOne : p<1) (t : ℕ) :
    Real.exp (-(t : ℝ)*p/(1-p))≤(1-p)^t := by
  have Positive : 0<1-p := sub_pos.mpr BelowOne
  have LogLower := Real.one_sub_inv_le_log_of_pos Positive
  have Rational : 1-(1-p)⁻¹= -p/(1-p) := by
    field_simp [Positive.ne']
    ring
  rw [Rational] at LogLower
  rw [← Real.exp_log (pow_pos Positive t),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have Scaled := mul_le_mul_of_nonneg_left LogLower (Nat.cast_nonneg t : (0 : ℝ)≤t)
  calc
    -(t : ℝ)*p/(1-p)=(t : ℝ)*(-p/(1-p)) := by ring
    _≤(t : ℝ)*Real.log (1-p) := Scaled

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped unitInterval
noncomputable section

/-- Exact extended mean of the independent geometric reference waits, including an empty sum. -/
theorem GeometricWaitingProductSumExpectation {ι : Type*} [Fintype ι]
    (p : ι → I) (Positive : ∀ i, 0 < (p i : ℝ)) :
    (∫⁻ z : ι → ℕ, ENat.toENNReal (∑ i, ((z i + 1 : ℕ) : WithTop ℕ))
      ∂Measure.pi (fun i => geometricMeasure (p i))) =
      ∑ i, ENNReal.ofReal (1 / (p i : ℝ)) := by
  classical
  have CoordinateMean (i : ι) :
      (∫⁻ z : ι → ℕ, ((z i + 1 : ℕ) : ENNReal)
        ∂Measure.pi (fun i => geometricMeasure (p i))) = ENNReal.ofReal (1 / (p i : ℝ)) := by
    rw [(measurePreserving_eval (fun i => geometricMeasure (p i)) i).lintegral_comp
      (measurable_of_countable (fun n : ℕ => ((n + 1 : ℕ) : ENNReal)))]
    have Conversion := ofReal_integral_eq_lintegral_ofReal
      (GeometricWaitingIntegrable (p i) (Positive i))
      (ae_of_all _ (fun n => Nat.cast_nonneg (n + 1)))
    rw [GeometricWaitingExpectation (p i) (Positive i)] at Conversion
    simpa only [ENNReal.ofReal_natCast] using Conversion.symm
  have SumValue (z : ι → ℕ) :
      ENat.toENNReal (∑ i, ((z i + 1 : ℕ) : WithTop ℕ)) =
        ∑ i, ((z i + 1 : ℕ) : ENNReal) := by
    exact map_sum ENat.toENNRealRingHom (fun i => ((z i + 1 : ℕ) : WithTop ℕ)) Finset.univ
  simp_rw [SumValue]
  calc
    (∫⁻ z : ι → ℕ, ∑ i, ((z i + 1 : ℕ) : ENNReal)
      ∂Measure.pi (fun i => geometricMeasure (p i))) =
        ∑ i, ∫⁻ z : ι → ℕ, ((z i + 1 : ℕ) : ENNReal)
          ∂Measure.pi (fun i => geometricMeasure (p i)) :=
      lintegral_finsetSum Finset.univ (fun i _ =>
        (measurable_of_countable (fun n : ℕ => ((n + 1 : ℕ) : ENNReal))).comp
          (measurable_pi_apply i))
    _ = _ := Finset.sum_congr rfl (fun i _ => CoordinateMean i)

end
end ECTheoryLib.Probability
