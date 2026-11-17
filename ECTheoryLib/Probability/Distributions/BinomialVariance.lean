import ECTheoryLib.Probability.Distributions.BinomialTail
import ECTheoryLib.Probability.Distributions.BinomialExpectation
import Mathlib.Data.Nat.Choose.Cast

/-!
# Binomial second moments, variance, and deviation probabilities

The fixed Mathlib has an unproved variance placeholder. We use only proved
APIs: the choose moment, bounded Lp membership, variance expansion, and Chebyshev.
All probability endpoints and zero trials are retained.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- The second raw moment from the choose moment at k = 2. -/
theorem BinomialSecondMoment (n : ℕ) (p : I) :
    (∫ j, (j : ℝ) ^ 2 ∂binomial n p) =
      (n : ℝ) * ((n : ℝ) - 1) * (p : ℝ) ^ 2 + (n : ℝ) * (p : ℝ) := by
  have Pointwise (j : ℕ) : (j : ℝ) ^ 2 = 2 * (j.choose 2 : ℝ) + j := by
    rw [Nat.cast_choose_two]
    ring
  calc
    (∫ j, (j : ℝ) ^ 2 ∂binomial n p) =
        ∫ j, 2 * (j.choose 2 : ℝ) + j ∂binomial n p := by
      apply integral_congr_ae
      exact ae_of_all _ Pointwise
    _ = 2 * (∫ j, (j.choose 2 : ℝ) ∂binomial n p) +
        ∫ j, (j : ℝ) ∂binomial n p := by
      rw [integral_add (integrable_binomial _) (integrable_binomial _), integral_const_mul]
    _ = _ := by
      rw [BinomialChooseMoment, BinomialExpectation, Nat.cast_choose_two]
      ring

/-- Every real cast of a binomial count belongs to every Lp space. -/
theorem BinomialNatMemLp (n : ℕ) (p : I) (q : ENNReal) :
    MemLp (Nat.cast : ℕ → ℝ) q (binomial n p) := by
  have Bound : ∀ᵐ (j : ℕ) ∂binomial n p, (j : ℝ) ∈ Icc 0 (n : ℝ) := by
    filter_upwards [ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))] with j Below
    change j ≤ n at Below
    exact ⟨Nat.cast_nonneg j, Nat.cast_le.mpr Below⟩
  exact memLp_of_bounded Bound (measurable_of_countable _).aestronglyMeasurable q

/-- The binomial variance, proved without the upstream placeholder. -/
theorem BinomialVariance (n : ℕ) (p : I) :
    variance (Nat.cast : ℕ → ℝ) (binomial n p) =
      (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) := by
  rw [variance_eq_sub (BinomialNatMemLp n p 2)]
  change (∫ j, (j : ℝ) ^ 2 ∂binomial n p) - (∫ j, (j : ℝ) ∂binomial n p) ^ 2 = _
  rw [BinomialSecondMoment, BinomialExpectation]
  ring

/-- Transfer variance to an actual natural-valued variable. -/
theorem BinomialNatVarianceOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (n : ℕ) (p : I)
    (Law : HasLaw X (binomial n p) P) :
    variance (fun ω => (X ω : ℝ)) P = (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) := by
  have Transfer := variance_map (X := (Nat.cast : ℕ → ℝ))
    (measurable_of_countable _).aemeasurable Law.aemeasurable
  rw [Law.map_eq] at Transfer
  change variance (Nat.cast : ℕ → ℝ) (binomial n p) =
    variance (fun ω => (X ω : ℝ)) P at Transfer
  rw [← Transfer, BinomialVariance]

/-- Transfer variance to an actual real-valued variable. -/
theorem BinomialRealVarianceOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (n : ℕ) (p : I)
    (Law : HasLaw X ((binomial n p).map (Nat.cast : ℕ → ℝ)) P) :
    variance X P = (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) := by
  rw [← variance_id_map Law.aemeasurable, Law.map_eq,
    variance_id_map (measurable_of_countable _).aemeasurable]
  exact BinomialVariance n p

/-- The binomial law supplies the required moment hypotheses. -/
theorem BinomialNatMemLpOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (n : ℕ) (p : I) (q : ENNReal)
    (Law : HasLaw X (binomial n p) P) : MemLp (fun ω => (X ω : ℝ)) q P := by
  have Mapped := BinomialNatMemLp n p q
  rw [← Law.map_eq] at Mapped
  exact Mapped.comp_of_map Law.aemeasurable

/-- Mathlib Chebyshev instantiated with the proved binomial mean and variance. -/
theorem BinomialNatDeviationProbabilityOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℕ) (n : ℕ) (p : I)
    (Law : HasLaw X (binomial n p) P) (c : ℝ) (PositiveThreshold : 0 < c) :
    P {ω | c ≤ |(X ω : ℝ) - (n : ℝ) * (p : ℝ)|} ≤
      ENNReal.ofReal ((n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) / c ^ 2) := by
  have Bound := meas_ge_le_variance_div_sq (BinomialNatMemLpOfLaw P X n p 2 Law)
    PositiveThreshold
  rw [BinomialNatExpectationOfLaw P X n p Law, BinomialNatVarianceOfLaw P X n p Law,
    mul_comm (p : ℝ) (n : ℝ)] at Bound
  exact Bound

end
end ECTheoryLib.Probability

