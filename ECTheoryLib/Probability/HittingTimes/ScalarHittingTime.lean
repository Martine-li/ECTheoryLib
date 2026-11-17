import ECTheoryLib.Probability.Processes.ScalarProcess
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Absorbing processes and runtime tail sums

Absorption identifies reaching zero by time `t` with being zero at time `t`,
almost surely. Tail sums use extended nonnegative reals, allowing infinite
hitting times and expectations. Neither termination nor a Markov property
is assumed. The general extended-natural tail formula itself needs no absorption.
-/

namespace ECTheoryLib.Probability

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Almost-sure stepwise absorption holds simultaneously at every natural time. -/
theorem ZeroIsAbsorbingAllTimes (μ : Measure Ω) (X : Nat → Ω → ℝ)
    (Absorbing : ZeroIsAbsorbing μ X) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = 0 → X (t + 1) ω = 0 := by
  exact ae_all_iff.mpr Absorbing

/-- After a zero hit, every later coordinate is zero outside a null set. -/
theorem ZeroIsAbsorbingAfter (μ : Measure Ω) (X : Nat → Ω → ℝ)
    (Absorbing : ZeroIsAbsorbing μ X) :
    ∀ᵐ ω ∂μ, ∀ s t, s ≤ t → X s ω = 0 → X t ω = 0 := by
  filter_upwards [ZeroIsAbsorbingAllTimes μ X Absorbing] with ω EveryStepAbsorbing
  intro s t BeforeTime AtZero
  apply Nat.le_induction (P := fun n _ => X n ω = 0) AtZero
  · intro n _BeforeN AtZeroAtN
    exact EveryStepAbsorbing n AtZeroAtN
  · exact BeforeTime

/-- For an absorbing process, hitting by `t` is almost surely equivalent
to zero potential at `t`. -/
theorem ZeroHittingTimeLeIffOfAbsorbing (μ : Measure Ω) (X : Nat → Ω → ℝ)
    (Absorbing : ZeroIsAbsorbing μ X) (t : Nat) :
    ∀ᵐ ω ∂μ, ZeroHittingTime X ω ≤ (t : WithTop Nat) ↔ X t ω = 0 := by
  filter_upwards [ZeroIsAbsorbingAfter μ X Absorbing] with ω StaysAtZero
  have HitCriterion :
      ZeroHittingTime X ω ≤ (t : WithTop Nat) ↔ ∃ s ≤ t, X s ω = 0 := by
    exact FirstHittingTimeLeIff (fun x : ℝ => x = 0) (fun s => X s ω) t
  constructor
  · intro HitByTime
    obtain ⟨s, BeforeTime, AtZero⟩ := HitCriterion.mp HitByTime
    exact StaysAtZero s t BeforeTime AtZero
  · intro AtZero
    exact HitCriterion.mpr ⟨t, le_refl t, AtZero⟩

/-- For an absorbing process, hitting after `t` is almost surely equivalent
to nonzero potential at `t`. -/
theorem ZeroHittingTimeTailIffOfAbsorbing (μ : Measure Ω) (X : Nat → Ω → ℝ)
    (Absorbing : ZeroIsAbsorbing μ X) (t : Nat) :
    ∀ᵐ ω ∂μ, (t : WithTop Nat) < ZeroHittingTime X ω ↔ X t ω ≠ 0 := by
  filter_upwards [ZeroHittingTimeLeIffOfAbsorbing μ X Absorbing t] with ω HitCriterion
  rw [← not_le]
  exact not_congr HitCriterion

/-- The hitting-time tail probability equals the nonzero-potential probability
under absorption. -/
theorem ZeroHittingTimeTailMeasureOfAbsorbing (μ : Measure Ω) (X : Nat → Ω → ℝ)
    (Absorbing : ZeroIsAbsorbing μ X) (t : Nat) :
    μ {ω | (t : WithTop Nat) < ZeroHittingTime X ω} = μ {ω | X t ω ≠ 0} := by
  apply measure_congr
  filter_upwards [ZeroHittingTimeTailIffOfAbsorbing μ X Absorbing t] with ω TailCriterion
  exact propext TailCriterion

/-- An extended natural equals the sum of its strict-tail indicators,
including the value infinity. -/
theorem WithTopNatValueEqTailSum (n : WithTop Nat) :
    ENat.toENNReal n = ∑' t : Nat, if (t : WithTop Nat) < n then (1 : ENNReal) else 0 := by
  classical
  -- ENat recursion preserves the numeric embedding of WithTop Nat.
  have ExtendedNatFormula : ∀ m : ENat,
      ENat.toENNReal m = ∑' t : Nat, if (t : ENat) < m then (1 : ENNReal) else 0 := by
    intro m
    induction m using ENat.recTopCoe with
    | top =>
      simp only [ENat.natCast_lt_top, if_true, ENat.toENNReal_top]
      exact (ENNReal.tsum_const_eq_top_of_ne_zero (one_ne_zero : (1 : ENNReal) ≠ 0)).symm
    | coe n =>
      rw [ENat.toENNReal_coe]
      -- Express the finite indicator sum as a nonnegative infinite sum.
      
      have TailSumIsFiniteCount :
          (∑' t : Nat, if (t : ENat) < (n : ENat)
            then (1 : ENNReal) else 0) =
          ∑ _t ∈ Finset.range n, (1 : ENNReal) := by
        rw [sum_eq_tsum_indicator]
        apply tsum_congr
        intro t
        simp only [Set.indicator_apply, Finset.mem_coe, Finset.mem_range,
          ENat.natCast_lt_natCast]
      rw [TailSumIsFiniteCount]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact ExtendedNatFormula n

/-- Tail-sum formula for any measurable extended-natural random variable,
without a finite-expectation premise. -/
theorem ExpectedWithTopNatEqTailSum (μ : Measure Ω) (T : Ω → WithTop Nat)
    (TimeMeasurable : Measurable T) :
    (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) =
      ∑' t : Nat, μ {ω | (t : WithTop Nat) < T ω} := by
  classical
  let TailIndicator : Nat → Ω → ENNReal := fun t =>
    ({ω | (t : WithTop Nat) < T ω} : Set Ω).indicator 1
  have TailMeasurable : ∀ t : Nat, MeasurableSet {ω | (t : WithTop Nat) < T ω} := by
    intro t
    exact measurableSet_lt measurable_const TimeMeasurable
  have IndicatorMeasurable : ∀ t, Measurable (TailIndicator t) := by
    intro t
    exact measurable_const.indicator (TailMeasurable t)
  have PointwiseTailSum :
      ∀ ω, ENat.toENNReal (T ω) = ∑' t : Nat, TailIndicator t ω := by
    intro ω
    rw [WithTopNatValueEqTailSum]
    apply tsum_congr
    intro t
    simp only [TailIndicator, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  calc
    (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) = ∫⁻ ω, ∑' t : Nat, TailIndicator t ω ∂μ := by
      exact lintegral_congr PointwiseTailSum
    _ = ∑' t : Nat, ∫⁻ ω, TailIndicator t ω ∂μ := by
      exact lintegral_tsum (fun t => (IndicatorMeasurable t).aemeasurable)
    _ = ∑' t : Nat, μ {ω | (t : WithTop Nat) < T ω} := by
      apply tsum_congr
      intro t
      exact lintegral_indicator_one (TailMeasurable t)

/-- Expected first-zero hitting time equals the sum of its tail probabilities;
both sides may be infinite. -/
theorem ExpectedZeroHittingTimeEqTailSum (μ : Measure Ω) (X : Nat → Ω → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) :
    ExpectedZeroHittingTime μ X =
      ∑' t : Nat, μ {ω | (t : WithTop Nat) < ZeroHittingTime X ω} := by
  exact ExpectedWithTopNatEqTailSum μ (ZeroHittingTime X)
    (ZeroHittingTimeMeasurable X CoordinatesMeasurable)

/-- Under absorption, expected zero-hitting time is the sum of the
nonzero-potential probabilities at all natural times. -/
theorem ExpectedZeroHittingTimeEqNonzeroSum (μ : Measure Ω) (X : Nat → Ω → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (Absorbing : ZeroIsAbsorbing μ X) :
    ExpectedZeroHittingTime μ X = ∑' t : Nat, μ {ω | X t ω ≠ 0} := by
  rw [ExpectedZeroHittingTimeEqTailSum μ X CoordinatesMeasurable]
  apply tsum_congr
  intro t
  exact ZeroHittingTimeTailMeasureOfAbsorbing μ X Absorbing t

end

end ECTheoryLib.Probability
