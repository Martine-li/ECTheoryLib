import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ECTheoryLib.Probability

open MeasureTheory

noncomputable section

/-- The positive part of a real variable with integral positive values has the
natural closed-tail sum. Negative values may be arbitrary real numbers, and
the positive-part expectation may be infinite. -/
theorem PositivePartLIntegralEqNatUpperTailSum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (XMeasurable : Measurable X)
    (IntegerPositiveValues : ∀ᵐ ω ∂μ, X ω ≤ 0 ∨ ∃ n : Nat, X ω = (n : ℝ)) :
    (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) =
      ∑' n : Nat, μ {ω | ((n + 1 : Nat) : ℝ) ≤ X ω} := by
  let T : Ω → WithTop Nat := fun ω => (⌊X ω⌋₊ : WithTop Nat)
  have TMeasurable : Measurable T :=
    (measurable_of_countable (fun n : Nat => (n : WithTop Nat))).comp XMeasurable.nat_floor
  have PositivePart : ∀ᵐ ω ∂μ, ENat.toENNReal (T ω) = ENNReal.ofReal (X ω) := by
    filter_upwards [IntegerPositiveValues] with ω Values
    change ENat.toENNReal (⌊X ω⌋₊ : ENat) = ENNReal.ofReal (X ω)
    rcases Values with Nonpositive | ⟨n, Equal⟩
    · rw [Nat.floor_of_nonpos Nonpositive, ENat.toENNReal_coe]
      simp only [Nat.cast_zero, ENNReal.ofReal_of_nonpos Nonpositive]
    · simp only [Equal, Nat.floor_natCast, ENat.toENNReal_coe, ENNReal.ofReal_natCast]
  calc
    _ = ∫⁻ ω, ENat.toENNReal (T ω) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [PositivePart] with ω Equal
      exact Equal.symm
    _ = ∑' n : Nat, μ {ω | (n : WithTop Nat) < T ω} :=
      ExpectedWithTopNatEqTailSum μ T TMeasurable
    _ = _ := by
      apply tsum_congr
      intro n
      congr 1
      ext ω
      change (n : ENat) < (⌊X ω⌋₊ : ENat) ↔ ((n + 1 : Nat) : ℝ) ≤ X ω
      rw [ENat.natCast_lt_natCast, Nat.lt_iff_add_one_le, Nat.le_floor_iff' (Nat.add_one_ne_zero n)]

/-- Integrability makes the real upper-tail series summable, with sum equal to
the positive-part expectation. Finiteness is proved before conversion toReal. -/
theorem PositivePartHasSumNatUpperTail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (XMeasurable : Measurable X) (XIntegrable : Integrable X μ)
    (IntegerPositiveValues : ∀ᵐ ω ∂μ, X ω ≤ 0 ∨ ∃ n : Nat, X ω = (n : ℝ)) :
    HasSum (fun n : Nat => μ.real {ω | ((n + 1 : Nat) : ℝ) ≤ X ω})
      (∫ ω, max (X ω) 0 ∂μ) := by
  have PositiveMean : 0 ≤ ∫ ω, max (X ω) 0 ∂μ :=
    integral_nonneg (fun ω => le_max_right (X ω) 0)
  have ExtendedSum : ENNReal.ofReal (∫ ω, max (X ω) 0 ∂μ) =
      ∑' n : Nat, μ {ω | ((n + 1 : Nat) : ℝ) ≤ X ω} := by
    rw [ofReal_integral_eq_lintegral_ofReal XIntegrable.pos_part
      (ae_of_all _ (fun ω => le_max_right (X ω) 0))]
    simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le] using
      PositivePartLIntegralEqNatUpperTailSum μ X XMeasurable IntegerPositiveValues
  have FiniteSum : (∑' n : Nat, μ {ω | ((n + 1 : Nat) : ℝ) ≤ X ω}) ≠ ⊤ := by
    rw [← ExtendedSum]
    exact ENNReal.ofReal_ne_top
  have Sum := ENNReal.hasSum_toReal FiniteSum
  rw [← ENNReal.tsum_toReal_eq (fun n => ENNReal.ne_top_of_tsum_ne_top FiniteSum n),
    ← ExtendedSum, ENNReal.toReal_ofReal PositiveMean] at Sum
  exact Sum

/-- Book Lemma 1.6.1's signed extension: arbitrary nonpositive real values are
allowed. The upper bound uses the genuinely summable real series of closed
positive-integer tails, not a totalized divergent real tsum. -/
theorem ExpectedRealLeNatUpperTailSum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (XMeasurable : Measurable X) (XIntegrable : Integrable X μ)
    (IntegerPositiveValues : ∀ᵐ ω ∂μ, X ω ≤ 0 ∨ ∃ n : Nat, X ω = (n : ℝ)) :
    (∫ ω, X ω ∂μ) ≤ ∑' n : Nat, μ.real {ω | ((n + 1 : Nat) : ℝ) ≤ X ω} := by
  rw [(PositivePartHasSumNatUpperTail μ X XMeasurable XIntegrable IntegerPositiveValues).tsum_eq]
  exact integral_mono XIntegrable XIntegrable.pos_part (fun ω => le_max_left (X ω) 0)

end
end ECTheoryLib.Probability

