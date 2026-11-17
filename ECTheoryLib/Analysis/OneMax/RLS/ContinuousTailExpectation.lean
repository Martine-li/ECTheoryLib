import ECTheoryLib.Probability.Moments.ContinuousExponentialTailExpectation
import ECTheoryLib.Analysis.OneMax.RLS.TailBounds

/-!
# RLS last-bit expectation from continuous exponential tails

The actual path law supplies a closed tail at every positive real threshold.
Finite mean is established before converting the extended hitting time to a
real integrable variable. The resulting 1+n bound validates the reusable
probability interface; it is not an improvement over existing RLS bounds.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- The actual last-bit runtime has a multiplicative exponential closed tail
at every positive real epsilon. The real-valued representation is related to
the extended hitting time explicitly in the expectation theorem below. -/
theorem LastBitRealRuntimeMultiplicativeTail {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1)
    (ε : ℝ) (PositiveEpsilon : 0 < ε) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | 1 + ε ≤ (FirstHittingTimeValue IsTarget Path).toReal} ≤
      ENNReal.ofReal (Real.exp (-ε / (n : ℝ))) := by
  have Inclusion : {Path : Nat → Bits n |
      1 + ε ≤ (FirstHittingTimeValue IsTarget Path).toReal} ⊆
      {Path | (⌈ε⌉₊ : WithTop Nat) < FirstHittingTime IsTarget Path} := by
    intro Path InEvent
    by_cases Infinite : FirstHittingTime IsTarget Path = ⊤
    · change (⌈ε⌉₊ : WithTop Nat) < FirstHittingTime IsTarget Path
      rw [Infinite]
      exact WithTop.coe_lt_top _
    · obtain ⟨m, TimeEq⟩ := ENat.ne_top_iff_exists.mp Infinite
      change 1 + ε ≤ (FirstHittingTimeValue IsTarget Path).toReal at InEvent
      have RealBound : 1 + ε ≤ (m : ℝ) := by
        simpa only [FirstHittingTimeValue, ← TimeEq, ENat.toENNReal_coe,
          ENNReal.toReal_natCast] using InEvent
      have CeilBound : (⌈ε⌉₊ : ℝ) < (m : ℝ) :=
        (Nat.ceil_lt_add_one PositiveEpsilon.le).trans_le (by linarith)
      change (⌈ε⌉₊ : WithTop Nat) < FirstHittingTime IsTarget Path
      rw [← TimeEq]
      exact WithTop.coe_lt_coe.mpr (by exact_mod_cast CeilBound)
  have Mean : (∫ x, Potential x ∂(PMF.pure InitialState).toMeasure) = 1 := by
    rw [PMF.toMeasure_pure, integral_dirac]
    change (ZeroCount InitialState : ℝ) = 1
    rw [OneZero]
    norm_num
  have Bound := RuntimeTailAtTime PositiveLength (PMF.pure InitialState) ⌈ε⌉₊
  rw [Mean, mul_one] at Bound
  have Exponent : -(⌈ε⌉₊ : ℝ) / (n : ℝ) ≤ -ε / (n : ℝ) :=
    div_le_div_of_nonneg_right (neg_le_neg (Nat.le_ceil ε)) (Nat.cast_nonneg n)
  exact (measure_mono Inclusion).trans
    (Bound.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr Exponent)))

/-- Apply the continuous multiplicative theorem to the actual last-bit RLS law.
The old exponential-tail result supplies only finiteness, so toReal preserves
the extended expectation. The new bound is the non-sharp interface check 1+n. -/
theorem LastBitRuntimeUpperBoundOfContinuousTail {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) :
    ExpectedRuntime PositiveLength InitialState ≤ ENNReal.ofReal (1 + (n : ℝ)) := by
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let Y : (Nat → Bits n) → ENNReal := FirstHittingTimeValue IsTarget
  have YMeasurable : Measurable Y := FirstHittingTimeValueMeasurable IsTarget
  have FiniteMean : (∫⁻ Path, Y Path ∂μ) ≠ ⊤ := by
    have InitialPositive : 0 < ZeroCount InitialState := by rw [OneZero]; decide
    have OldBound := FixedRuntimeUpperBoundOfExponentialTail PositiveLength InitialState InitialPositive
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top OldBound
  have FiniteAlmostEverywhere : ∀ᵐ Path ∂μ, Y Path < ⊤ := ae_lt_top YMeasurable FiniteMean
  have RealIntegrable : Integrable (fun Path => (Y Path).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top YMeasurable.aemeasurable FiniteMean
  have Tail : ∀ ε : ℝ, 0 < ε → μ {Path | (1 + ε) * 1 ≤ (Y Path).toReal} ≤
      ENNReal.ofReal ((1 : ℝ) * Real.exp (-ε / (n : ℝ))) := by
    intro ε PositiveEpsilon
    simpa only [mul_one, one_mul] using
      LastBitRealRuntimeMultiplicativeTail PositiveLength InitialState OneZero ε PositiveEpsilon
  have Bound := ExpectedRealLeOfMultiplicativeExponentialTail μ (fun Path => (Y Path).toReal)
    1 1 (n : ℝ) RealIntegrable (by norm_num) (by norm_num)
    (Nat.cast_pos.mpr PositiveLength) Tail
  rw [integral_toReal YMeasurable.aemeasurable FiniteAlmostEverywhere] at Bound
  change (∫⁻ Path, Y Path ∂μ) ≤ ENNReal.ofReal (1 + (n : ℝ))
  apply (ENNReal.toReal_le_toReal FiniteMean ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  simpa only [mul_one, one_mul] using Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
