import ECTheoryLib.Probability.Moments.ContinuousExponentialTailExpectation
import ECTheoryLib.Analysis.OneMax.RLS.ContinuousTailExpectation
import ECTheoryLib.Analysis.OneMax.RLS.ExponentialLowerTailExpectation

/-!
# RLS last-bit expectation from continuous lower tails

The nonnegative repair of book Corollary 1.6.2(d) is applied to the actual RLS
path law. Finiteness is established before using toReal for lower-tail events
or expectations. The bound is a reuse example, weaker than the known exact mean.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- The actual closed lower tail survives conversion to real runtime. The
null set of infinite paths must be removed because toReal infinity is zero. -/
theorem LastBitRealRuntimeClosedLowerTail {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t : Nat) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | (FirstHittingTimeValue IsTarget Path).toReal ≤ (t : ℝ)} =
        ENNReal.ofReal (1 - (1 - 1 / (n : ℝ)) ^ t) := by
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let Y : (Nat → Bits n) → ENNReal := FirstHittingTimeValue IsTarget
  have FiniteMean : (∫⁻ Path, Y Path ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (LastBitRuntimeUpperBoundOfContinuousTail PositiveLength InitialState OneZero)
  have FiniteAE : ∀ᵐ Path ∂μ, Y Path < ⊤ :=
    ae_lt_top (FirstHittingTimeValueMeasurable IsTarget) FiniteMean
  have EventMeasure : μ {Path | (Y Path).toReal ≤ (t : ℝ)} =
      μ {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop Nat)} := by
    apply measure_congr
    filter_upwards [FiniteAE] with Path Finite
    have TimeFinite : FirstHittingTime IsTarget Path ≠ ⊤ := by
      intro Infinite
      simp only [Y, FirstHittingTimeValue, Infinite] at Finite
      exact lt_irrefl (⊤ : ENNReal) Finite
    obtain ⟨m, TimeEq⟩ := ENat.ne_top_iff_exists.mp TimeFinite
    apply propext
    change (Y Path).toReal ≤ (t : ℝ) ↔ FirstHittingTime IsTarget Path ≤ (t : WithTop Nat)
    simp only [Y, FirstHittingTimeValue, ← TimeEq,
      ENat.toENNReal_coe, ENNReal.toReal_natCast, Nat.cast_le]
    exact WithTop.coe_le_coe.symm
  change μ {Path | (Y Path).toReal ≤ (t : ℝ)} = _
  rw [EventMeasure, ← LastBitRuntimeClosedLowerTail PositiveLength InitialState OneZero t]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- Every real epsilon in (0,1] is controlled, including the closed event at
epsilon=1/2 with positive probability. No integer-epsilon substitution is used. -/
theorem LastBitRealRuntimeMultiplicativeLowerTail {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1)
    (ε : ℝ) (PositiveEpsilon : 0 < ε) (Within : ε ≤ 1) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | (FirstHittingTimeValue IsTarget Path).toReal ≤ (1 - ε) * 2} ≤
        ENNReal.ofReal ((Real.exp 1 / (n : ℝ)) * Real.exp (-ε / 1)) := by
  have Inclusion : {Path : Nat → Bits n |
      (FirstHittingTimeValue IsTarget Path).toReal ≤ (1 - ε) * 2} ⊆
      {Path | (FirstHittingTimeValue IsTarget Path).toReal ≤ (1 : ℝ)} := by
    intro Path InEvent
    by_cases Infinite : FirstHittingTime IsTarget Path = ⊤
    · simp only [Set.mem_ofPred_eq, FirstHittingTimeValue, Infinite]
      change (0 : ℝ) ≤ 1
      norm_num
    · obtain ⟨m, TimeEq⟩ := ENat.ne_top_iff_exists.mp Infinite
      have RealBound : (m : ℝ) < 2 := by
        have := InEvent
        simp only [Set.mem_ofPred_eq, FirstHittingTimeValue, ← TimeEq,
          ENat.toENNReal_coe, ENNReal.toReal_natCast] at this
        linarith
      have NatBound : m ≤ 1 := by
        have : m < 2 := by exact_mod_cast RealBound
        omega
      simpa only [Set.mem_ofPred_eq, FirstHittingTimeValue, ← TimeEq,
        ENat.toENNReal_coe, ENNReal.toReal_natCast, Nat.cast_le_one] using NatBound
  have Mass := LastBitRealRuntimeClosedLowerTail PositiveLength InitialState OneZero 1
  simp only [pow_one, sub_sub_cancel, Nat.cast_one] at Mass
  have Cancel : (Real.exp 1 / (n : ℝ)) * Real.exp (-1) = 1 / (n : ℝ) := by
    calc
      _ = (Real.exp 1 * Real.exp (-1)) / (n : ℝ) := by ring
      _ = 1 / (n : ℝ) := by rw [← Real.exp_add]; norm_num
  calc
    _ ≤ (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
        {Path | (FirstHittingTimeValue IsTarget Path).toReal ≤ (1 : ℝ)} := measure_mono Inclusion
    _ = ENNReal.ofReal (1 / (n : ℝ)) := Mass
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Cancel]
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr (by simpa using neg_le_neg Within)
      · positivity

/-- The repaired continuous lower-tail interface gives a non-sharp RLS bound.
The prior upper bound is used only to justify finite real expectation. -/
theorem LastBitRuntimeLowerBoundOfContinuousTail {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) :
    ENNReal.ofReal (2 - 2 * Real.exp 1 / (n : ℝ)) ≤
      ExpectedRuntime PositiveLength InitialState := by
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let Y : (Nat → Bits n) → ENNReal := FirstHittingTimeValue IsTarget
  have YMeasurable : Measurable Y := FirstHittingTimeValueMeasurable IsTarget
  have FiniteMean : (∫⁻ Path, Y Path ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (LastBitRuntimeUpperBoundOfContinuousTail PositiveLength InitialState OneZero)
  have FiniteAE : ∀ᵐ Path ∂μ, Y Path < ⊤ := ae_lt_top YMeasurable FiniteMean
  have RealIntegrable : Integrable (fun Path => (Y Path).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top YMeasurable.aemeasurable FiniteMean
  have Bound := ExpectedRealGeOfMultiplicativeExponentialLowerTail μ
    (fun Path => (Y Path).toReal) 2 (Real.exp 1 / (n : ℝ)) 1 RealIntegrable
    (ae_of_all _ (fun _ => ENNReal.toReal_nonneg)) (by norm_num)
    (div_pos (Real.exp_pos _) (Nat.cast_pos.mpr PositiveLength)) (by norm_num)
    (LastBitRealRuntimeMultiplicativeLowerTail PositiveLength InitialState OneZero)
  rw [integral_toReal YMeasurable.aemeasurable FiniteAE] at Bound
  change ENNReal.ofReal (2 - 2 * Real.exp 1 / (n : ℝ)) ≤ ∫⁻ Path, Y Path ∂μ
  apply (ENNReal.ofReal_le_iff_le_toReal FiniteMean).mpr
  convert Bound using 1
  ring

end
end ECTheoryLib.Analysis.RLSOnOneMax

