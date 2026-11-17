import ECTheoryLib.Tools.Drift.FiniteState
import ECTheoryLib.Probability.Processes.FiniteStateBounds
import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Multiplicative drift upper tails

Source: Johannes Lengler, *Drift Analysis*, Theorem 2.4.5, pp. 116-117,
in Doerr and Neumann (eds.), *Theory of Evolutionary Computation* (2020).
https://doi.org/10.1007/978-3-030-29414-4_2

The scalar process has a pointwise finite nonnegative range and an explicitly
absorbing zero. Drift is conditioned only on positive-probability current-value
events; no Markov, historical drift, or bounded-jump assumption is added.
The fixed-time bound also allows random initialization with mass at zero.
Markov's inequality is reused from mathlib, after scaling by the positive gap.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Average the level-dependent multiplicative drift over the current finite
partition. Null levels contribute zero, and absorption handles the zero level. -/
theorem MultiplicativeExpectedDecrease (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta * s ≤ StateDrift μ X t s)
    (t : Nat) :
    Delta * ExpectedValue μ (X t) ≤
      ExpectedValue μ (X t) - ExpectedValue μ (X (t + 1)) := by
  classical
  have CurrentIntegrable : Integrable (X t) μ :=
    FiniteStateIntegrable μ (X t) S (CoordinatesMeasurable t)
      (Filter.Eventually.of_forall (ValuesInS t))
  have NextIntegrable : Integrable (X (t + 1)) μ :=
    FiniteStateIntegrable μ (X (t + 1)) S (CoordinatesMeasurable (t + 1))
      (Filter.Eventually.of_forall (ValuesInS (t + 1)))
  have EachContribution : ∀ s ∈ S,
      (∫ ω in StateEvent X t s, Delta * X t ω ∂μ) ≤
        ∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ := by
    intro s InS
    have EventMeasurable : MeasurableSet (StateEvent X t s) :=
      StateEventMeasurable X t s (CoordinatesMeasurable t)
    have CurrentConstant :
        (∫ ω in StateEvent X t s, Delta * X t ω ∂μ) =
          Delta * s * (μ (StateEvent X t s)).toReal := by
      have OnEvent : Set.EqOn (fun ω => Delta * X t ω)
          (fun _ => Delta * s) (StateEvent X t s) := by
        intro ω InEvent
        have CurrentValue : X t ω = s := InEvent
        change Delta * X t ω = Delta * s
        rw [CurrentValue]
      rw [setIntegral_congr_fun EventMeasurable OnEvent, setIntegral_const,
        measureReal_def, smul_eq_mul, mul_comm]
    rw [CurrentConstant]
    by_cases StateZero : s = 0
    · rw [StateZero, mul_zero, zero_mul,
        ZeroStateDecreaseIntegral μ X t (CoordinatesMeasurable t) ZeroAbsorbing]
    · by_cases EventNull : μ (StateEvent X t s) = 0
      · rw [EventNull, ENNReal.toReal_zero, mul_zero,
          Measure.restrict_eq_zero.mpr EventNull, integral_zero_measure]
      · have ProbabilityPositive : 0 < (μ (StateEvent X t s)).toReal :=
          ENNReal.toReal_pos EventNull (measure_ne_top μ _)
        have ConditionalBound : Delta * s ≤
            (∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ) /
              (μ (StateEvent X t s)).toReal :=
          StateDriftLowerBound t s InS StateZero (bot_lt_iff_ne_bot.mpr EventNull)
        exact (le_div_iff₀ ProbabilityPositive).mp ConditionalBound
  unfold ExpectedValue
  rw [← integral_const_mul, ← integral_sub CurrentIntegrable NextIntegrable]
  rw [FiniteStateIntegralPartition μ X t S _ (CoordinatesMeasurable t)
    (ValuesInS t) (CurrentIntegrable.const_mul Delta)]
  rw [FiniteStateIntegralPartition μ X t S (fun ω => X t ω - X (t + 1) ω)
    (CoordinatesMeasurable t)
    (ValuesInS t) (CurrentIntegrable.sub NextIntegrable)]
  exact Finset.sum_le_sum EachContribution

/-- Exponential mean bound under multiplicative drift, giving contraction when
`Delta > 0`. The positive factor `exp (-Delta)` avoids an artificial `Delta ≤ 1`
hypothesis and makes the intermediate estimate valid for every real coefficient. -/
theorem MultiplicativeExpectedValueDecay (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (StatesNonnegative : ∀ s ∈ S, 0 ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta * s ≤ StateDrift μ X t s)
    (t : Nat) :
    ExpectedValue μ (X t) ≤ Real.exp (-Delta * (t : ℝ)) * ExpectedValue μ (X 0) := by
  have OneStep : ∀ j, ExpectedValue μ (X (j + 1)) ≤
      Real.exp (-Delta) * ExpectedValue μ (X j) := by
    intro j
    have MeanNonnegative : 0 ≤ ExpectedValue μ (X j) :=
      FiniteStateExpectedValueNonneg μ (X j) S StatesNonnegative (ValuesInS j)
    have Decrease := MultiplicativeExpectedDecrease μ X S Delta
      CoordinatesMeasurable ValuesInS ZeroAbsorbing StateDriftLowerBound j
    have LinearContraction : ExpectedValue μ (X (j + 1)) ≤
        (1 - Delta) * ExpectedValue μ (X j) := by linarith
    have ExponentialFactor : 1 - Delta ≤ Real.exp (-Delta) := by
      have Bound := Real.add_one_le_exp (-Delta)
      linarith
    exact LinearContraction.trans
      (mul_le_mul_of_nonneg_right ExponentialFactor MeanNonnegative)
  have Bound := le_geom (u := fun j => ExpectedValue μ (X j))
    (Real.exp_nonneg (-Delta)) t (fun j _ => OneStep j)
  have Factor : Real.exp (-Delta) ^ t = Real.exp (-Delta * (t : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [Factor] at Bound

/-- The strict hitting-time tail at every natural time, with arbitrary random
initialization. Infinite hitting times remain in the event being bounded. -/
theorem MultiplicativeDriftTailAtTime (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (smin Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta * s ≤ StateDrift μ X t s)
    (t : Nat) :
    μ {ω | (t : WithTop Nat) < ZeroHittingTime X ω} ≤
      ENNReal.ofReal (Real.exp (-Delta * (t : ℝ)) * ExpectedValue μ (X 0) / smin) := by
  have StatesNonnegative : ∀ s ∈ S, 0 ≤ s := by
    intro s InS
    rcases StateLowerBound s InS with IsZero | AboveMinimum
    · rw [IsZero]
    · exact MinimumPositive.le.trans AboveMinimum
  have CurrentIntegrable : Integrable (X t) μ :=
    FiniteStateIntegrable μ (X t) S (CoordinatesMeasurable t)
      (Filter.Eventually.of_forall (ValuesInS t))
  have ScaledNonnegative : ∀ᵐ ω ∂μ, 0 ≤ X t ω / smin := by
    apply Filter.Eventually.of_forall
    intro ω
    exact div_nonneg (StatesNonnegative _ (ValuesInS t ω)) MinimumPositive.le
  have MarkovBound : μ {ω | X t ω ≠ 0} ≤
      ENNReal.ofReal (ExpectedValue μ (X t) / smin) := by
    have Bound := (CurrentIntegrable.div_const smin).measure_le_integral
      ScaledNonnegative (s := {ω | X t ω ≠ 0}) (by
        intro ω Nonzero
        apply (le_div_iff₀ MinimumPositive).mpr
        rw [one_mul]
        exact (StateLowerBound _ (ValuesInS t ω)).resolve_left Nonzero)
    rw [integral_div] at Bound
    exact Bound
  rw [ZeroHittingTimeTailMeasureOfAbsorbing μ X ZeroAbsorbing t]
  apply MarkovBound.trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ MinimumPositive.le
  exact MultiplicativeExpectedValueDecay μ X S Delta CoordinatesMeasurable
    StatesNonnegative ValuesInS ZeroAbsorbing StateDriftLowerBound t

/-- Lengler's Theorem 2.4.5 with the source proof's zero-absorption convention
explicit. The initial state is fixed almost surely, and time counts transitions
starting from time zero. The natural ceiling agrees with the ordinary ceiling
on the nonnegative threshold furnished by an attainable positive initial state. -/
theorem MultiplicativeDriftUpperTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (smin Delta s0 : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (_ZeroInS : 0 ∈ S)
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (PositiveDelta : 0 < Delta)
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta * s ≤ StateDrift μ X t s)
    (InitialFixed : ∀ᵐ ω ∂μ, X 0 ω = s0)
    (InitialPositive : 0 < s0)
    (r : ℝ) (_NonnegativeR : 0 ≤ r) :
    μ {ω | (⌈(r + Real.log (s0 / smin)) / Delta⌉₊ : WithTop Nat) <
      ZeroHittingTime X ω} ≤ ENNReal.ofReal (Real.exp (-r)) := by
  let t : Nat := ⌈(r + Real.log (s0 / smin)) / Delta⌉₊
  have InitialMean : ExpectedValue μ (X 0) = s0 := by
    unfold ExpectedValue
    rw [integral_congr_ae InitialFixed, integral_const, probReal_univ, one_smul]
  have TailBound := MultiplicativeDriftTailAtTime μ X S smin Delta
    CoordinatesMeasurable MinimumPositive StateLowerBound ValuesInS ZeroAbsorbing
    StateDriftLowerBound t
  rw [InitialMean] at TailBound
  have CeilingBound : (r + Real.log (s0 / smin)) / Delta ≤ (t : ℝ) :=
    Nat.le_ceil _
  have ExponentBound : -Delta * (t : ℝ) + Real.log (s0 / smin) ≤ -r := by
    have TimeBound := (div_le_iff₀ PositiveDelta).mp CeilingBound
    linarith
  have RatioPositive : 0 < s0 / smin := div_pos InitialPositive MinimumPositive
  have RealBound : Real.exp (-Delta * (t : ℝ)) * s0 / smin ≤ Real.exp (-r) := by
    calc
      Real.exp (-Delta * (t : ℝ)) * s0 / smin =
          Real.exp (-Delta * (t : ℝ)) * (s0 / smin) := by ring
      _ = Real.exp (-Delta * (t : ℝ) + Real.log (s0 / smin)) := by
        rw [Real.exp_add, Real.exp_log RatioPositive]
      _ ≤ Real.exp (-r) := Real.exp_le_exp.mpr ExponentBound
  exact TailBound.trans (ENNReal.ofReal_le_ofReal RealBound)

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Retain the discrete contraction factor instead of replacing it by an
exponential. The nonnegative factor requires delta at most one. -/
theorem MultiplicativeExpectedGeometricDecay (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (δ : ℝ) (DeltaAtMostOne : δ≤1)
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω∈S)
    (Absorbing : ZeroIsAbsorbing μ X)
    (Drift : ∀ t s, s∈S → s≠0 → 0<μ (StateEvent X t s) → δ*s≤StateDrift μ X t s)
    (t : ℕ) : ExpectedValue μ (X t)≤(1-δ)^t*ExpectedValue μ (X 0) := by
  apply le_geom (u := fun j => ExpectedValue μ (X j)) (c := 1 - δ)
    (sub_nonneg.mpr DeltaAtMostOne) t
  intro j _
  have Decrease := MultiplicativeExpectedDecrease μ X S δ
    CoordinatesMeasurable Values Absorbing Drift j
  linarith

/-- A geometric-factor hitting tail, including delta=1 and t=0. -/
theorem MultiplicativeDriftGeometricTailAtTime (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin δ : ℝ) (DeltaAtMostOne : δ≤1)
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) (MinimumPositive : 0<smin)
    (StateLower : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ t ω, X t ω∈S)
    (Absorbing : ZeroIsAbsorbing μ X)
    (Drift : ∀ t s, s∈S → s≠0 → 0<μ (StateEvent X t s) → δ*s≤StateDrift μ X t s)
    (t : ℕ) : μ {ω | (t : WithTop ℕ)<ZeroHittingTime X ω}≤
      ENNReal.ofReal ((1-δ)^t*ExpectedValue μ (X 0)/smin) := by
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases StateLower s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have IntegrableX : Integrable (X t) μ :=
    FiniteStateIntegrable μ (X t) S (CoordinatesMeasurable t) (ae_of_all _ (Values t))
  have Markov := (IntegrableX.div_const smin).measure_le_integral
    (ae_of_all _ (fun ω => div_nonneg (Nonnegative _ (Values t ω)) MinimumPositive.le))
    (s := {ω | X t ω≠0}) (by
      intro ω Active
      apply (le_div_iff₀ MinimumPositive).mpr
      rw [one_mul]
      exact (StateLower _ (Values t ω)).resolve_left Active)
  rw [integral_div] at Markov
  rw [ZeroHittingTimeTailMeasureOfAbsorbing μ X Absorbing t]
  apply Markov.trans
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right
    (MultiplicativeExpectedGeometricDecay μ X S δ DeltaAtMostOne CoordinatesMeasurable Values Absorbing Drift t)
    MinimumPositive.le

end
end ECTheoryLib.Tools.Drift
