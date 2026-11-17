import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integrable stopped-level multiplicative tails

The original process has a positive gap away from zero but need not have a
finite or bounded range, and may leave zero after its first visit. Each stopped
coordinate is integrable. Drift is conditioned on the sigma algebra generated
by that stopped coordinate, including its zero level. These sigma algebras are
not assumed to form a filtration. In particular, the drift hypothesis is not
silently strengthened to a full-history hypothesis.

The first theorem allows arbitrary initialization and every real drift
coefficient. The second specializes it to the usual positive fixed initial
value and natural-ceiling strict hitting-time tail.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A strict first-zero tail under integrable stopped-current-level drift.
There is no finite-range, raw absorption, or fixed-initial-value hypothesis. -/
theorem MultiplicativeDriftTailAtTimeOfIntegrableStoppedLevel
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (smin Delta : ℝ)
    (Coordinates : ∀ t, Measurable (X t))
    (MinimumPositive : 0 < smin)
    (ValueGap : ∀ t ω, X t ω = 0 ∨ smin ≤ X t ω)
    (StoppedIntegrable : ∀ t,
      Integrable (StopAtFirstHit (fun x : ℝ => x ≤ 0) X t) μ)
    (StoppedLevelDrift : ∀ t,
      (fun ω => Delta * StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω) ≤ᵐ[μ]
        μ[fun ω => StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω -
          StopAtFirstHit (fun x : ℝ => x ≤ 0) X (t + 1) ω |
          MeasurableSpace.comap
            (StopAtFirstHit (fun x : ℝ => x ≤ 0) X t) (borel ℝ)])
    (t : ℕ) :
    μ {ω | (t : WithTop ℕ) < ZeroHittingTime X ω} ≤
      ENNReal.ofReal
        (Real.exp (-Delta * (t : ℝ)) * ExpectedValue μ (X 0) / smin) := by
  have Pointwise : ∀ j ω, 0 ≤ X j ω := by
    intro j ω
    rcases ValueGap j ω with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  let Y := StopAtFirstHit (fun x : ℝ => x ≤ 0) X
  -- The top filtration is used only for stopped-coordinate measurability.
  -- No drift bound conditional on it is assumed or inferred.
  have AdaptedX : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) X := by
    intro j
    change Measurable (X j)
    exact Coordinates j
  have AdaptedY : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) Y :=
    StopAtFirstHitAdapted X _ AdaptedX _ measurableSet_Iic
  have YMeasurable : ∀ j, Measurable (Y j) := fun _ => AdaptedY.measurable
  have YNonnegative : ∀ j ω, 0 ≤ Y j ω :=
    StopAtNonpositiveNonnegative X Pointwise
  have YGap : ∀ j ω, Y j ω = 0 ∨ smin ≤ Y j ω :=
    StopAtFirstHitValues _ X {s : ℝ | s = 0 ∨ smin ≤ s} ValueGap
  let Mean : ℕ → ℝ := fun j => ∫ ω, Y j ω ∂μ
  have MeanNonnegative : ∀ j, 0 ≤ Mean j :=
    fun j => integral_nonneg (YNonnegative j)
  have OneStep : ∀ j, Mean (j + 1) ≤ Real.exp (-Delta) * Mean j := by
    intro j
    let G : MeasurableSpace Ω := MeasurableSpace.comap (Y j) (borel ℝ)
    have GLe := (YMeasurable j).comap_le
    have MeanDrift : Delta * Mean j ≤ Mean j - Mean (j + 1) := by
      calc
        Delta * Mean j = ∫ ω, Delta * Y j ω ∂μ := (integral_const_mul _ _).symm
        _ ≤ ∫ ω, (μ[fun u => Y j u - Y (j + 1) u | G]) ω ∂μ :=
          integral_mono_ae ((StoppedIntegrable j).const_mul Delta)
            integrable_condExp (StoppedLevelDrift j)
        _ = ∫ ω, Y j ω - Y (j + 1) ω ∂μ := integral_condExp GLe
        _ = Mean j - Mean (j + 1) :=
          integral_sub (StoppedIntegrable j) (StoppedIntegrable (j + 1))
    have Linear : Mean (j + 1) ≤ (1 - Delta) * Mean j := by linarith
    have ExponentialFactor : 1 - Delta ≤ Real.exp (-Delta) := by
      have Bound := Real.add_one_le_exp (-Delta)
      linarith
    exact Linear.trans
      (mul_le_mul_of_nonneg_right ExponentialFactor (MeanNonnegative j))
  have InitialMean : Mean 0 = ExpectedValue μ (X 0) := by
    change (∫ ω, Y 0 ω ∂μ) = ∫ ω, X 0 ω ∂μ
    exact integral_congr_ae (ae_of_all _ (StopAtFirstHitInitial _ X))
  have Decay : Mean t ≤ Real.exp (-Delta * (t : ℝ)) * ExpectedValue μ (X 0) := by
    have Bound := le_geom (u := Mean) (Real.exp_nonneg (-Delta)) t
      (fun j _ => OneStep j)
    have Factor : Real.exp (-Delta) ^ t = Real.exp (-Delta * (t : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rwa [Factor, InitialMean] at Bound
  have MarkovBound : μ {ω | Y t ω ≠ 0} ≤ ENNReal.ofReal (Mean t / smin) := by
    have Bound := ((StoppedIntegrable t).div_const smin).measure_le_integral
      (ae_of_all _ (fun ω => div_nonneg (YNonnegative t ω) MinimumPositive.le))
      (s := {ω | Y t ω ≠ 0}) (by
        intro ω Nonzero
        apply (le_div_iff₀ MinimumPositive).mpr
        rw [one_mul]
        exact (YGap t ω).resolve_left Nonzero)
    rw [integral_div] at Bound
    exact Bound
  have Times : ZeroHittingTime Y = ZeroHittingTime X :=
    funext (StopAtNonpositiveZeroTime X Pointwise)
  rw [← Times, ZeroHittingTimeTailMeasureOfAbsorbing μ Y
    (StopAtNonpositiveZeroAbsorbing μ X Pointwise) t]
  exact MarkovBound.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right Decay MinimumPositive.le))

/-- The natural-ceiling exponential tail for a fixed positive initial value.
The original process can be nonabsorbing and have an unbounded range. -/
theorem MultiplicativeDriftUpperTailOfIntegrableStoppedLevel
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (smin Delta : ℝ)
    (Coordinates : ∀ t, Measurable (X t))
    (MinimumPositive : 0 < smin)
    (ValueGap : ∀ t ω, X t ω = 0 ∨ smin ≤ X t ω)
    (StoppedIntegrable : ∀ t,
      Integrable (StopAtFirstHit (fun x : ℝ => x ≤ 0) X t) μ)
    (StoppedLevelDrift : ∀ t,
      (fun ω => Delta * StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω) ≤ᵐ[μ]
        μ[fun ω => StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω -
          StopAtFirstHit (fun x : ℝ => x ≤ 0) X (t + 1) ω |
          MeasurableSpace.comap
            (StopAtFirstHit (fun x : ℝ => x ≤ 0) X t) (borel ℝ)])
    (s0 : ℝ) (PositiveDelta : 0 < Delta)
    (InitialFixed : ∀ᵐ ω ∂μ, X 0 ω = s0) (InitialPositive : 0 < s0)
    (r : ℝ) (_NonnegativeR : 0 ≤ r) :
    μ {ω | (⌈(r + Real.log (s0 / smin)) / Delta⌉₊ : WithTop ℕ) <
      ZeroHittingTime X ω} ≤ ENNReal.ofReal (Real.exp (-r)) := by
  let t : ℕ := ⌈(r + Real.log (s0 / smin)) / Delta⌉₊
  have InitialMean : ExpectedValue μ (X 0) = s0 := by
    unfold ExpectedValue
    rw [integral_congr_ae InitialFixed, integral_const, probReal_univ, one_smul]
  have TailBound := MultiplicativeDriftTailAtTimeOfIntegrableStoppedLevel μ X smin Delta
    Coordinates MinimumPositive ValueGap StoppedIntegrable StoppedLevelDrift t
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
