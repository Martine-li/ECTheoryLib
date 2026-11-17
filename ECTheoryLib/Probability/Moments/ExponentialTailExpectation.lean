import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential integer tails and expected values

An integer center and positive integer offsets are explicit. The extended-natural
result permits infinite values and assumes no finite expectation in advance.
The signed integer corollary retains arbitrary negative values and the source's
finite real-expectation convention. This is the upper additive branch of
Corollary 1.6.2(a), with the center explicitly typed as a natural number; it does
not assert any of the other branches of that numbered source item.
-/

namespace ECTheoryLib.Probability

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Positive-offset closed exponential tails give the precise geometric-series
upper bound for an extended-natural expectation, without a finiteness premise. -/
theorem ExpectedWithTopNatLeGeometricOfExponentialTail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Ω → WithTop Nat) (B : Nat) (α β : ℝ)
    (TimeMeasurable : Measurable τ)
    (PositiveAlpha : 0 < α) (PositiveBeta : 0 < β)
    (Tail : ∀ offset : Nat, 0 < offset →
      μ {ω | ((B + offset : Nat) : WithTop Nat) ≤ τ ω} ≤
        ENNReal.ofReal (α * Real.exp (-(offset : ℝ) / β))) :
    (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) ≤
      ENNReal.ofReal ((B : ℝ) + α / (Real.exp (1 / β) - 1)) := by
  classical
  let q : ℝ := Real.exp (-(1 / β))
  have PositiveReciprocal : 0 < 1 / β := one_div_pos.mpr PositiveBeta
  have PositiveQ : 0 < q := Real.exp_pos _
  have QLtOne : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith
  have PositiveDenominator : 0 < Real.exp (1 / β) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr PositiveReciprocal)
  have QExp : q * Real.exp (1 / β) = 1 := by
    dsimp [q]
    rw [Real.exp_neg]
    exact inv_mul_cancel₀ (ne_of_gt (Real.exp_pos _))
  have GeometricRatio :
      α * q / (1 - q) = α / (Real.exp (1 / β) - 1) := by
    apply (div_eq_div_iff (ne_of_gt (sub_pos.mpr QLtOne))
      (ne_of_gt PositiveDenominator)).mpr
    calc
      α * q * (Real.exp (1 / β) - 1) =
          α * (q * Real.exp (1 / β) - q) := by ring
      _ = α * (1 - q) := by rw [QExp]
  have GeometricSum : HasSum (fun j : Nat => (α * q) * q ^ j)
      (α * q / (1 - q)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one PositiveQ.le QLtOne).mul_left (α * q)
  have GeometricTerm (j : Nat) :
      α * Real.exp (-((j + 1 : Nat) : ℝ) / β) = (α * q) * q ^ j := by
    have Exponent : -((j + 1 : Nat) : ℝ) / β =
        ((j + 1 : Nat) : ℝ) * (-(1 / β)) := by ring
    rw [Exponent, Real.exp_nat_mul]
    change α * q ^ (j + 1) = (α * q) * q ^ j
    rw [pow_succ]
    ring
  have TailSeries :
      (∑' j : Nat, ENNReal.ofReal
        (α * Real.exp (-((j + 1 : Nat) : ℝ) / β))) =
      ENNReal.ofReal (α / (Real.exp (1 / β) - 1)) := by
    calc
      _ = ∑' j : Nat, ENNReal.ofReal ((α * q) * q ^ j) := by
        apply tsum_congr
        intro j
        rw [GeometricTerm j]
      _ = ENNReal.ofReal (∑' j : Nat, (α * q) * q ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (mul_nonneg PositiveAlpha.le PositiveQ.le)
            (pow_nonneg PositiveQ.le j)) GeometricSum.summable).symm
      _ = ENNReal.ofReal (α * q / (1 - q)) := by rw [GeometricSum.tsum_eq]
      _ = ENNReal.ofReal (α / (Real.exp (1 / β) - 1)) := by rw [GeometricRatio]
  let TailMass : Nat → ENNReal := fun t => μ {ω | (t : WithTop Nat) < τ ω}
  have Split :
      (∑ t ∈ Finset.range B, TailMass t) + (∑' j : Nat, TailMass (j + B)) =
        ∑' t : Nat, TailMass t :=
    (ENNReal.summable : Summable (fun j : Nat => TailMass (j + B))).sum_add_tsum_nat_add'
  have PrefixBound : (∑ t ∈ Finset.range B, TailMass t) ≤ (B : ENNReal) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range B, (1 : ENNReal) :=
        Finset.sum_le_sum (fun _t _Member => prob_le_one)
      _ = (B : ENNReal) := by simp
  have ShiftedTail (j : Nat) : TailMass (j + B) ≤
      ENNReal.ofReal (α * Real.exp (-((j + 1 : Nat) : ℝ) / β)) := by
    have Event :
        {ω | ((j + B : Nat) : WithTop Nat) < τ ω} =
          {ω | ((B + (j + 1) : Nat) : WithTop Nat) ≤ τ ω} := by
      ext ω
      have Index : B + (j + 1) = (j + B) + 1 := by omega
      rw [Index]
      change ((j + B : Nat) : ENat) < τ ω ↔
        (((j + B) + 1 : Nat) : ENat) ≤ τ ω
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENat.natCast_add_one_le_iff (m := j + B) (n := τ ω)).symm
    dsimp [TailMass]
    rw [Event]
    exact Tail (j + 1) (Nat.succ_pos j)
  calc
    (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) = ∑' t : Nat, TailMass t :=
      ExpectedWithTopNatEqTailSum μ τ TimeMeasurable
    _ = (∑ t ∈ Finset.range B, TailMass t) + (∑' j : Nat, TailMass (j + B)) :=
      Split.symm
    _ ≤ (B : ENNReal) + ∑' j : Nat,
        ENNReal.ofReal (α * Real.exp (-((j + 1 : Nat) : ℝ) / β)) :=
      add_le_add PrefixBound (ENNReal.tsum_le_tsum ShiftedTail)
    _ = (B : ENNReal) + ENNReal.ofReal (α / (Real.exp (1 / β) - 1)) := by
      rw [TailSeries]
    _ = ENNReal.ofReal ((B : ℝ) + α / (Real.exp (1 / β) - 1)) := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg B)
        (div_nonneg PositiveAlpha.le PositiveDenominator.le), ENNReal.ofReal_natCast]

/-- The source's simpler additive upper bound follows from the exact geometric
constant and `exp x ≥ 1 + x`; the runtime may initially take the value infinity. -/
theorem ExpectedWithTopNatLeOfExponentialTail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Ω → WithTop Nat) (B : Nat) (α β : ℝ)
    (TimeMeasurable : Measurable τ)
    (PositiveAlpha : 0 < α) (PositiveBeta : 0 < β)
    (Tail : ∀ offset : Nat, 0 < offset →
      μ {ω | ((B + offset : Nat) : WithTop Nat) ≤ τ ω} ≤
        ENNReal.ofReal (α * Real.exp (-(offset : ℝ) / β))) :
    (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) ≤ ENNReal.ofReal ((B : ℝ) + α * β) := by
  have PositiveDenominator : 0 < Real.exp (1 / β) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (one_div_pos.mpr PositiveBeta))
  have ExpBound : 1 / β ≤ Real.exp (1 / β) - 1 := by
    linarith [Real.add_one_le_exp (1 / β)]
  have ProductBound : 1 ≤ β * (Real.exp (1 / β) - 1) := by
    have Bound := mul_le_mul_of_nonneg_left ExpBound PositiveBeta.le
    have Cancel : β * (1 / β) = 1 := by
      simp only [one_div, mul_inv_cancel₀ (ne_of_gt PositiveBeta)]
    rwa [Cancel] at Bound
  have ReciprocalBound : 1 / (Real.exp (1 / β) - 1) ≤ β :=
    (div_le_iff₀ PositiveDenominator).mpr ProductBound
  have CoefficientBound : α / (Real.exp (1 / β) - 1) ≤ α * β := by
    calc
      _ = α * (1 / (Real.exp (1 / β) - 1)) := by ring
      _ ≤ α * β := mul_le_mul_of_nonneg_left ReciprocalBound PositiveAlpha.le
  exact (ExpectedWithTopNatLeGeometricOfExponentialTail μ τ B α β
    TimeMeasurable PositiveAlpha PositiveBeta Tail).trans
      (ENNReal.ofReal_le_ofReal (add_le_add (le_refl (B : ℝ)) CoefficientBound))

/-- The signed integer upper branch: arbitrary negative values are retained.
Only the positive part is passed to the extended-natural tail-sum theorem. -/
theorem ExpectedIntLeOfExponentialTail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Int) (B : Nat) (α β : ℝ)
    (XMeasurable : Measurable X)
    (XIntegrable : Integrable (fun ω => (X ω : ℝ)) μ)
    (PositiveAlpha : 0 < α) (PositiveBeta : 0 < β)
    (Tail : ∀ offset : Nat, 0 < offset →
      μ {ω | ((B + offset : Nat) : Int) ≤ X ω} ≤
        ENNReal.ofReal (α * Real.exp (-(offset : ℝ) / β))) :
    (∫ ω, (X ω : ℝ) ∂μ) ≤ (B : ℝ) + α * β := by
  let τ : Ω → WithTop Nat := fun ω => ((X ω).toNat : WithTop Nat)
  have TimeMeasurable : Measurable τ :=
    (measurable_of_countable (fun z : Int => (z.toNat : WithTop Nat))).comp XMeasurable
  have PositivePart (ω : Ω) : ((X ω).toNat : ℝ) = max (X ω : ℝ) 0 := by
    have Cast := congrArg (fun z : Int => (z : ℝ)) (Int.toNat_eq_max (X ω))
    simpa only [Int.cast_natCast, Int.cast_max, Int.cast_zero] using Cast
  have PositivePartIntegrable : Integrable (fun ω => ((X ω).toNat : ℝ)) μ :=
    XIntegrable.pos_part.congr (ae_of_all μ (fun ω => (PositivePart ω).symm))
  have PositivePartNonnegative : 0 ≤ᵐ[μ] (fun ω => ((X ω).toNat : ℝ)) :=
    ae_of_all μ (fun ω => Nat.cast_nonneg (X ω).toNat)
  have PositivePartTail : ∀ offset : Nat, 0 < offset →
      μ {ω | ((B + offset : Nat) : WithTop Nat) ≤ τ ω} ≤
        ENNReal.ofReal (α * Real.exp (-(offset : ℝ) / β)) := by
    intro offset PositiveLambda
    have Event :
        {ω | ((B + offset : Nat) : WithTop Nat) ≤ τ ω} =
          {ω | ((B + offset : Nat) : Int) ≤ X ω} := by
      ext ω
      change ((B + offset : Nat) : ENat) ≤ ((X ω).toNat : ENat) ↔
        ((B + offset : Nat) : Int) ≤ X ω
      rw [ENat.natCast_le_natCast]
      have PositiveIndex : 0 < B + offset := lt_of_lt_of_le PositiveLambda (Nat.le_add_left offset B)
      simpa only [not_lt] using
        (not_congr (Int.toNat_lt' (m := X ω) (n := B + offset) PositiveIndex))
    rw [Event]
    exact Tail offset PositiveLambda
  have ExtendedBound := ExpectedWithTopNatLeOfExponentialTail μ τ B α β
    TimeMeasurable PositiveAlpha PositiveBeta PositivePartTail
  have IntegralBridge :
      ENNReal.ofReal (∫ ω, ((X ω).toNat : ℝ) ∂μ) =
        ∫⁻ ω, ENat.toENNReal (τ ω) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal PositivePartIntegrable PositivePartNonnegative]
    apply lintegral_congr
    intro ω
    change ENNReal.ofReal ((X ω).toNat : ℝ) =
      ENat.toENNReal ((X ω).toNat : ENat)
    simp only [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
  rw [← IntegralBridge] at ExtendedBound
  have PositivePartBound : (∫ ω, ((X ω).toNat : ℝ) ∂μ) ≤ (B : ℝ) + α * β :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp ExtendedBound
  calc
    (∫ ω, (X ω : ℝ) ∂μ) ≤ ∫ ω, ((X ω).toNat : ℝ) ∂μ := by
      apply integral_mono XIntegrable PositivePartIntegrable
      intro ω
      change (X ω : ℝ) ≤ ((X ω).toNat : ℝ)
      rw [PositivePart ω]
      exact le_max_left _ _
    _ ≤ (B : ℝ) + α * β := PositivePartBound

end

end ECTheoryLib.Probability

