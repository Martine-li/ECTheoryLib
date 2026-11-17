import ECTheoryLib.Tools.Drift.VariableLower
import ECTheoryLib.Tools.Drift.Multiplicative
import ECTheoryLib.Probability.Conditioning.FiniteConditioning

import ECTheoryLib.Probability.Processes.ConditionalDrift

/-!
# Multiplicative drift lower bound with a rare-large-jump condition

Source: Lengler, Drift Analysis, Theorem 2.4.3, pp.114-115, in Doerr and
Neumann (eds.), Theory of Evolutionary Computation (2020),
<https://doi.org/10.1007/978-3-030-29414-4_2>.
See also Lehre and Witt, General Drift Analysis with Tail Bounds,
arXiv:1307.2559v4, Theorem 19 and its proof.

The finite range is pointwise, the path is nonincreasing almost surely,
and the rare event includes equality: current-next >= beta*current.
A logarithmic potential is injective on the attainable range and preserves
first hitting zero. Its conditional drift is bounded by splitting small
and large relative drops, then the existing additive lower theorem applies.
No finite runtime or termination premise is added.

The general bound uses zero potential at initial zero. The displayed
logarithm formula requires almost surely nonzero initialization; Lean's
total log(0)=0 is not used as a mathematical logarithm at zero.
The beta=1 endpoint is handled separately. The proof also admits beta=0
and any delta>0; the source's 0<beta,delta<=1 is a specialization.
The filtration entry uses Mathlib conditional expectations for both the
signed decrease and the indicator of a large decrease.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability ProbabilityTheory
noncomputable section

theorem LogDriftPotentialPositive (smin s : ℝ) (MinimumPositive : 0 < smin)
    (LowerS : smin ≤ s) : 0 < MultiplicativeDriftPotential smin 1 s := by
  have PositiveS : 0 < s := MinimumPositive.trans_le LowerS
  have RatioAtLeastOne : 1 ≤ s/smin := (le_div_iff₀ MinimumPositive).mpr (by simpa only [one_mul] using LowerS)
  have LogNonnegative : 0 ≤ Real.log (s/smin) := Real.log_nonneg RatioAtLeastOne
  rw [MultiplicativeDriftPotential, if_neg PositiveS.ne', div_one]
  linarith

theorem LogDriftPotentialZeroIff (smin s : ℝ) (MinimumPositive : 0 < smin)
    (RangeS : s=0 ∨ smin ≤ s) : MultiplicativeDriftPotential smin 1 s=0 ↔ s=0 := by
  constructor
  · intro Zero
    by_contra Nonzero
    exact (LogDriftPotentialPositive smin s MinimumPositive (RangeS.resolve_left Nonzero)).ne' Zero
  · intro Zero
    rw [Zero, MultiplicativeDriftPotential, if_pos rfl]

theorem LogDriftPotentialInjective (smin s r : ℝ) (MinimumPositive : 0 < smin)
    (RangeS : s=0 ∨ smin ≤ s) (RangeR : r=0 ∨ smin ≤ r)
    (Equal : MultiplicativeDriftPotential smin 1 s=MultiplicativeDriftPotential smin 1 r) : s=r := by
  by_cases ZeroS : s=0
  · have ZeroR : r=0 := (LogDriftPotentialZeroIff smin r MinimumPositive RangeR).mp
      (Equal.symm.trans ((LogDriftPotentialZeroIff smin s MinimumPositive RangeS).mpr ZeroS))
    exact ZeroS.trans ZeroR.symm
  · have ZeroR : r ≠ 0 := by
      intro Zero
      apply ZeroS
      apply (LogDriftPotentialZeroIff smin s MinimumPositive RangeS).mp
      rw [Equal]
      exact (LogDriftPotentialZeroIff smin r MinimumPositive RangeR).mpr Zero
    have PositiveS := MinimumPositive.trans_le (RangeS.resolve_left ZeroS)
    have PositiveR := MinimumPositive.trans_le (RangeR.resolve_left ZeroR)
    simp only [MultiplicativeDriftPotential, if_neg ZeroS, if_neg ZeroR, div_one] at Equal
    have LogsEqual : Real.log (s/smin)=Real.log (r/smin) := by linarith
    have RatiosEqual := Real.log_injOn_pos (div_pos PositiveS MinimumPositive)
      (div_pos PositiveR MinimumPositive) LogsEqual
    exact (div_left_inj' MinimumPositive.ne').mp RatiosEqual

/-- Small relative jumps use the reciprocal slope; large jumps cost at most the full potential. -/
theorem LogDriftPotentialDifferenceUpper (smin β s r : ℝ)
    (MinimumPositive : 0 < smin) (BetaLessOne : β < 1)
    (LowerS : smin ≤ s) (RangeR : r=0 ∨ smin ≤ r) (Nonincreasing : r ≤ s) :
    MultiplicativeDriftPotential smin 1 s-MultiplicativeDriftPotential smin 1 r ≤
      (s-r)/((1-β)*s)+MultiplicativeDriftPotential smin 1 s*(if β*s ≤ s-r then 1 else 0) := by
  have PositiveS : 0 < s := MinimumPositive.trans_le LowerS
  have PositiveGap : 0 < 1-β := sub_pos.mpr BetaLessOne
  have PositiveDenominator := mul_pos PositiveGap PositiveS
  by_cases Large : β*s ≤ s-r
  · rw [if_pos Large, mul_one]
    have NextNonnegative : 0 ≤ MultiplicativeDriftPotential smin 1 r := by
      rcases RangeR with Zero | Lower
      · rw [Zero, MultiplicativeDriftPotential, if_pos rfl]
      · exact (LogDriftPotentialPositive smin r MinimumPositive Lower).le
    have RatioNonnegative : 0 ≤ (s-r)/((1-β)*s) :=
      div_nonneg (sub_nonneg.mpr Nonincreasing) PositiveDenominator.le
    linarith
  · rw [if_neg Large, mul_zero, add_zero]
    have Small : s-r < β*s := lt_of_not_ge Large
    have Ratio : 1/(1/(1-β)) ≤ max r smin/s := by
      rw [one_div_one_div]
      apply (le_div_iff₀ PositiveS).mpr
      have AboveR := le_max_left r smin
      nlinarith
    have Raw := VariableDriftPotentialDifferenceUpper smin (fun x => x) MinimumPositive
      (fun x Lower => MinimumPositive.trans_le Lower) (by intro _ _ _ _ Before; exact Before)
      s r (1/(1-β)) (one_div_pos.mpr PositiveGap) LowerS RangeR Nonincreasing Ratio
    have Current := LinearVariableDriftPotential smin 1 s MinimumPositive zero_lt_one (Or.inr LowerS)
    have Next := LinearVariableDriftPotential smin 1 r MinimumPositive zero_lt_one RangeR
    simp only [one_mul] at Current Next
    rw [Current, Next] at Raw
    have Scale : (1/(1-β))*((s-r)/s) = (s-r)/((1-β)*s) := by field_simp
    rw [Scale] at Raw
    exact Raw

variable {Ω : Type*} [MeasurableSpace Ω]

def RelativeDecreaseEvent (X : ℕ → Ω → ℝ) (β : ℝ) (t : ℕ) : Set Ω :=
  {ω | β*X t ω ≤ X t ω-X (t+1) ω}

theorem RelativeDecreaseEventMeasurable (X : ℕ → Ω → ℝ) (β : ℝ) (t : ℕ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) : MeasurableSet (RelativeDecreaseEvent X β t) :=
  measurableSet_le ((CoordinatesMeasurable t).const_mul β)
    ((CoordinatesMeasurable t).sub (CoordinatesMeasurable (t+1)))

theorem LogPotentialConditionalDecrease (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin β δ : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (MinimumPositive : 0 < smin) (BetaLessOne : β < 1)
    (DeltaNonnegative : 0 ≤ δ)
    (StateLowerBound : ∀ s ∈ S, s=0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (t : ℕ) (s : ℝ) (InS : s ∈ S) (Nonzero : s ≠ 0)
    (PositiveEvent : 0 < μ (StateEvent X t s))
    (DriftBound : StateDrift μ X t s ≤ δ*s)
    (LargeJumpBound : EventConditionalExpectation μ
      ((RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ))) (StateEvent X t s) ≤
        β*δ/(1+Real.log (s/smin))) :
    EventConditionalExpectation μ
      (fun ω => MultiplicativeDriftPotential smin 1 (X t ω)-
        MultiplicativeDriftPotential smin 1 (X (t+1) ω)) (StateEvent X t s) ≤
      δ*(1+β)/(1-β) := by
  classical
  let ν := cond μ (StateEvent X t s)
  let g := MultiplicativeDriftPotential smin 1
  let I := (RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ))
  have ConditionalProbability : IsProbabilityMeasure ν := cond_isProbabilityMeasure PositiveEvent.ne'
  have LowerS := (StateLowerBound s InS).resolve_left Nonzero
  have PositiveS := MinimumPositive.trans_le LowerS
  have PositiveGap : 0 < 1-β := sub_pos.mpr BetaLessOne
  have PositivePotential : 0 < g s := LogDriftPotentialPositive smin s MinimumPositive LowerS
  have PotentialFormula : g s=1+Real.log (s/smin) := by
    simp only [g, MultiplicativeDriftPotential, if_neg Nonzero, div_one]
  have DecreaseIntegrable : Integrable (fun ω => X t ω-X (t+1) ω) ν :=
    (FiniteStateIntegrable ν (X t) S (CoordinatesMeasurable t) (ae_of_all _ (ValuesInS t))).sub
      (FiniteStateIntegrable ν (X (t+1)) S (CoordinatesMeasurable (t+1)) (ae_of_all _ (ValuesInS (t+1))))
  have PotentialIntegrable : Integrable (fun ω => g (X t ω)-g (X (t+1) ω)) ν :=
    (FiniteStateCompositionIntegrable ν (X t) S g (CoordinatesMeasurable t) (ValuesInS t)).sub
      (FiniteStateCompositionIntegrable ν (X (t+1)) S g (CoordinatesMeasurable (t+1)) (ValuesInS (t+1)))
  have IndicatorIntegrable : Integrable I ν :=
    (integrable_const 1).indicator (RelativeDecreaseEventMeasurable X β t CoordinatesMeasurable)
  have ConditionalNonincreasing : ∀ᵐ ω ∂ν, X (t+1) ω ≤ X t ω :=
    cond_absolutelyContinuous.ae_le (Nonincreasing t)
  have Comparison : (∫ ω, g (X t ω)-g (X (t+1) ω) ∂ν) ≤
      ∫ ω, (X t ω-X (t+1) ω)/((1-β)*s)+g s*I ω ∂ν := by
    apply integral_mono_ae PotentialIntegrable
      ((DecreaseIntegrable.div_const _).add (IndicatorIntegrable.const_mul _))
    filter_upwards [ae_cond_mem (StateEventMeasurable X t s (CoordinatesMeasurable t)),
      ConditionalNonincreasing] with ω InEvent NextLe
    have Current : X t ω=s := InEvent
    have Bound := LogDriftPotentialDifferenceUpper smin β s (X (t+1) ω) MinimumPositive
      BetaLessOne LowerS (StateLowerBound _ (ValuesInS (t+1) ω))
      (by rw [← Current]; exact NextLe)
    simpa only [I, g, Pi.add_apply, Set.indicator_apply, RelativeDecreaseEvent, Set.mem_ofPred_eq, Current] using Bound
  rw [integral_add (DecreaseIntegrable.div_const _) (IndicatorIntegrable.const_mul _),
    integral_div, integral_const_mul] at Comparison
  have MeanDrift : (∫ ω, X t ω-X (t+1) ω ∂ν) ≤ δ*s := by
    rw [StateDrift, EventConditionalExpectationEqCondIntegral] at DriftBound
    exact DriftBound
  have MeanIndicator : (∫ ω, I ω ∂ν) ≤ β*δ/g s := by
    rw [EventConditionalExpectationEqCondIntegral, ← PotentialFormula] at LargeJumpBound
    exact LargeJumpBound
  have RightBound : (∫ ω, X t ω-X (t+1) ω ∂ν)/((1-β)*s)+g s*(∫ ω, I ω ∂ν) ≤
      δ*(1+β)/(1-β) := by
    have First := div_le_div_of_nonneg_right MeanDrift (mul_pos PositiveGap PositiveS).le
    have Second := mul_le_mul_of_nonneg_left MeanIndicator PositivePotential.le
    have SimplifyFirst : (δ*s)/((1-β)*s)=δ/(1-β) := by field_simp
    have SimplifySecond : g s*(β*δ/g s)=β*δ := by field_simp
    rw [SimplifyFirst] at First
    rw [SimplifySecond] at Second
    have Scalar : δ/(1-β)+β*δ ≤ δ*(1+β)/(1-β) := by
      apply (le_div_iff₀ PositiveGap).mpr
      rw [add_mul, div_mul_cancel₀ _ PositiveGap.ne']
      nlinarith [sq_nonneg β]
    exact (add_le_add First Second).trans Scalar
  rw [EventConditionalExpectationEqCondIntegral]
  exact Comparison.trans RightBound

/-- Multiplicative lower drift with a rare-large-jump condition, including β=1 and initial zero mass. -/
theorem MultiplicativeDriftLowerBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin β δ : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) (ZeroInS : 0 ∈ S)
    (MinimumPositive : 0 < smin) (BetaNonnegative : 0 ≤ β) (BetaAtMostOne : β ≤ 1)
    (DeltaPositive : 0 < δ)
    (StateLowerBound : ∀ s ∈ S, s=0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (DriftBound : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ δ*s)
    (LargeJumpBound : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ ((RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)))
        (StateEvent X t s) ≤ β*δ/(1+Real.log (s/smin))) :
    ENNReal.ofReal (((1-β)/(1+β))*(ExpectedValue μ
      (fun ω => MultiplicativeDriftPotential smin 1 (X 0 ω))/δ)) ≤ ExpectedZeroHittingTime μ X := by
  classical
  by_cases BetaOne : β=1
  · rw [BetaOne, sub_self, zero_div, zero_mul, ENNReal.ofReal_zero]
    exact bot_le
  · have BetaLessOne : β < 1 := lt_of_le_of_ne BetaAtMostOne BetaOne
    let g := MultiplicativeDriftPotential smin 1
    let Y := fun t ω => g (X t ω)
    let c := δ*(1+β)/(1-β)
    have PositiveGap : 0 < 1-β := sub_pos.mpr BetaLessOne
    have PositiveSum : 0 < 1+β := by linarith
    have PositiveC : 0 < c := div_pos (mul_pos DeltaPositive PositiveSum) PositiveGap
    have PotentialZero : g 0=0 := by simp only [g, MultiplicativeDriftPotential, ↓reduceIte]
    have ZeroIff (t : ℕ) (ω : Ω) : Y t ω=0 ↔ X t ω=0 :=
      LogDriftPotentialZeroIff smin (X t ω) MinimumPositive (StateLowerBound _ (ValuesInS t ω))
    have MeasurableY (t : ℕ) : Measurable (Y t) :=
      FiniteStateCompositionMeasurable (X t) S g (CoordinatesMeasurable t) (ValuesInS t)
    have RangeY (t : ℕ) (ω : Ω) : Y t ω ∈ S.image g :=
      Finset.mem_image.mpr ⟨X t ω, ValuesInS t ω, rfl⟩
    have NonnegativeY : ∀ y ∈ S.image g, 0 ≤ y := by
      intro y InImage
      obtain ⟨s, InS, rfl⟩ := Finset.mem_image.mp InImage
      rcases StateLowerBound s InS with Zero | Lower
      · rw [Zero, PotentialZero]
      · exact (LogDriftPotentialPositive smin s MinimumPositive Lower).le
    have AbsorbingY : ZeroIsAbsorbing μ Y := by
      intro t
      filter_upwards [Nonincreasing t] with ω NextLe
      intro CurrentZero
      apply (ZeroIff (t+1) ω).mpr
      have OriginalZero := (ZeroIff t ω).mp CurrentZero
      rw [OriginalZero] at NextLe
      rcases StateLowerBound _ (ValuesInS (t+1) ω) with NextZero | LowerNext
      · exact NextZero
      · have PositiveNext := MinimumPositive.trans_le LowerNext
        linarith
    have DriftY (t : ℕ) (y : ℝ) (InY : y ∈ S.image g) (NonzeroY : y ≠ 0)
        (PositiveY : 0 < μ (StateEvent Y t y)) : StateDrift μ Y t y ≤ c := by
      obtain ⟨s, InS, rfl⟩ := Finset.mem_image.mp InY
      have NonzeroS : s ≠ 0 := by
        intro Zero
        exact NonzeroY (Zero ▸ PotentialZero)
      have EventEquality : StateEvent Y t (g s)=StateEvent X t s := by
        ext ω
        change g (X t ω)=g s ↔ X t ω=s
        constructor
        · intro Equal
          exact LogDriftPotentialInjective smin (X t ω) s MinimumPositive
            (StateLowerBound _ (ValuesInS t ω)) (StateLowerBound s InS) Equal
        · intro Equal
          rw [Equal]
      have PositiveOriginal : 0 < μ (StateEvent X t s) := by
        rw [← EventEquality]
        exact PositiveY
      have Conditional := LogPotentialConditionalDecrease μ X S smin β δ CoordinatesMeasurable
        MinimumPositive BetaLessOne DeltaPositive.le StateLowerBound ValuesInS Nonincreasing t s InS
        NonzeroS PositiveOriginal (DriftBound t s InS NonzeroS PositiveOriginal)
        (LargeJumpBound t s InS NonzeroS PositiveOriginal)
      unfold StateDrift
      rw [EventEquality]
      exact Conditional
    have Bound := AdditiveDriftLowerBound μ Y (S.image g) c MeasurableY
      (Finset.mem_image.mpr ⟨0, ZeroInS, PotentialZero⟩) NonnegativeY RangeY AbsorbingY PositiveC DriftY
    have HittingTimeEquality : ZeroHittingTime Y=ZeroHittingTime X := by
      funext ω
      unfold ZeroHittingTime FirstHittingTime hittingAfter
      simp only [Set.mem_ofPred_eq, ZeroIff]
    have RuntimeEquality : ExpectedZeroHittingTime μ Y=ExpectedZeroHittingTime μ X := by
      unfold ExpectedZeroHittingTime
      rw [HittingTimeEquality]
    rw [RuntimeEquality] at Bound
    have Coefficient : ExpectedValue μ (Y 0)/c =
        ((1-β)/(1+β))*(ExpectedValue μ (Y 0)/δ) := by
      dsimp [c]
      field_simp
    rw [Coefficient] at Bound
    exact Bound

/-- The displayed logarithmic formula for almost surely positive initialization. -/
theorem MultiplicativeDriftLowerBoundOfPositiveInitial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin β δ : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) (ZeroInS : 0 ∈ S)
    (MinimumPositive : 0 < smin) (BetaNonnegative : 0 ≤ β) (BetaAtMostOne : β ≤ 1)
    (DeltaPositive : 0 < δ)
    (StateLowerBound : ∀ s ∈ S, s=0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (DriftBound : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ δ*s)
    (LargeJumpBound : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ ((RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)))
        (StateEvent X t s) ≤ β*δ/(1+Real.log (s/smin)))
    (InitialPositive : ∀ᵐ ω ∂μ, X 0 ω ≠ 0) :
    ENNReal.ofReal (((1-β)/(1+β))*((1+ExpectedValue μ (fun ω => Real.log (X 0 ω/smin)))/δ)) ≤
      ExpectedZeroHittingTime μ X := by
  have Bound := MultiplicativeDriftLowerBound μ X S smin β δ CoordinatesMeasurable ZeroInS
    MinimumPositive BetaNonnegative BetaAtMostOne DeltaPositive StateLowerBound ValuesInS
    Nonincreasing DriftBound LargeJumpBound
  have LogIntegrable := FiniteStateCompositionIntegrable μ (X 0) S (fun s => Real.log (s/smin))
    (CoordinatesMeasurable 0) (ValuesInS 0)
  have InitialMean : ExpectedValue μ (fun ω => MultiplicativeDriftPotential smin 1 (X 0 ω)) =
      1+ExpectedValue μ (fun ω => Real.log (X 0 ω/smin)) := by
    unfold ExpectedValue
    have Formula : (fun ω => MultiplicativeDriftPotential smin 1 (X 0 ω)) =ᵐ[μ]
        (fun ω => 1+Real.log (X 0 ω/smin)) := by
      filter_upwards [InitialPositive] with ω Nonzero
      simp only [MultiplicativeDriftPotential, if_neg Nonzero, div_one]
    rw [integral_congr_ae Formula, integral_add (integrable_const _) LogIntegrable,
      integral_const, probReal_univ, one_smul]
  rw [InitialMean] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Drift
namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Lengler's full-filtration hypotheses imply the logarithmic lower bound for positive initialization. -/
theorem MultiplicativeDriftLowerBoundOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (ProcessAdapted : Adapted F X) (S : Finset ℝ) (smin β δ : ℝ)
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (BetaNonnegative : 0 ≤ β) (BetaAtMostOne : β ≤ 1) (DeltaPositive : 0 < δ)
    (StateLowerBound : ∀ s ∈ S, s=0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (ConditionalDrift : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ δ*X t ω)
    (ConditionalLargeJump : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[(RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)) | F t]) ω ≤
        β*δ/(1+Real.log (X t ω/smin)))
    (InitialPositive : ∀ᵐ ω ∂μ, X 0 ω ≠ 0) :
    ENNReal.ofReal (((1-β)/(1+β))*((1+ExpectedValue μ (fun ω => Real.log (X 0 ω/smin)))/δ)) ≤
      ExpectedZeroHittingTime μ X := by
  have CoordinatesMeasurable (t : ℕ) : Measurable (X t) := ProcessAdapted.measurable
  have DriftBound (t : ℕ) (s : ℝ) (_InS : s ∈ S) (Nonzero : s ≠ 0)
      (PositiveEvent : 0 < μ (StateEvent X t s)) : StateDrift μ X t s ≤ δ*s := by
    have DecreaseIntegrable : Integrable (fun ω => X t ω-X (t+1) ω) μ :=
      (FiniteStateIntegrable μ (X t) S (CoordinatesMeasurable t) (ae_of_all _ (ValuesInS t))).sub
        (FiniteStateIntegrable μ (X (t+1)) S (CoordinatesMeasurable (t+1)) (ae_of_all _ (ValuesInS (t+1))))
    exact StateDriftUpperBoundOfCondExp μ X F ProcessAdapted (fun s => δ*s) t
      DecreaseIntegrable (ConditionalDrift t) s Nonzero PositiveEvent
  have LargeJumpBound (t : ℕ) (s : ℝ) (_InS : s ∈ S) (Nonzero : s ≠ 0)
      (PositiveEvent : 0 < μ (StateEvent X t s)) :
      EventConditionalExpectation μ ((RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)))
        (StateEvent X t s) ≤ β*δ/(1+Real.log (s/smin)) := by
    have IndicatorIntegrable : Integrable ((RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const 1).indicator (RelativeDecreaseEventMeasurable X β t CoordinatesMeasurable)
    exact StateEventExpectationUpperBoundOfCondExp μ X F ProcessAdapted
      (fun s => β*δ/(1+Real.log (s/smin))) t _ IndicatorIntegrable (ConditionalLargeJump t)
      s Nonzero PositiveEvent
  exact MultiplicativeDriftLowerBoundOfPositiveInitial μ X S smin β δ CoordinatesMeasurable
    ZeroInS MinimumPositive BetaNonnegative BetaAtMostOne DeltaPositive StateLowerBound ValuesInS
    Nonincreasing DriftBound LargeJumpBound InitialPositive

end
end ECTheoryLib.Tools.Drift
