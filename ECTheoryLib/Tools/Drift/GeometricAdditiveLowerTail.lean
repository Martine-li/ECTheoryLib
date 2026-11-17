import ECTheoryLib.Tools.Drift.ExponentialLowerTail
import ECTheoryLib.Probability.Moments.ConditionalExponentialMoment
import ECTheoryLib.Probability.Moments.ConditionalGeometricJumpMoment
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative
import Mathlib.Tactic.FieldSimp

/-!
# Geometric-jump additive lower tails

The original process may overshoot and may
leave the target again. The bound concerns its actual first hitting time.
The constants are explicit corrected counterparts, not the printed constants
of book Theorem 2.4.7.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- A closed early-hit bound under an upper bound on the conditional downward
drift and closed geometric jump tails. No absorption or finite runtime of the
original process is assumed. -/
theorem GeometricAdditiveDriftLowerTailOfCondExp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a s₀ eta Delta r : ℝ)
    (PositiveEta : 0 < eta) (PositiveDelta : 0 < Delta) (OneLeR : 1 ≤ r)
    (Values : ∀ j ω, X j ω ∈ S)
    (InitialAbove : a < s₀) (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω = s₀)
    (JumpTail : ∀ j (k : ℕ), ∀ᵐ ω ∂μ, a < X j ω →
      (μ[({u | (k : ℝ) ≤ |X (j + 1) u - X j u|}).indicator
        (fun _ => (1 : ℝ)) | F j]) ω ≤ r / (1 + eta) ^ k)
    (Drift : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => X j u - X (j + 1) u | F j]) ω ≤ Delta)
    (t : ℕ) (PositiveTime : 0 < t)
    (EarlyEnough : Delta * (t : ℝ) ≤ s₀ - a) :
    μ {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)
      ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal (Real.exp (-min
        (GeometricJumpMomentRadius eta * ((s₀ - a) - Delta * (t : ℝ)) / 4)
        ((GeometricJumpMomentRadius eta) ^ 2 *
          ((s₀ - a) - Delta * (t : ℝ)) ^ 2 /
          (32 * GeometricJumpMomentBound eta r * (t : ℝ))))) := by
  classical
  let q := GeometricJumpMomentRadius eta
  let M := GeometricJumpMomentBound eta r
  let h := (s₀ - a) - Delta * (t : ℝ)
  let Lambda := min (q / 2) (h * q ^ 2 / (16 * M * (t : ℝ)))
  let Beta := Real.exp (Lambda * Delta + (8 * M / q ^ 2) * Lambda ^ 2)
  let U (j : ℕ) (ω : Ω) := -ActiveIncrement X a j ω
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  let W (j : ℕ) (ω : Ω) := max (Y j ω - a) 0
  let R := S.image (fun s => max (s - a) 0)
  have PositiveQ : 0 < q := GeometricJumpMomentRadiusPositive eta PositiveEta
  have PositiveR : 0 < r := lt_of_lt_of_le zero_lt_one OneLeR
  have PositiveM : 0 < M := GeometricJumpMomentBoundPositive eta r PositiveEta PositiveR
  have TimePositive : 0 < (t : ℝ) := Nat.cast_pos.mpr PositiveTime
  have NonnegativeH : 0 ≤ h := sub_nonneg.mpr EarlyEnough
  have PositiveDenominator : 0 < 16 * M * (t : ℝ) := by positivity
  have NonnegativeLambda : 0 ≤ Lambda := le_min
    (div_nonneg PositiveQ.le (by norm_num))
    (div_nonneg (mul_nonneg NonnegativeH (sq_nonneg q)) PositiveDenominator.le)
  have Small : Lambda ≤ q / 2 := min_le_left _ _
  have Radius : Lambda ≤ q := by linarith
  have OneLeBeta : 1 ≤ Beta := by
    apply Real.one_le_exp
    exact add_nonneg (mul_nonneg NonnegativeLambda PositiveDelta.le)
      (mul_nonneg (by positivity) (sq_nonneg Lambda))
  have Coordinates (j : ℕ) : Measurable (X j) := AdaptedX.measurable
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) S (Coordinates j) (ae_of_all _ (Values j))
  have ActiveObservable (j : ℕ) : Measurable (ActiveIncrement X a j) :=
    Measurable.ite (measurableSet_lt measurable_const (Coordinates j))
      ((Coordinates (j + 1)).sub (Coordinates j)) measurable_const
  have ActiveTail (j k : ℕ) :
      (μ[({u | (k : ℝ) ≤ |ActiveIncrement X a j u|}).indicator
        (fun _ => (1 : ℝ)) | F j]) ≤ᵐ[μ]
        (fun _ => r / (1 + eta) ^ k) :=
    ConditionalJumpTailOfRestriction μ (F j) (F.le j) {ω | a < X j ω}
      (measurableSet_lt measurable_const (AdaptedX j))
      (fun ω => X (j + 1) ω - X j ω)
      ((Coordinates (j + 1)).sub (Coordinates j)) eta r PositiveEta OneLeR
      (JumpTail j) k
  have ActiveMoment (j : ℕ) :
      Integrable (fun ω => Real.exp (q * |ActiveIncrement X a j ω|)) μ ∧
      (μ[fun u => Real.exp (q * |ActiveIncrement X a j u|) | F j]) ≤ᵐ[μ]
        (fun _ => M) :=
    ConditionalAbsoluteExponentialMomentOfJumpTail μ (F j) (F.le j)
      (ActiveIncrement X a j) eta r PositiveEta PositiveR.le
      (ActiveObservable j) (ActiveTail j)
  have ActiveIntegrable (j : ℕ) : Integrable (ActiveIncrement X a j) μ :=
    IntegrableOfAbsoluteExponential μ (ActiveIncrement X a j) q PositiveQ
      (ActiveObservable j) (ActiveMoment j).1
  have IntegrableU (j : ℕ) : Integrable (U j) μ := (ActiveIntegrable j).neg
  have AbsoluteU (j : ℕ) :
      Integrable (fun ω => Real.exp (q * |U j ω|)) μ ∧
      (μ[fun u => Real.exp (q * |U j u|) | F j]) ≤ᵐ[μ] (fun _ => M) := by
    simpa only [U, abs_neg] using ActiveMoment j
  have ActiveMean (j : ℕ) : ∀ᵐ ω ∂μ, a < X j ω →
      (μ[U j | F j]) ω ≤ Delta := by
    have AsIndicator : U j = ({ω | a < X j ω}).indicator
        (fun ω => X j ω - X (j + 1) ω) := by
      funext ω
      by_cases Above : a < X j ω
      · simp only [U, ActiveIncrement, if_pos Above,
          Set.indicator_of_mem (show ω ∈ {u | a < X j u} from Above)]
        ring
      · simp only [U, ActiveIncrement, if_neg Above, neg_zero,
          Set.indicator_of_notMem (show ω ∉ {u | a < X j u} from Above)]
    have Event : MeasurableSet[F j] {ω | a < X j ω} :=
      measurableSet_lt measurable_const (AdaptedX j)
    have Conditional := condExp_indicator (f := fun ω => X j ω - X (j + 1) ω)
      ((IntegrableX j).sub (IntegrableX (j + 1))) Event
    rw [AsIndicator]
    filter_upwards [Conditional, Drift j] with ω Equal Mean
    intro Above
    rw [Equal, Set.indicator_of_mem (show ω ∈ {u | a < X j u} from Above)]
    exact Mean Above
  have ActiveExponential (j : ℕ) :
      Integrable (fun ω => Real.exp (Lambda * U j ω)) μ := by
    simpa only [U, mul_neg, neg_mul] using
      (NegativeExponentialIntegrableOfAbsolute μ (ActiveIncrement X a j) q Lambda
        NonnegativeLambda Radius (ActiveObservable j).aemeasurable (ActiveMoment j).1)
  have LocalMoment (j : ℕ) : ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * U j u) | F j]) ω ≤ Beta := by
    have AbsoluteNeg : Integrable (fun ω => Real.exp (q * |-(U j ω)|)) μ := by
      simpa only [abs_neg] using (AbsoluteU j).1
    have Quadratic := ConditionalNegativeExponentialQuadraticUpper μ (F j) (F.le j)
      (-(U j)) q Lambda PositiveQ NonnegativeLambda Small
      (IntegrableU j).neg AbsoluteNeg
    simp only [Pi.neg_apply, neg_mul_neg, abs_neg] at Quadratic
    have Flip := condExp_neg (U j) (F j) (μ := μ)
    have NonnegativeCoefficient : 0 ≤ 8 * Lambda ^ 2 / q ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) (sq_nonneg Lambda)) (sq_nonneg q)
    filter_upwards [Quadratic, Flip, (AbsoluteU j).2, ActiveMean j]
      with ω Quadratic Flip Moment Mean
    intro Above
    change (μ[-(U j) | F j]) ω = -(μ[U j | F j]) ω at Flip
    rw [Flip] at Quadratic
    have MeanScale := mul_le_mul_of_nonneg_left (Mean Above) NonnegativeLambda
    have MomentScale := mul_le_mul_of_nonneg_left Moment NonnegativeCoefficient
    calc
      _ ≤ 1 + Lambda * Delta + (8 * Lambda ^ 2 / q ^ 2) * M := by
        linarith only [Quadratic, MeanScale, MomentScale]
      _ = (Lambda * Delta + (8 * M / q ^ 2) * Lambda ^ 2) + 1 := by ring
      _ ≤ Beta := Real.add_one_le_exp _
  have StoppedBridge (j : ℕ) :
      Integrable (fun ω => Real.exp (-Lambda * (Y (j + 1) ω - Y j ω))) μ ∧
      (μ[fun u => Real.exp (-Lambda * (Y (j + 1) u - Y j u)) | F j]) =ᵐ[μ]
        (fun ω => if a < Y j ω then
          (μ[fun u => Real.exp (Lambda * U j u) | F j]) ω else 1) := by
    have IntegrableActive :
        Integrable (fun ω => Real.exp (-Lambda * ActiveIncrement X a j ω)) μ := by
      simpa only [U, mul_neg, neg_mul] using ActiveExponential j
    have Bridge := StoppedIncrementConditional μ X F AdaptedX a j
      (fun z => Real.exp (-Lambda * z)) IntegrableActive
    simpa only [Y, U, mul_neg, neg_mul, mul_zero, Real.exp_zero] using Bridge
  have AdaptedY : Adapted F Y :=
    StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have AdaptedW : Adapted F W := fun j =>
    ((AdaptedY j).sub measurable_const).max measurable_const
  have ValuesY (j : ℕ) (ω : Ω) : Y j ω ∈ S :=
    StopAtFirstHitValues (fun s : ℝ => s ≤ a) X (S : Set ℝ) Values j ω
  have ValuesW (j : ℕ) (ω : Ω) : W j ω ∈ R :=
    Finset.mem_image.mpr ⟨Y j ω, ValuesY j ω, rfl⟩
  have MomentIntegrableW (j : ℕ) :
      Integrable (fun ω => Real.exp (Lambda * (W j ω - W (j + 1) ω))) μ := by
    let D := fun ω => W j ω - W (j + 1) ω
    let V := (R.product R).image (fun p => p.1 - p.2)
    have Observable : Measurable D := (AdaptedW.measurable).sub AdaptedW.measurable
    have RangeD (ω : Ω) : D ω ∈ V :=
      Finset.mem_image.mpr ⟨(W j ω, W (j + 1) ω),
        Finset.mem_product.mpr ⟨ValuesW j ω, ValuesW (j + 1) ω⟩, rfl⟩
    exact FiniteStateCompositionIntegrable μ D V (fun z => Real.exp (Lambda * z))
      Observable RangeD
  have MomentW (j : ℕ) : ∀ᵐ ω ∂μ, W j ω ≠ 0 →
      (μ[fun u => Real.exp (Lambda * (W j u - W (j + 1) u)) | F j]) ω ≤ Beta := by
    have Domination : (fun ω => Real.exp (Lambda * (W j ω - W (j + 1) ω))) ≤ᵐ[μ]
        (fun ω => Real.exp (-Lambda * (Y (j + 1) ω - Y j ω))) := by
      apply ae_of_all
      intro ω
      apply Real.exp_le_exp.mpr
      have Clipped := mul_le_mul_of_nonneg_left
        (ShiftedPositivePartStoppedDecreaseLe X a j ω) NonnegativeLambda
      change Lambda * (W j ω - W (j + 1) ω) ≤
        Lambda * (Y j ω - Y (j + 1) ω) at Clipped
      linarith only [Clipped]
    have Comparison := condExp_mono (m := F j) (MomentIntegrableW j)
      (StoppedBridge j).1 Domination
    filter_upwards [Comparison, (StoppedBridge j).2, LocalMoment j]
      with ω Comparison Stopped Local
    intro Nonzero
    have Above : a < Y j ω := by
      by_contra NotAbove
      apply Nonzero
      exact max_eq_right (sub_nonpos.mpr (le_of_not_gt NotAbove))
    rw [Stopped, if_pos Above] at Comparison
    apply Comparison.trans (Local _)
    have Original := StopAtFirstHitStepBefore (fun s : ℝ => s ≤ a) X j ω
      (not_le_of_gt Above)
    rwa [← Original.1]
  have InitialW : ∀ᵐ ω ∂μ, W 0 ω = s₀ - a := by
    filter_upwards [FixedInitial] with ω Initial
    change max (Y 0 ω - a) 0 = s₀ - a
    rw [show Y 0 ω = s₀ by simpa only [Y, StopAtFirstHitInitial] using Initial]
    exact max_eq_left (sub_nonneg.mpr InitialAbove.le)
  have Bound := ExponentialDriftLowerTailOfCondExp μ W F AdaptedW R Lambda (s₀ - a) id
    (fun _ => Beta) ValuesW (ShiftedPositivePartStoppedZeroAbsorbing μ X a)
    rfl (fun _ => OneLeBeta) MomentW InitialW t
  have EventEq : {ω | ZeroHittingTime W ω ≤ (t : WithTop ℕ)} =
      {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)} := by
    ext ω
    have TimeEq : ZeroHittingTime W ω =
        FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) :=
      (ShiftedPositivePartZeroTime Y a ω).trans
        (FirstHittingTimeStopped (fun s : ℝ => s ≤ a) X ω)
    change ZeroHittingTime W ω ≤ (t : WithTop ℕ) ↔
      FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)
    rw [TimeEq]
  rw [EventEq] at Bound
  simp only [id_eq, Finset.prod_const, Finset.card_range] at Bound
  dsimp only [Beta] at Bound
  rw [← Real.exp_nat_mul, ← Real.exp_add] at Bound
  have QuadraticBudget :
      (t : ℝ) * (8 * M / q ^ 2) * Lambda ^ 2 ≤ h * Lambda / 2 := by
    have Parameter : Lambda ≤ h * q ^ 2 / (16 * M * (t : ℝ)) := min_le_right _ _
    have Multiplied := (le_div_iff₀ PositiveDenominator).mp Parameter
    have Scaled := mul_le_mul_of_nonneg_left Multiplied NonnegativeLambda
    rw [show (t : ℝ) * (8 * M / q ^ 2) * Lambda ^ 2 =
      (8 * M * (t : ℝ) * Lambda ^ 2) / q ^ 2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos PositiveQ)).mpr
    nlinarith only [Scaled]
  have Optimized : h * Lambda / 2 =
      min (q * h / 4) (q ^ 2 * h ^ 2 / (32 * M * (t : ℝ))) := by
    calc
      _ = (h / 2) * min (q / 2) (h * q ^ 2 / (16 * M * (t : ℝ))) := by
        dsimp only [Lambda]
        ring
      _ = min ((h / 2) * (q / 2))
          ((h / 2) * (h * q ^ 2 / (16 * M * (t : ℝ)))) :=
        mul_min_of_nonneg _ _ (div_nonneg NonnegativeH (by norm_num))
      _ = _ := by
        congr 1 <;> field_simp [PositiveM.ne', TimePositive.ne'] <;> ring
  have ExponentBound :
      (t : ℝ) * (Lambda * Delta + (8 * M / q ^ 2) * Lambda ^ 2) -
        Lambda * (s₀ - a) ≤
      -min (q * h / 4) (q ^ 2 * h ^ 2 / (32 * M * (t : ℝ))) := by
    calc
      _ = -h * Lambda + (t : ℝ) * (8 * M / q ^ 2) * Lambda ^ 2 := by
        dsimp only [h]
        ring
      _ ≤ -(h * Lambda / 2) := by linarith only [QuadraticBudget]
      _ = _ := congrArg Neg.neg Optimized
  exact Bound.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
    simpa only [q, M, h, sub_eq_add_neg, neg_mul] using ExponentBound)))

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Strict integer jump tails imply the corrected lower tail with the explicit
prefactor cost `max 1 (r * (1 + eta))`. This is not the book's printed bound. -/
theorem GeometricAdditiveDriftLowerTailOfStrictJumpTail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a s₀ eta Delta r : ℝ)
    (PositiveEta : 0 < eta) (PositiveDelta : 0 < Delta) (PositiveR : 0 < r)
    (Values : ∀ j ω, X j ω ∈ S)
    (InitialAbove : a < s₀) (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω = s₀)
    (JumpTail : ∀ j (k : ℕ), ∀ᵐ ω ∂μ, a < X j ω →
      (μ[({u | (k : ℝ) < |X (j + 1) u - X j u|}).indicator
        (fun _ => (1 : ℝ)) | F j]) ω ≤ r / (1 + eta) ^ k)
    (Drift : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => X j u - X (j + 1) u | F j]) ω ≤ Delta)
    (t : ℕ) (PositiveTime : 0 < t)
    (EarlyEnough : Delta * (t : ℝ) ≤ s₀ - a) :
    μ {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)
      ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal (Real.exp (-min
        (GeometricJumpMomentRadius eta * ((s₀ - a) - Delta * (t : ℝ)) / 4)
        ((GeometricJumpMomentRadius eta) ^ 2 *
          ((s₀ - a) - Delta * (t : ℝ)) ^ 2 /
          (32 * GeometricJumpMomentBound eta (max 1 (r * (1 + eta))) * (t : ℝ))))) := by
  apply GeometricAdditiveDriftLowerTailOfCondExp μ X F AdaptedX S a s₀ eta Delta
    (max 1 (r * (1 + eta))) PositiveEta PositiveDelta (le_max_left _ _)
    Values InitialAbove FixedInitial _ Drift t PositiveTime EarlyEnough
  intro j
  exact ConditionalClosedJumpTailOfStrict μ (F j) (F.le j) {ω | a < X j ω}
    (fun u => X (j + 1) u - X j u)
    (AdaptedX.measurable.sub AdaptedX.measurable) eta r PositiveEta PositiveR (JumpTail j)

end
end ECTheoryLib.Tools.Drift
