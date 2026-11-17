import ECTheoryLib.Tools.Drift.ExponentialTail
import ECTheoryLib.Probability.Moments.ConditionalExponentialMoment
import ECTheoryLib.Probability.Moments.ConditionalGeometricJumpMoment
import ECTheoryLib.Probability.HittingTimes.StoppedIncrement
import Mathlib.Tactic.FieldSimp

/-!
# Additive upper tails from conditional geometric jump bounds

The original process need not be absorbing. A common finite scalar range,
full-history downward drift and closed integer jump tails yield a strict
first-hitting-time tail with explicit constants. Internal stopping preserves
the first hitting jump. Arbitrary real targets and the drift-time equality
case are included. These constants are not the printed pair in Theorem 2.4.7.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- A geometric-jump upper tail for the original, possibly nonabsorbing process.
The jump premise is a closed integer tail, including threshold zero. -/
theorem GeometricAdditiveDriftUpperTailOfCondExp
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
      Delta ≤ (μ[fun u => X j u - X (j + 1) u | F j]) ω)
    (t : ℕ) (PositiveTime : 0 < t)
    (LateEnough : s₀ - a ≤ Delta * (t : ℝ)) :
    μ {ω | (t : WithTop ℕ) <
      FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} ≤
      ENNReal.ofReal (Real.exp (-min
        (GeometricJumpMomentRadius eta * (Delta * (t : ℝ) - (s₀ - a)) / 4)
        ((GeometricJumpMomentRadius eta) ^ 2 *
          (Delta * (t : ℝ) - (s₀ - a)) ^ 2 /
          (32 * GeometricJumpMomentBound eta r * (t : ℝ))))) := by
  classical
  let q := GeometricJumpMomentRadius eta
  let M := GeometricJumpMomentBound eta r
  let h := Delta * (t : ℝ) - (s₀ - a)
  let Lambda := min (q / 2) (h * q ^ 2 / (16 * M * (t : ℝ)))
  let Beta := Real.exp (-Lambda * Delta + (8 * M / q ^ 2) * Lambda ^ 2)
  let U (j : ℕ) (ω : Ω) := -ActiveIncrement X a j ω
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  have PositiveQ : 0 < q := GeometricJumpMomentRadiusPositive eta PositiveEta
  have PositiveR : 0 < r := lt_of_lt_of_le zero_lt_one OneLeR
  have PositiveM : 0 < M := GeometricJumpMomentBoundPositive eta r PositiveEta PositiveR
  have TimePositive : 0 < (t : ℝ) := Nat.cast_pos.mpr PositiveTime
  have NonnegativeH : 0 ≤ h := sub_nonneg.mpr LateEnough
  have PositiveDenominator : 0 < 16 * M * (t : ℝ) := by positivity
  have NonnegativeLambda : 0 ≤ Lambda := le_min
    (div_nonneg PositiveQ.le (by norm_num))
    (div_nonneg (mul_nonneg NonnegativeH (sq_nonneg q)) PositiveDenominator.le)
  have Small : Lambda ≤ q / 2 := min_le_left _ _
  have Radius : Lambda ≤ q := by linarith
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
      Delta ≤ (μ[U j | F j]) ω := by
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
      Integrable (fun ω => Real.exp (-Lambda * U j ω)) μ :=
    NegativeExponentialIntegrableOfAbsolute μ (U j) q Lambda NonnegativeLambda Radius
      (IntegrableU j).aemeasurable (AbsoluteU j).1
  have LocalMoment (j : ℕ) : ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (-Lambda * U j u) | F j]) ω ≤ Beta := by
    have Quadratic := ConditionalNegativeExponentialQuadraticUpper μ (F j) (F.le j)
      (U j) q Lambda PositiveQ NonnegativeLambda Small
      (IntegrableU j) (AbsoluteU j).1
    have NonnegativeCoefficient : 0 ≤ 8 * Lambda ^ 2 / q ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) (sq_nonneg Lambda)) (sq_nonneg q)
    filter_upwards [Quadratic, (AbsoluteU j).2, ActiveMean j]
      with ω Quadratic Moment Mean
    intro Above
    have MeanScale := mul_le_mul (le_refl Lambda) (Mean Above)
      PositiveDelta.le NonnegativeLambda
    have MomentScale := mul_le_mul_of_nonneg_left Moment NonnegativeCoefficient
    calc
      _ ≤ 1 - Lambda * Delta + (8 * Lambda ^ 2 / q ^ 2) * M := by
        linarith only [Quadratic, MeanScale, MomentScale]
      _ = (-Lambda * Delta + (8 * M / q ^ 2) * Lambda ^ 2) + 1 := by ring
      _ ≤ Beta := Real.add_one_le_exp _
  have StoppedMoment (j : ℕ) :
      (μ[fun u => Real.exp (Lambda * (Y (j + 1) u - Y j u)) | F j]) =ᵐ[μ]
        (fun ω => if a < Y j ω then
          (μ[fun u => Real.exp (-Lambda * U j u) | F j]) ω else 1) := by
    have IntegrableActive :
        Integrable (fun ω => Real.exp (Lambda * ActiveIncrement X a j ω)) μ := by
      simpa only [U, neg_mul_neg] using ActiveExponential j
    have Bridge := StoppedIncrementConditional μ X F AdaptedX a j
      (fun z => Real.exp (Lambda * z)) IntegrableActive
    simpa only [Y, U, neg_mul_neg, mul_zero, Real.exp_zero] using Bridge.2
  have AdaptedY : Adapted F Y :=
    StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have ValuesY (j : ℕ) (ω : Ω) : Y j ω ∈ S :=
    StopAtFirstHitValues (fun s : ℝ => s ≤ a) X (S : Set ℝ) Values j ω
  have InitialY : ∀ᵐ ω ∂μ, Y 0 ω = s₀ := by
    simpa only [Y, StopAtFirstHitInitial] using FixedInitial
  have AbsorbingY (j : ℕ) : ∀ᵐ ω ∂μ, Y j ω ≤ a → Y (j + 1) ω ≤ a :=
    ae_of_all _ (StopAtFirstHitAbsorbing (fun s : ℝ => s ≤ a) X j)
  have MomentY (j : ℕ) : ∀ᵐ ω ∂μ, a < Y j ω →
      (μ[fun u => Real.exp (Lambda * (Y (j + 1) u - Y j u)) | F j]) ω ≤ Beta := by
    filter_upwards [StoppedMoment j, LocalMoment j] with ω Equal Bound
    intro Above
    rw [Equal, if_pos Above]
    apply Bound
    have Original := StopAtFirstHitStepBefore (fun s : ℝ => s ≤ a) X j ω
      (not_le_of_gt Above)
    rwa [← Original.1]
  have Bound := ExponentialDriftUpperTailOfCondExp μ Y F AdaptedY S a Lambda s₀ id
    (fun _ => Beta) ValuesY AbsorbingY NonnegativeLambda
    (fun _ => (Real.exp_pos _).le) (fun _ _ Above => Above.le)
    MomentY InitialAbove InitialY t
  have TailEq :
      {ω | (t : WithTop ℕ) <
        FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => Y j ω)} =
      {ω | (t : WithTop ℕ) <
        FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} := by
    ext ω
    have Same :
        FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => Y j ω) ≤ (t : WithTop ℕ) ↔
        FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ) :=
      Set.ext_iff.mp (StopAtFirstHitEvent (fun s : ℝ => s ≤ a) X t) ω
    change ((t : WithTop ℕ) <
      FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => Y j ω)) ↔
      ((t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω))
    simpa only [not_le] using not_congr Same
  rw [TailEq] at Bound
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
      (t : ℝ) * (-Lambda * Delta + (8 * M / q ^ 2) * Lambda ^ 2) +
        Lambda * (s₀ - a) ≤
      -min (q * h / 4) (q ^ 2 * h ^ 2 / (32 * M * (t : ℝ))) := by
    calc
      _ = -h * Lambda + (t : ℝ) * (8 * M / q ^ 2) * Lambda ^ 2 := by
        dsimp only [h]
        ring
      _ ≤ -(h * Lambda / 2) := by linarith only [QuadraticBudget]
      _ = _ := congrArg Neg.neg Optimized
  exact Bound.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ExponentBound))

end
end ECTheoryLib.Tools.Drift
