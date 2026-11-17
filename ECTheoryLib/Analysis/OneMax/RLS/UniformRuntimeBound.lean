import ECTheoryLib.Analysis.OneMax.RLS.Drift
import ECTheoryLib.Tools.Drift.Additive
import Mathlib.Tactic.Linarith

/-!
# A coarse additive bound for uniformly initialized RLS on OneMax

The actual RLS kernel and uniform initial law generate trajectories through
mathlib's Ionescu–Tulcea construction. Positive length suffices to verify finite
nonnegative range, zero absorption, and conditional drift at least `1/n`.
The initial mean zero count is `n/2`, yielding `E[T] ≤ n²/2`.
This module asserts the coarse additive bound, not an exact or logarithmic bound.
Time zero is initialization, so initially optimal runs have zero runtime.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift

noncomputable section

/-- A complete sequence of length-n bit strings, indexed from initialization at time zero. -/
abbrev Trajectory (n : Nat) := Nat → Bits n

/-- The actual infinite trajectory law with standard uniform initialization. -/
def RunMeasure {n : Nat} (PositiveLength : 0 < n) : Measure (Trajectory n) :=
  RLSProcess PositiveLength (Problems.MaxNotWorse OneMax) (RLSInit n)

instance RunMeasureIsProbability {n : Nat} (PositiveLength : 0 < n) :
    IsProbabilityMeasure (RunMeasure PositiveLength) := by
  unfold RunMeasure
  infer_instance

/-- Read zero count along complete bit-string trajectories. The finite-range
constraint holds pointwise, even on trajectories not following the algorithm. -/
def PotentialProcess (n : Nat) (t : Nat) (Path : Trajectory n) : ℝ :=
  Potential (Path t)

/-- Expected iterations until OneMax optimality under standard uniform initialization. -/
def ExpectedUniformRuntime {n : Nat} (PositiveLength : 0 < n) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength) IsTarget (RLSInit n)
/-- Uniform initial zero count has mean `n/2`: complementation pairs
strings whose potentials sum to `n`. -/
theorem UniformInitialPotentialExpectation (n : Nat) :
    (∫ x, Potential x
      ∂(RLSInit n).toMeasure) = (n : ℝ) / 2 := by
  classical
  let Complement : Bits n → Bits n := fun x => fun i => !(x i)
  have ComplementTwice : Function.Involutive Complement := by
    intro x
    funext i
    unfold Complement
    cases x i with
    | false => rfl
    | true => rfl
  have ComplementBijective : Function.Bijective Complement := by
    exact ComplementTwice.bijective
  have ComplementScore : ∀ x : Bits n,
      OneMax (Complement x) = n - OneMax x := by
    intro x
    rw [← Problems.OneMax.ZeroBitCount]
    unfold OneMax
    apply Finset.sum_congr rfl
    intro i _Membership
    change (if !(x i) then 1 else 0 : Nat) = (if x i then 0 else 1)
    cases x i with
    | false => rfl
    | true => rfl
  have PairedPotential : ∀ x : Bits n,
      Potential x +
        Potential (Complement x) = (n : ℝ) := by
    intro x
    unfold Potential ZeroCount
    rw [Problems.OneMax.ZeroCountAsRealDifference, Problems.OneMax.ZeroCountAsRealDifference, ComplementScore]
    rw [Nat.cast_sub (Problems.OneMax.OneMaxLeN x)]
    ring
  have ComplementSum :
      (∑ x : Bits n, Potential (Complement x)) =
        ∑ x : Bits n, Potential x := by
    exact ComplementBijective.sum_comp (Potential (n := n))
  have SumPairedPotential :
      (∑ x : Bits n, Potential x) +
        (∑ x : Bits n, Potential (Complement x)) =
          (Fintype.card (Bits n) : ℝ) * (n : ℝ) := by
    rw [← Finset.sum_add_distrib]
    have EachPairContributesN :
        (∑ x : Bits n, (Potential x +
          Potential (Complement x))) =
            ∑ _x : Bits n, (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _Membership
      exact PairedPotential x
    rw [EachPairContributesN, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have SumPotential :
      (∑ x : Bits n, Potential x) =
        (Fintype.card (Bits n) : ℝ) * ((n : ℝ) / 2) := by
    rw [ComplementSum] at SumPairedPotential
    linarith
  unfold RLSInit
  rw [PMF.integral_eq_sum]
  change (∑ x : Bits n, ((PMF.uniformOfFintype (Bits n)) x).toReal *
    Potential x) = (n : ℝ) / 2
  have UniformWeight : ∀ x : Bits n,
      ((PMF.uniformOfFintype (Bits n)) x).toReal =
        1 / (Fintype.card (Bits n) : ℝ) := by
    intro x
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact (one_div (Fintype.card (Bits n) : ℝ)).symm
  have WeightedSum :
      (∑ x : Bits n, ((PMF.uniformOfFintype (Bits n)) x).toReal *
        Potential x) =
          (1 / (Fintype.card (Bits n) : ℝ)) *
            ∑ x : Bits n, Potential x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _Membership
    rw [UniformWeight]
  have CardinalityNonzero : (Fintype.card (Bits n) : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [WeightedSum, SumPotential, one_div, ← mul_assoc,
    inv_mul_cancel₀ CardinalityNonzero, one_mul]

/-- Project the actual trajectory law at time zero to identify its initial mean. -/
theorem InitialExpectation {n : Nat}
    (PositiveLength : 0 < n) :
    (∫ ω, PotentialProcess n 0 ω
      ∂(RunMeasure PositiveLength)) = (n : ℝ) / 2 := by
  have PotentialMeasurable : Measurable (Potential (n := n)) := by
    exact measurable_of_finite _
  unfold PotentialProcess RunMeasure
  rw [← integral_map_of_stronglyMeasurable (measurable_pi_apply 0)
    PotentialMeasurable.stronglyMeasurable]
  change (∫ x, Potential x
    ∂(PathMeasure (Step PositiveLength) (RLSInit n)).map (fun Path => Path 0)) = _
  rw [PathMeasureInitial (Step PositiveLength) (RLSInit n)]
  exact UniformInitialPotentialExpectation n

/-- Conditional drift is `s/n` on every positive-probability potential-level
event, by one-step total expectation under the actual trajectory law. -/
theorem ConditionalDrift {n : Nat}
    (PositiveLength : 0 < n) (t : Nat) (s : ℝ)
    (EventPositive : 0 < (RunMeasure PositiveLength)
      (StateEvent (PotentialProcess n) t s)) :
    StateDrift (RunMeasure PositiveLength)
      (PotentialProcess n) t s = s / (n : ℝ) := by
  classical
  let μ := RunMeasure PositiveLength
  let X := PotentialProcess n
  let Event := StateEvent X t s
  have EventMeasurable : MeasurableSet Event := by
    apply ECTheoryLib.Probability.StateEventMeasurable
    exact (measurable_of_finite (Potential (n := n))).comp
      (measurable_pi_apply t)
  let EventDecrease : Bits n → Bits n → ℝ :=
    fun x y => if Potential x = s then
      Potential x - Potential y else 0
  have Numerator :
      (∫ ω in Event, X t ω - X (t + 1) ω ∂μ) =
        (μ Event).toReal * (s / (n : ℝ)) := by
    rw [← integral_indicator EventMeasurable]
    change (∫ ω, EventDecrease (ω t) (ω (t + 1)) ∂μ) = _
    have TransitionIntegral :
        (∫ ω, EventDecrease (ω t) (ω (t + 1)) ∂μ) =
          ∫ ω, (∫ y, EventDecrease (ω t) y ∂(Step PositiveLength (ω t)).toMeasure) ∂μ := by
      exact PathMeasureTransitionIntegral (Step PositiveLength) (RLSInit n) t EventDecrease
    rw [TransitionIntegral]
    have ConditionalAverage : ∀ x : Bits n,
        (∫ y, EventDecrease x y ∂(Step PositiveLength x).toMeasure) =
          if Potential x = s then s / (n : ℝ) else 0 := by
      intro x
      unfold EventDecrease
      by_cases CurrentPotential : Potential x = s
      · simp only [if_pos CurrentPotential]
        rw [OneStepDrift PositiveLength x, CurrentPotential]
      · simp only [if_neg CurrentPotential, integral_zero]
    have AverageAsIndicator :
        (fun ω : Trajectory n =>
          ∫ y, EventDecrease (ω t) y ∂(Step PositiveLength (ω t)).toMeasure) =
            Event.indicator (fun _ => s / (n : ℝ)) := by
      funext ω
      rw [ConditionalAverage]
      rfl
    rw [AverageAsIndicator, integral_indicator_const _ EventMeasurable]
    rfl
  change (∫ ω in Event, X t ω - X (t + 1) ω ∂μ) / (μ Event).toReal = _
  rw [Numerator]
  have EventRealNonzero : (μ Event).toReal ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.toReal_pos EventPositive.ne' (measure_ne_top μ Event)
  exact mul_div_cancel_left₀ (s / (n : ℝ)) EventRealNonzero

/-- Supported successors are complete coordinate updates, so an optimal
parent retains zero potential. -/
theorem PotentialZeroIsAbsorbing {n : Nat} (PositiveLength : 0 < n) :
    ZeroIsAbsorbing (RunMeasure PositiveLength) (PotentialProcess n) := by
  have StepPreservesZero : ∀ x : Bits n,
      ∀ᵐ y ∂(Step PositiveLength x).toMeasure, Potential x = 0 → Potential y = 0 := by
    intro x
    have InRange :
        ∀ᵐ y ∂((UniformBitIndex n PositiveLength).toMeasure.map (Update x)),
          y ∈ Set.range (Update x) := by
      apply ae_map_mem_range
      exact (Set.to_countable _).measurableSet
    rw [PMF.toMeasure_map (Update x) (UniformBitIndex n PositiveLength)
      (measurable_of_finite _)] at InRange
    rw [Step, RLSStepEqUniformUpdate]
    filter_upwards [InRange] with y PossibleUpdate
    intro ParentZero
    obtain ⟨i, UpdateEq⟩ := PossibleUpdate
    rw [← UpdateEq]
    exact UpdatePreservesZero x i ParentZero
  intro t
  exact PathMeasureFollowsTransition (Step PositiveLength) (RLSInit n)
    (fun x y => Potential x = 0 → Potential y = 0) StepPreservesZero t

/-- Hitting zero potential is exactly hitting the formal OneMax goal. -/
theorem ZeroHittingTimeEqRuntime {n : Nat} (Path : Trajectory n) :
    ZeroHittingTime (PotentialProcess n) Path = FirstHittingTime IsTarget Path := by
  classical
  unfold ZeroHittingTime FirstHittingTime hittingAfter
  change (if ∃ j, 0 ≤ j ∧ Potential (Path j) = 0 then
    ((sInf {j : Nat | 0 ≤ j ∧ Potential (Path j) = 0} : Nat) : WithTop Nat) else ⊤) =
      if ∃ j, 0 ≤ j ∧ IsTarget (Path j) then
        ((sInf {j : Nat | 0 ≤ j ∧ IsTarget (Path j)} : Nat) : WithTop Nat) else ⊤
  simp only [PotentialEqZeroIffTarget]

/-- An initially optimal trajectory hits at time zero, including the
all-ones outcome under uniform initialization. -/
theorem InitialOptimalRuntimeZero {n : Nat} (Path : Trajectory n)
    (InitialOptimal : Path 0 = AllOnes n) :
    FirstHittingTime IsTarget Path = 0 := by
  apply (FirstHittingTimeEqZeroIff IsTarget Path).mpr
  exact (IsTargetIffEqAllOnes (Path 0)).mpr InitialOptimal

/-- With only `n>0`, uniformly initialized RLS has expected runtime at most
`n²/2`. Drift and the initial mean are proved internally, not assumed. -/
theorem UniformRuntimeUpperBound {n : Nat} (PositiveLength : 0 < n) :
    ExpectedUniformRuntime PositiveLength ≤ ENNReal.ofReal ((n : ℝ) ^ 2 / 2) := by
  classical
  let μ := RunMeasure PositiveLength
  let X := PotentialProcess n
  let S : Finset ℝ := (Finset.range (n + 1)).image (fun k : Nat => (k : ℝ))
  let Delta : ℝ := 1 / (n : ℝ)
  have CoordinatesMeasurable : ∀ t, Measurable (X t) := by
    intro t
    exact (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply t)
  have ZeroInS : (0 : ℝ) ∈ S := by
    apply Finset.mem_image.mpr
    exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), Nat.cast_zero⟩
  have NonnegativeValues : ∀ s ∈ S, (0 : ℝ) ≤ s := by
    intro s InS
    obtain ⟨k, _InRange, CastEq⟩ := Finset.mem_image.mp InS
    rw [← CastEq]
    exact Nat.cast_nonneg k
  have ValuesInS : ∀ t Path, X t Path ∈ S := by
    intro t Path
    apply Finset.mem_image.mpr
    refine ⟨ZeroCount (Path t), ?_, rfl⟩
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.sub_le n (OneMax (Path t)))
  have Absorbing : ZeroIsAbsorbing μ X := by
    exact PotentialZeroIsAbsorbing PositiveLength
  have LengthPositive : (0 : ℝ) < (n : ℝ) := by
    exact Nat.cast_pos.mpr PositiveLength
  have DeltaPositive : 0 < Delta := by
    exact one_div_pos.mpr LengthPositive
  -- A nonzero integer zero count is at least one, giving drift at least 1/n.
  have DriftLowerBound : ∀ (t : Nat) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta ≤ StateDrift μ X t s := by
    intro t s InS Nonzero EventPositive
    have ExactDrift : StateDrift μ X t s = s / (n : ℝ) := by
      exact ConditionalDrift PositiveLength t s EventPositive
    obtain ⟨k, _InRange, CastEq⟩ := Finset.mem_image.mp InS
    have IndexNonzero : k ≠ 0 := by
      intro IndexZero
      apply Nonzero
      rw [← CastEq, IndexZero, Nat.cast_zero]
    have StateAtLeastOne : (1 : ℝ) ≤ s := by
      rw [← CastEq]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr IndexNonzero
    rw [ExactDrift]
    exact div_le_div_of_nonneg_right StateAtLeastOne LengthPositive.le
  have BoundFromDrift :
      ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal (ExpectedValue μ (X 0) / Delta) := by
    exact AdditiveDriftUpperBound μ X S Delta CoordinatesMeasurable ZeroInS
      NonnegativeValues ValuesInS Absorbing DeltaPositive DriftLowerBound
  have InitialMean : ExpectedValue μ (X 0) = (n : ℝ) / 2 := by
    exact InitialExpectation PositiveLength
  have BoundValue : ExpectedValue μ (X 0) / Delta = (n : ℝ) ^ 2 / 2 := by
    rw [InitialMean]
    change ((n : ℝ) / 2) / (1 / (n : ℝ)) = (n : ℝ) ^ 2 / 2
    rw [one_div, div_inv_eq_mul]
    ring
  have RuntimeAsZeroHitting :
      ExpectedUniformRuntime PositiveLength = ExpectedZeroHittingTime μ X := by
    unfold ExpectedUniformRuntime ExpectedHittingTime ExpectedZeroHittingTime
    apply lintegral_congr
    intro Path
    rw [ZeroHittingTimeEqRuntime]
    rfl
  rw [RuntimeAsZeroHitting]
  rw [BoundValue] at BoundFromDrift
  exact BoundFromDrift

end
end ECTheoryLib.Analysis.RLSOnOneMax
