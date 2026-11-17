import ECTheoryLib.Probability.Concentration.AzumaHoeffding
import ECTheoryLib.Probability.HittingTimes.StoppedIncrement

/-!
Finite maximal Azuma with a fixed additive threshold.
Reuse the existing stopped process, retaining the hitting step and random initial value.
-/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

/-- Fixed additive upper deviation at any positive prefix of a finite conditional sum. -/
theorem BoundedConditionalSumMaximalUpperTail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ) (c : ℕ → ℝ≥0) (horizon : ℕ)
    (NextObservable : ∀ i < horizon, StronglyMeasurable[F (i + 1)] (Z i))
    (Bounded : ∀ i < horizon, ∀ᵐ ω ∂P, |Z i ω| ≤ (c i : ℝ))
    (Centered : ∀ i < horizon, P[Z i | F i] =ᵐ[P] (fun _ => 0))
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    P.real {ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ horizon ∧
        threshold ≤ ∑ i ∈ Finset.range k, Z i ω} ≤
      Real.exp (-threshold ^ 2 / (2 * ∑ i ∈ Finset.range horizon, (c i : ℝ) ^ 2)) := by
  classical
  by_cases Zero : threshold = 0
  · subst threshold
    simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero]
    exact measureReal_le_one
  have Positive : 0 < threshold := lt_of_le_of_ne Nonnegative (Ne.symm Zero)
  let S : ℕ → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range (min t horizon), Z i ω
  have AdaptedS : Adapted F S := by
    intro t
    have Observable : StronglyMeasurable[F t] (S t) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro i Member
      have Inside : i < min t horizon := Finset.mem_range.mp Member
      exact (NextObservable i (lt_of_lt_of_le Inside (Nat.min_le_right _ _))).mono
        (F.mono (Nat.succ_le_of_lt (lt_of_lt_of_le Inside (Nat.min_le_left _ _))))
    exact Observable.measurable
  let Y := StopAtFirstHit (fun s : ℝ => threshold ≤ s) S
  have AdaptedY : Adapted F Y :=
    StopAtFirstHitAdapted S F AdaptedS _ measurableSet_Ici
  have Initial (ω : Ω) : Y 0 ω = 0 := by
    simpa only [Y, S, Nat.zero_min, Finset.range_zero, Finset.sum_empty] using
      (StopAtFirstHitInitial (fun s : ℝ => threshold ≤ s) S ω)
  have SumStep (i : ℕ) (Within : i < horizon) (ω : Ω) :
      S (i + 1) ω - S i ω = Z i ω := by
    dsimp only [S]
    rw [Nat.min_eq_left (Nat.succ_le_of_lt Within), Nat.min_eq_left Within.le,
      Finset.sum_range_succ]
    ring
  have Increment (i : ℕ) (Within : i < horizon) (ω : Ω) :
      Y (i + 1) ω - Y i ω = if Y i ω < threshold then Z i ω else 0 := by
    by_cases Before : Y i ω < threshold
    · rw [if_pos Before]
      have Same := StopAtFirstHitStepBefore (fun s : ℝ => threshold ≤ s) S i ω
        (not_le_of_gt Before)
      dsimp only [Y]
      rw [Same.1, Same.2]
      exact SumStep i Within ω
    · rw [if_neg Before]
      dsimp only [Y]
      rw [StopAtFirstHitFrozenStep (fun s : ℝ => threshold ≤ s) S i ω
        (le_of_not_gt Before), sub_self]
  have NextStopped (i : ℕ) : StronglyMeasurable[F (i + 1)]
      (fun ω => Y (i + 1) ω - Y i ω) :=
    (AdaptedY (i + 1)).stronglyMeasurable.sub
      ((AdaptedY i).stronglyMeasurable.mono (F.mono (Nat.le_succ i)))
  have BoundedStopped (i : ℕ) (Within : i < horizon) :
      ∀ᵐ ω ∂P, |Y (i + 1) ω - Y i ω| ≤ (c i : ℝ) := by
    filter_upwards [Bounded i Within] with ω Bound
    rw [Increment i Within ω]
    split_ifs
    · exact Bound
    · simpa only [abs_zero] using (c i).coe_nonneg
  have CenteredStopped (i : ℕ) (Within : i < horizon) :
      P[fun ω => Y (i + 1) ω - Y i ω | F i] =ᵐ[P] (fun _ => 0) := by
    let B : Set Ω := {ω | Y i ω < threshold}
    have MeasurableB : MeasurableSet[F i] B :=
      measurableSet_lt (AdaptedY i) measurable_const
    have Equal : (fun ω => Y (i + 1) ω - Y i ω) = B.indicator (Z i) := by
      funext ω
      rw [Increment i Within ω]
      rfl
    have IntegrableZ : Integrable (Z i) P := by
      apply Integrable.of_mem_Icc (-(c i : ℝ)) (c i : ℝ)
        (((NextObservable i Within).mono (F.le (i + 1))).measurable.aemeasurable)
      filter_upwards [Bounded i Within] with ω Bound
      exact abs_le.mp Bound
    rw [Equal]
    have Conditional := condExp_indicator IntegrableZ MeasurableB
    filter_upwards [Conditional, Centered i Within] with ω ConditionalAt CenteredAt
    rw [ConditionalAt]
    by_cases Member : ω ∈ B
    · rw [Set.indicator_of_mem Member]
      exact CenteredAt
    · rw [Set.indicator_of_notMem Member]
  have Bound := BoundedConditionalSumUpperTail P F
    (fun i ω => Y (i + 1) ω - Y i ω) c horizon
    (fun i _ => NextStopped i) BoundedStopped CenteredStopped threshold Nonnegative
  have Telescope (ω : Ω) :
      (∑ i ∈ Finset.range horizon, (Y (i + 1) ω - Y i ω)) = Y horizon ω := by
    simpa only [Initial, sub_zero] using
      (Finset.sum_range_sub (fun i => Y i ω) horizon)
  simp only [Telescope] at Bound
  have Event : {ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ horizon ∧
      threshold ≤ ∑ i ∈ Finset.range k, Z i ω} = {ω | threshold ≤ Y horizon ω} := by
    ext ω
    change (∃ k : ℕ, 1 ≤ k ∧ k ≤ horizon ∧ threshold ≤ ∑ i ∈ Finset.range k, Z i ω) ↔
      threshold ≤ StopAtFirstHit (fun s : ℝ => threshold ≤ s) S horizon ω
    rw [StopAtFirstHitGoalIff (fun s : ℝ => threshold ≤ s) S horizon ω,
      FirstHittingTimeLeIff (fun s : ℝ => threshold ≤ s) (fun t => S t ω) horizon]
    constructor
    · rintro ⟨k, _, Before, Reached⟩
      refine ⟨k, Before, ?_⟩
      simpa only [S, Nat.min_eq_left Before] using Reached
    · rintro ⟨k, Before, Reached⟩
      have Nonzero : k ≠ 0 := by
        intro AtZero
        subst k
        have Bad : threshold ≤ 0 := by
          simpa only [S, Nat.zero_min, Finset.range_zero, Finset.sum_empty] using Reached
        exact (not_le_of_gt Positive) Bad
      refine ⟨k, Nat.one_le_iff_ne_zero.mpr Nonzero, Before, ?_⟩
      simpa only [S, Nat.min_eq_left Before] using Reached
  rw [Event]
  exact Bound

/-- Finite maximal Azuma for a martingale with an integrable, possibly random initial value. -/
theorem FiniteMartingaleAzumaMaximalUpperTail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (c : ℕ → ℝ≥0) (horizon : ℕ)
    (Observable : ∀ i ≤ horizon, StronglyMeasurable[F i] (X i))
    (IntegrableX : ∀ i ≤ horizon, Integrable (X i) P)
    (OneStepMean : ∀ i < horizon, P[X (i + 1) | F i] =ᵐ[P] X i)
    (Bounded : ∀ i < horizon, ∀ᵐ ω ∂P, |X (i + 1) ω - X i ω| ≤ (c i : ℝ))
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    P.real {ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ horizon ∧ threshold ≤ X k ω - X 0 ω} ≤
      Real.exp (-threshold ^ 2 / (2 * ∑ i ∈ Finset.range horizon, (c i : ℝ) ^ 2)) := by
  have NextObservable (i : ℕ) (Within : i < horizon) :
      StronglyMeasurable[F (i + 1)] (fun ω => X (i + 1) ω - X i ω) :=
    (Observable (i + 1) (Nat.succ_le_of_lt Within)).sub
      ((Observable i Within.le).mono (F.mono (Nat.le_succ i)))
  have Centered (i : ℕ) (Within : i < horizon) :
      P[fun ω => X (i + 1) ω - X i ω | F i] =ᵐ[P] (fun _ => 0) := by
    have Subtract := condExp_sub (IntegrableX (i + 1) (Nat.succ_le_of_lt Within))
      (IntegrableX i Within.le) (F i)
    have Now := condExp_of_stronglyMeasurable (F.le i)
      (Observable i Within.le) (IntegrableX i Within.le)
    filter_upwards [Subtract, OneStepMean i Within] with ω SubtractAt MeanAt
    calc
      _ = (P[X (i + 1) | F i]) ω - (P[X i | F i]) ω := SubtractAt
      _ = 0 := by rw [Now, MeanAt, sub_self]
  have Bound := BoundedConditionalSumMaximalUpperTail P F
    (fun i ω => X (i + 1) ω - X i ω) c horizon
    NextObservable Bounded Centered threshold Nonnegative
  have Telescope (k : ℕ) (ω : Ω) :
      (∑ i ∈ Finset.range k, (X (i + 1) ω - X i ω)) = X k ω - X 0 ω :=
    Finset.sum_range_sub (fun i => X i ω) k
  simpa only [Telescope] using Bound

end
end ECTheoryLib.Probability
