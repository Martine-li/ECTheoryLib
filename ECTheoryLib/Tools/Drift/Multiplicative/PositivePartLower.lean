import ECTheoryLib.Tools.Drift.MultiplicativeLower
import ECTheoryLib.Tools.Drift.NonabsorbingAdditive
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! Positive-part logarithmic decrease permits genuine upward moves.
Source counterpart: Lengler, equation2.13, printed115. The decreasing
branch reuses the existing logarithmic comparison. -/
namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- The logarithmic drop is controlled by positive-part decrease and a
closed large-drop indicator, with no ordering premise on the successor. -/
theorem LogDriftPotentialDifferenceUpperPositivePart (smin β s r : ℝ)
    (MinimumPositive : 0 < smin) (BetaLessOne : β < 1)
    (LowerS : smin ≤ s) (RangeR : r = 0 ∨ smin ≤ r) :
    MultiplicativeDriftPotential smin 1 s - MultiplicativeDriftPotential smin 1 r ≤
      max (s-r) 0 / ((1-β)*s) +
        MultiplicativeDriftPotential smin 1 s * (if β*s ≤ s-r then 1 else 0) := by
  by_cases Down : r ≤ s
  · rw [max_eq_left (sub_nonneg.mpr Down)]
    exact LogDriftPotentialDifferenceUpper smin β s r MinimumPositive BetaLessOne LowerS RangeR Down
  · have Up : s ≤ r := (lt_of_not_ge Down).le
    have PositiveS : 0 < s := MinimumPositive.trans_le LowerS
    have PositiveR : 0 < r := PositiveS.trans_le Up
    have PotentialLe : MultiplicativeDriftPotential smin 1 s ≤
        MultiplicativeDriftPotential smin 1 r := by
      simp only [MultiplicativeDriftPotential, if_neg PositiveS.ne', if_neg PositiveR.ne', div_one]
      have LogLe := Real.log_le_log (div_pos PositiveS MinimumPositive)
        (div_le_div_of_nonneg_right Up MinimumPositive.le)
      linarith
    have NonnegativeRatio : 0 ≤ max (s-r) 0 / ((1-β)*s) :=
      div_nonneg (le_max_right _ _) (mul_pos (sub_pos.mpr BetaLessOne) PositiveS).le
    have NonnegativeLarge : 0 ≤ MultiplicativeDriftPotential smin 1 s *
        (if β*s ≤ s-r then 1 else 0) := by
      apply mul_nonneg (LogDriftPotentialPositive smin s MinimumPositive LowerS).le
      split_ifs <;> norm_num
    exact (sub_nonpos.mpr PotentialLe).trans (add_nonneg NonnegativeRatio NonnegativeLarge)

/-- The zero-safe comparison also holds at current zero; leaving the goal
can only give a nonpositive transformed decrease. -/
theorem LogDriftPotentialDifferenceUpperPositivePartIncludingZero (smin β s r : ℝ)
    (MinimumPositive : 0 < smin) (BetaLessOne : β < 1)
    (RangeS : s = 0 ∨ smin ≤ s) (RangeR : r = 0 ∨ smin ≤ r) :
    MultiplicativeDriftPotential smin 1 s - MultiplicativeDriftPotential smin 1 r ≤
      max (s-r) 0 / ((1-β)*s) +
        MultiplicativeDriftPotential smin 1 s * (if β*s ≤ s-r then 1 else 0) := by
  rcases RangeS with Zero | Lower
  · rw [Zero]
    have NextNonnegative : 0 ≤ MultiplicativeDriftPotential smin 1 r := by
      rcases RangeR with ZeroR | LowerR
      · simp [ZeroR, MultiplicativeDriftPotential]
      · exact (LogDriftPotentialPositive smin r MinimumPositive LowerR).le
    simpa [MultiplicativeDriftPotential] using neg_nonpos.mpr NextNonnegative
  · exact LogDriftPotentialDifferenceUpperPositivePart smin β s r
      MinimumPositive BetaLessOne Lower RangeR

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem FiniteTwoObservationIntegrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (A B : Ω → ℝ) (S : Finset ℝ) (f : ℝ → ℝ → ℝ)
    (ObservableMeasurable : Measurable (fun ω => f (A ω) (B ω)))
    (ValuesA : ∀ ω, A ω ∈ S) (ValuesB : ∀ ω, B ω ∈ S) :
    Integrable (fun ω => f (A ω) (B ω)) μ := by
  classical
  apply FiniteStateIntegrable μ _ (S.biUnion (fun a => S.image (f a))) ObservableMeasurable
  exact ae_of_all μ (fun ω => Finset.mem_biUnion.mpr
    ⟨A ω, ValuesA ω, Finset.mem_image.mpr ⟨B ω, ValuesB ω, rfl⟩⟩)

/-- Complete-history control of the zero-safe logarithmic decrease from
positive-part drift and closed large jumps, without monotone trajectories. -/
theorem LogPotentialConditionalDecreaseOfPositivePart (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin β δ : ℝ)
    (MinimumPositive : 0 < smin) (BetaLessOne : β < 1) (DeltaNonnegative : 0 ≤ δ)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (t : ℕ)
    (PositivePartDrift : ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun u => max (X t u-X (t+1) u) 0 | F t]) ω ≤ δ*X t ω)
    (LargeJump : ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[(RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)) | F t]) ω ≤
        β*δ/(1+Real.log (X t ω/smin))) :
    ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun u => MultiplicativeDriftPotential smin 1 (X t u)-
        MultiplicativeDriftPotential smin 1 (X (t+1) u) | F t]) ω ≤
          δ*(1+β)/(1-β) := by
  classical
  let g := MultiplicativeDriftPotential smin 1
  let D : Ω → ℝ := fun ω => max (X t ω-X (t+1) ω) 0
  let C : Ω → ℝ := fun ω => ((1-β)*X t ω)⁻¹
  let I : Ω → ℝ := fun ω => if β*X t ω ≤ X t ω-X (t+1) ω then 1 else 0
  have IndicatorFormula : I = (RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp [I, RelativeDecreaseEvent, Set.indicator_apply]
  have LargeJumpI : ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[I | F t]) ω ≤ β*δ/(1+Real.log (X t ω/smin)) := by
    rw [IndicatorFormula]
    exact LargeJump
  have CoordinatesMeasurable (j : ℕ) : Measurable (X j) := AdaptedX.measurable
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) S (CoordinatesMeasurable j) (ae_of_all μ (Values j))
  have IntegrableG (j : ℕ) : Integrable (fun ω => g (X j ω)) μ :=
    FiniteStateCompositionIntegrable μ (X j) S g (CoordinatesMeasurable j) (Values j)
  have IntegrableDiff := (IntegrableG t).sub (IntegrableG (t+1))
  have MeasurableG : Measurable (fun ω => g (X t ω)) :=
    FiniteStateCompositionMeasurable (X t) S g (CoordinatesMeasurable t) (Values t)
  have AdaptedG : StronglyMeasurable[F t] (fun ω => g (X t ω)) :=
    (@FiniteStateCompositionMeasurable Ω (F t) (X t) S g (AdaptedX t) (Values t)).stronglyMeasurable
  have AdaptedC : StronglyMeasurable[F t] C :=
    ((measurable_const.mul (AdaptedX t)).inv).stronglyMeasurable
  have MeasurableC : Measurable C :=
    ((measurable_const.mul (CoordinatesMeasurable t)).inv)
  have MeasurableD : Measurable D :=
    ((CoordinatesMeasurable t).sub (CoordinatesMeasurable (t+1))).max measurable_const
  have IntegrableD : Integrable D μ := ((IntegrableX t).sub (IntegrableX (t+1))).pos_part
  have MeasurableI : Measurable I := by
    rw [IndicatorFormula]
    exact measurable_const.indicator (RelativeDecreaseEventMeasurable X β t CoordinatesMeasurable)
  have IntegrableI : Integrable I μ := by
    rw [IndicatorFormula]
    exact (integrable_const 1).indicator (RelativeDecreaseEventMeasurable X β t CoordinatesMeasurable)
  have IntegrableCD : Integrable (C*D) μ :=
    FiniteTwoObservationIntegrable μ (X t) (X (t+1)) S
      (fun s r => ((1-β)*s)⁻¹ * max (s-r) 0)
      (MeasurableC.mul MeasurableD) (Values t) (Values (t+1))
  have IntegrableGI : Integrable ((fun ω => g (X t ω))*I) μ :=
    FiniteTwoObservationIntegrable μ (X t) (X (t+1)) S
      (fun s r => g s * (if β*s ≤ s-r then 1 else 0))
      (MeasurableG.mul MeasurableI) (Values t) (Values (t+1))
  have Compare : (fun ω => g (X t ω)-g (X (t+1) ω)) ≤ᵐ[μ]
      (C*D + (fun ω => g (X t ω))*I) := by
    apply ae_of_all
    intro ω
    have Bound := LogDriftPotentialDifferenceUpperPositivePartIncludingZero smin β
      (X t ω) (X (t+1) ω) MinimumPositive BetaLessOne
      (StateLowerBound _ (Values t ω)) (StateLowerBound _ (Values (t+1) ω))
    simpa only [g, C, D, I, Pi.add_apply, Pi.mul_apply, div_eq_mul_inv, mul_comm] using Bound
  have MeanCompare := condExp_mono (m := F t) IntegrableDiff (IntegrableCD.add IntegrableGI) Compare
  have Expand := condExp_add IntegrableCD IntegrableGI (F t)
  have PullD := condExp_mul_of_stronglyMeasurable_left AdaptedC IntegrableCD IntegrableD
  have PullI := condExp_mul_of_stronglyMeasurable_left AdaptedG IntegrableGI IntegrableI
  have Scalar : δ/(1-β)+β*δ ≤ δ*(1+β)/(1-β) := by
    apply (le_div_iff₀ (sub_pos.mpr BetaLessOne)).mpr
    rw [add_mul, div_mul_cancel₀ _ (sub_pos.mpr BetaLessOne).ne']
    nlinarith [mul_nonneg DeltaNonnegative (sq_nonneg β)]
  filter_upwards [MeanCompare, Expand, PullD, PullI, PositivePartDrift, LargeJumpI] with
    ω Comparison Expansion PullDecrease PullIndicator DriftBound JumpBound
  intro Active
  have PositiveS : 0 < X t ω :=
    MinimumPositive.trans_le ((StateLowerBound _ (Values t ω)).resolve_left Active)
  have PositiveDenominator : 0 < (1-β)*X t ω := mul_pos (sub_pos.mpr BetaLessOne) PositiveS
  have PositiveG : 0 < g (X t ω) := LogDriftPotentialPositive smin _ MinimumPositive
    ((StateLowerBound _ (Values t ω)).resolve_left Active)
  have Rewritten : (μ[fun u => g (X t u)-g (X (t+1) u) | F t]) ω ≤
      C ω*(μ[D | F t]) ω+g (X t ω)*(μ[I | F t]) ω := by
    calc
      _ ≤ (μ[C*D+(fun u => g (X t u))*I | F t]) ω := Comparison
      _ = _ := by rw [Expansion, Pi.add_apply, PullDecrease, PullIndicator]; rfl
  have First := mul_le_mul_of_nonneg_left (DriftBound Active) (inv_pos.mpr PositiveDenominator).le
  have Second := mul_le_mul_of_nonneg_left (JumpBound Active) PositiveG.le
  have FirstTerm : C ω*(δ*X t ω) = δ/(1-β) := by
    dsimp [C]
    field_simp
  have PotentialFormula : g (X t ω) = 1+Real.log (X t ω/smin) := by
    simp only [g, MultiplicativeDriftPotential, if_neg Active, div_one]
  have SecondTerm : g (X t ω)*(β*δ/(1+Real.log (X t ω/smin))) = β*δ := by
    rw [← PotentialFormula]
    field_simp
  change C ω*(μ[D | F t]) ω ≤ C ω*(δ*X t ω) at First
  rw [FirstTerm] at First
  rw [SecondTerm] at Second
  exact Rewritten.trans ((add_le_add First Second).trans Scalar)

/-- Multiplicative lower drift allowing both positive rebounds and goal
restarts. The initial potential is zero-safe and runtime may be infinite. -/
theorem MultiplicativeDriftLowerBoundOfPositivePart (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin β δ : ℝ)
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (BetaNonnegative : 0 ≤ β) (BetaAtMostOne : β ≤ 1) (DeltaPositive : 0 < δ)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (PositivePartDrift : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun u => max (X t u-X (t+1) u) 0 | F t]) ω ≤ δ*X t ω)
    (LargeJump : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[(RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)) | F t]) ω ≤
        β*δ/(1+Real.log (X t ω/smin))) :
    ENNReal.ofReal (((1-β)/(1+β))*(ExpectedValue μ
      (fun ω => MultiplicativeDriftPotential smin 1 (X 0 ω))/δ)) ≤
        ExpectedZeroHittingTime μ X := by
  classical
  by_cases BetaOne : β = 1
  · rw [BetaOne, sub_self, zero_div, zero_mul, ENNReal.ofReal_zero]
    exact bot_le
  have BetaLessOne : β < 1 := lt_of_le_of_ne BetaAtMostOne BetaOne
  let g := MultiplicativeDriftPotential smin 1
  let Y : ℕ → Ω → ℝ := fun t ω => g (X t ω)
  let c := δ*(1+β)/(1-β)
  have PositiveC : 0 < c :=
    div_pos (mul_pos DeltaPositive (by linarith)) (sub_pos.mpr BetaLessOne)
  have PotentialZero : g 0 = 0 := by simp [g, MultiplicativeDriftPotential]
  have ZeroIff (t : ℕ) (ω : Ω) : Y t ω = 0 ↔ X t ω = 0 :=
    LogDriftPotentialZeroIff smin (X t ω) MinimumPositive (StateLowerBound _ (Values t ω))
  have AdaptedY : Adapted F Y := by
    intro t
    exact @FiniteStateCompositionMeasurable Ω (F t) (X t) S g (AdaptedX t) (Values t)
  have ValuesY (t : ℕ) (ω : Ω) : Y t ω ∈ S.image g :=
    Finset.mem_image.mpr ⟨X t ω, Values t ω, rfl⟩
  have NonnegativeY : ∀ y ∈ S.image g, 0 ≤ y := by
    intro y InImage
    obtain ⟨s, InS, rfl⟩ := Finset.mem_image.mp InImage
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero, PotentialZero]
    · exact (LogDriftPotentialPositive smin s MinimumPositive Lower).le
  have DriftY : ∀ t, ∀ᵐ ω ∂μ, Y t ω ≠ 0 →
      (μ[fun u => Y t u-Y (t+1) u | F t]) ω ≤ c := by
    intro t
    have Local := LogPotentialConditionalDecreaseOfPositivePart μ X F AdaptedX S smin β δ
      MinimumPositive BetaLessOne DeltaPositive.le StateLowerBound Values t
      (PositivePartDrift t) (LargeJump t)
    filter_upwards [Local] with ω Bound
    intro NonzeroY
    exact Bound (fun Zero => NonzeroY ((ZeroIff t ω).mpr Zero))
  have Bound := AdditiveDriftLowerBoundNonabsorbing μ Y F AdaptedY (S.image g) c
    (Finset.mem_image.mpr ⟨0, ZeroInS, PotentialZero⟩) NonnegativeY ValuesY PositiveC DriftY
  have HittingTimeEquality : ZeroHittingTime Y = ZeroHittingTime X := by
    funext ω
    unfold ZeroHittingTime FirstHittingTime hittingAfter
    simp only [Set.mem_ofPred_eq, ZeroIff]
  have RuntimeEquality : ExpectedZeroHittingTime μ Y = ExpectedZeroHittingTime μ X := by
    unfold ExpectedZeroHittingTime
    rw [HittingTimeEquality]
  rw [RuntimeEquality] at Bound
  have Coefficient : ExpectedValue μ (Y 0)/c =
      ((1-β)/(1+β))*(ExpectedValue μ (Y 0)/δ) := by
    dsimp [c]
    field_simp
  rw [Coefficient] at Bound
  exact Bound

private theorem CondExpEqOnMeasurableLevel (μ : Measure Ω) (m : MeasurableSpace Ω)
    (A : Set Ω) (MeasurableA : MeasurableSet[m] A) (f h : Ω → ℝ)
    (IntegrableF : Integrable f μ) (IntegrableH : Integrable h μ)
    (EqualOn : ∀ ω ∈ A, f ω = h ω) :
    ∀ᵐ ω ∂μ, ω ∈ A → (μ[f | m]) ω = (μ[h | m]) ω := by
  have EqualIndicators : A.indicator f = A.indicator h := by
    funext ω
    by_cases Member : ω ∈ A
    · simp only [Set.indicator_of_mem Member, EqualOn ω Member]
    · simp only [Set.indicator_of_notMem Member]
  have Same := congrArg (fun Z : Ω → ℝ => μ[Z | m]) EqualIndicators
  filter_upwards [condExp_indicator IntegrableF MeasurableA,
    condExp_indicator IntegrableH MeasurableA] with ω Left Right
  intro Member
  have AtPoint := congrFun Same ω
  rw [Left, Right, Set.indicator_of_mem Member, Set.indicator_of_mem Member] at AtPoint
  exact AtPoint

/-- The source's every-reference-level family implies the diagonal positive
part bound. Localization on the measurable current level is essential. -/
theorem PositivePartDriftOfReferenceLevels (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (δ : ℝ) (Values : ∀ t ω, X t ω ∈ S)
    (ReferenceDrift : ∀ t r, r ∈ S → r ≠ 0 → ∀ᵐ ω ∂μ,
      X t ω ≠ 0 → r ≤ X t ω →
        (μ[fun u => max (r-X (t+1) u) 0 | F t]) ω ≤ δ*r) :
    ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun u => max (X t u-X (t+1) u) 0 | F t]) ω ≤ δ*X t ω := by
  classical
  intro t
  have CoordinatesMeasurable (j : ℕ) : Measurable (X j) := AdaptedX.measurable
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) S (CoordinatesMeasurable j) (ae_of_all μ (Values j))
  have IntegrableD : Integrable (fun u => max (X t u-X (t+1) u) 0) μ :=
    ((IntegrableX t).sub (IntegrableX (t+1))).pos_part
  have PerLevel (r : {r : ℝ // r ∈ S}) : ∀ᵐ ω ∂μ,
      X t ω = r.val → X t ω ≠ 0 →
        (μ[fun u => max (X t u-X (t+1) u) 0 | F t]) ω ≤ δ*X t ω := by
    by_cases ZeroR : r.val = 0
    · exact ae_of_all μ (fun _ Equal Active => False.elim (Active (Equal.trans ZeroR)))
    have LevelMeasurable : MeasurableSet[F t] {ω | X t ω = r.val} :=
      measurableSet_eq_fun (AdaptedX t) measurable_const
    have IntegrableReference : Integrable (fun u => max (r.val-X (t+1) u) 0) μ :=
      ((integrable_const r.val).sub (IntegrableX (t+1))).pos_part
    have Agreement := CondExpEqOnMeasurableLevel μ (F t) {ω | X t ω = r.val}
      LevelMeasurable (fun u => max (X t u-X (t+1) u) 0)
      (fun u => max (r.val-X (t+1) u) 0) IntegrableD IntegrableReference (by
        intro ω Member
        change X t ω = r.val at Member
        rw [Member])
    filter_upwards [Agreement, ReferenceDrift t r.val r.property ZeroR] with ω EqualMeans Bound
    intro Equal Active
    rw [EqualMeans Equal]
    have AtReference := Bound Active Equal.ge
    simpa only [Equal] using AtReference
  have AllLevels : ∀ᵐ ω ∂μ, ∀ r : {r : ℝ // r ∈ S},
      X t ω = r.val → X t ω ≠ 0 →
        (μ[fun u => max (X t u-X (t+1) u) 0 | F t]) ω ≤ δ*X t ω :=
    (ae_all_iff).mpr PerLevel
  filter_upwards [AllLevels] with ω Bound
  exact Bound ⟨X t ω, Values t ω⟩ rfl

/-- The book's reference-level positive-part condition removes monotonicity,
while the closed large-jump condition is retained on the same filtration. -/
theorem MultiplicativeDriftLowerBoundOfReferenceLevels (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin β δ : ℝ)
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (BetaNonnegative : 0 ≤ β) (BetaAtMostOne : β ≤ 1) (DeltaPositive : 0 < δ)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (ReferenceDrift : ∀ t r, r ∈ S → r ≠ 0 → ∀ᵐ ω ∂μ,
      X t ω ≠ 0 → r ≤ X t ω →
        (μ[fun u => max (r-X (t+1) u) 0 | F t]) ω ≤ δ*r)
    (LargeJump : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[(RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)) | F t]) ω ≤
        β*δ/(1+Real.log (X t ω/smin))) :
    ENNReal.ofReal (((1-β)/(1+β))*(ExpectedValue μ
      (fun ω => MultiplicativeDriftPotential smin 1 (X 0 ω))/δ)) ≤
        ExpectedZeroHittingTime μ X :=
  MultiplicativeDriftLowerBoundOfPositivePart μ X F AdaptedX S smin β δ ZeroInS MinimumPositive
    BetaNonnegative BetaAtMostOne DeltaPositive StateLowerBound Values
    (PositivePartDriftOfReferenceLevels μ X F AdaptedX S δ Values ReferenceDrift) LargeJump

/-- The displayed log-mean formula additionally requires almost surely
positive initialization. Initial zeros use the preceding zero-safe theorem. -/
theorem MultiplicativeDriftLowerBoundOfPositivePartPositiveInitial
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin β δ : ℝ)
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (BetaNonnegative : 0 ≤ β) (BetaAtMostOne : β ≤ 1) (DeltaPositive : 0 < δ)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ t ω, X t ω ∈ S)
    (PositivePartDrift : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun u => max (X t u-X (t+1) u) 0 | F t]) ω ≤ δ*X t ω)
    (LargeJump : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[(RelativeDecreaseEvent X β t).indicator (fun _ => (1 : ℝ)) | F t]) ω ≤
        β*δ/(1+Real.log (X t ω/smin)))
    (InitialPositive : ∀ᵐ ω ∂μ, X 0 ω ≠ 0) :
    ENNReal.ofReal (((1-β)/(1+β))*((1+ExpectedValue μ
      (fun ω => Real.log (X 0 ω/smin)))/δ)) ≤ ExpectedZeroHittingTime μ X := by
  have Bound := MultiplicativeDriftLowerBoundOfPositivePart μ X F AdaptedX S smin β δ ZeroInS
    MinimumPositive BetaNonnegative BetaAtMostOne DeltaPositive StateLowerBound Values
    PositivePartDrift LargeJump
  have LogIntegrable := FiniteStateCompositionIntegrable μ (X 0) S
    (fun s => Real.log (s/smin)) (show Measurable (X 0) from AdaptedX.measurable) (Values 0)
  have InitialMean : ExpectedValue μ (fun ω => MultiplicativeDriftPotential smin 1 (X 0 ω)) =
      1+ExpectedValue μ (fun ω => Real.log (X 0 ω/smin)) := by
    unfold ExpectedValue
    have Formula : (fun ω => MultiplicativeDriftPotential smin 1 (X 0 ω)) =ᵐ[μ]
        (fun ω => 1+Real.log (X 0 ω/smin)) := by
      filter_upwards [InitialPositive] with ω Active
      simp only [MultiplicativeDriftPotential, if_neg Active, div_one]
    rw [integral_congr_ae Formula, integral_add (integrable_const _) LogIntegrable,
      integral_const, probReal_univ, one_smul]
  rw [InitialMean] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Drift

