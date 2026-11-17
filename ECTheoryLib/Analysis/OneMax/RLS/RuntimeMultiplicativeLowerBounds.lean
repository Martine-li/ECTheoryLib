import ECTheoryLib.Tools.Drift.MultiplicativeLower
import ECTheoryLib.Analysis.OneMax.RLS.RuntimeLowerBounds

/-!
# Multiplicative lower drift for actual RLS on OneMax

The actual zero-count drop is zero or one. For beta=1/2 a large jump is
impossible above state two; at states one and two its probability is at
most the exact drift s/n. This verifies the rare-jump condition with
delta=8/n and gives n*(1+log k)/24 from k>0 zero bits.
For n>=8 these parameters also lie in the source's delta<=1 range.
The theorem proved in the library permits every delta>0, so this client
retains all positive lengths. The constant is conservative; stronger
variable-drift and exact harmonic results remain available.
Time counts mutation iterations, not initial evaluation cost.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift ProbabilityTheory
noncomputable section

/-- The actual conditional half-distance-jump probability satisfies Theorem 2.4.3 with δ=8/n. -/
theorem PathHalfDecreaseProbability {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n))
    (t : ℕ) (s : ℝ) (LowerS : 1 ≤ s)
    (PositiveEvent : 0 < PathMeasure (Step PositiveLength) Initial
      (StateEvent (fun t Path => Potential (Path t)) t s)) :
    EventConditionalExpectation (PathMeasure (Step PositiveLength) Initial)
      ((RelativeDecreaseEvent (fun t Path => Potential (Path t)) (1/2) t).indicator (fun _ => (1 : ℝ)))
      (StateEvent (fun t Path => Potential (Path t)) t s) ≤
        (1/2)*(8/(n : ℝ))/(1+Real.log (s/1)) := by
  classical
  let μ := PathMeasure (Step PositiveLength) Initial
  let X : ℕ → (ℕ → Bits n) → ℝ := fun t Path => Potential (Path t)
  let ν := cond μ (StateEvent X t s)
  let I := (RelativeDecreaseEvent X (1/2) t).indicator (fun _ => (1 : ℝ))
  have ConditionalProbability : IsProbabilityMeasure ν := cond_isProbabilityMeasure PositiveEvent.ne'
  have CoordinatesMeasurable (t : ℕ) : Measurable (X t) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply t)
  have PositiveS : 0 < s := lt_of_lt_of_le zero_lt_one LowerS
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have LogNonnegative : 0 ≤ Real.log s := Real.log_nonneg LowerS
  have PositiveDen : 0 < 1+Real.log s := by linarith
  have Binary : ∀ᵐ Path ∂ν, X t Path-X (t+1) Path=0 ∨ X t Path-X (t+1) Path=1 :=
    cond_absolutelyContinuous.ae_le (PathMeasureFollowsTransition (Step PositiveLength) Initial
      (fun x y => Potential x-Potential y=0 ∨ Potential x-Potential y=1)
      (StepPotentialDecreaseBinary PositiveLength) t)
  have Current : ∀ᵐ Path ∂ν, X t Path=s :=
    ae_cond_mem (StateEventMeasurable X t s (CoordinatesMeasurable t))
  have IndicatorIntegrable : Integrable I ν :=
    (integrable_const 1).indicator (RelativeDecreaseEventMeasurable X (1/2) t CoordinatesMeasurable)
  have CoordinateIntegrable (t : ℕ) : Integrable (X t) ν :=
    FiniteStateIntegrable ν (X t) (Finset.univ.image (Potential (n := n)))
      (CoordinatesMeasurable t) (ae_of_all _ (fun Path => Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩))
  have ExactDrift : (∫ Path, X t Path-X (t+1) Path ∂ν)=s/(n : ℝ) := by
    have Local (x : Bits n) : (∫ y, Potential x-Potential y ∂(Step PositiveLength x).toMeasure)=Potential x/(n : ℝ) :=
      OneStepDrift PositiveLength x
    have Bound := PathMeasureStateDrift (Step PositiveLength) Initial Potential (fun s => s/(n : ℝ))
      Local t s PositiveEvent
    rw [StateDrift, EventConditionalExpectationEqCondIntegral] at Bound
    exact Bound
  rw [EventConditionalExpectationEqCondIntegral, div_one]
  change (∫ Path, I Path ∂ν) ≤ (1/2)*(8/(n : ℝ))/(1+Real.log s)
  by_cases SmallState : s ≤ 2
  · have IndicatorLeDecrease : ∀ᵐ Path ∂ν, I Path ≤ X t Path-X (t+1) Path := by
      filter_upwards [Binary, Current] with Path Drop CurrentValue
      rcases Drop with ZeroDrop | OneDrop
      · have NotLarge : Path ∉ RelativeDecreaseEvent X (1/2) t := by
          change ¬ (1/2)*X t Path ≤ X t Path-X (t+1) Path
          rw [ZeroDrop, CurrentValue]
          nlinarith
        dsimp only [I]
        rw [Set.indicator_of_notMem NotLarge, ZeroDrop]
      · rw [OneDrop]
        by_cases Large : Path ∈ RelativeDecreaseEvent X (1/2) t
        · dsimp only [I]
          rw [Set.indicator_of_mem Large]
        · dsimp only [I]
          rw [Set.indicator_of_notMem Large]
          exact zero_le_one
    have MeanBound := integral_mono_ae IndicatorIntegrable
      ((CoordinateIntegrable t).sub (CoordinateIntegrable (t+1))) IndicatorLeDecrease
    change (∫ Path, I Path ∂ν) ≤ ∫ Path, X t Path-X (t+1) Path ∂ν at MeanBound
    rw [ExactDrift] at MeanBound
    apply MeanBound.trans
    have LogTwoLeOne : Real.log 2 ≤ 1 := by
      have Bound := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at Bound
      exact Bound
    have LogLeOne : Real.log s ≤ 1 := (Real.log_le_log PositiveS SmallState).trans LogTwoLeOne
    have ProductBound : s*(1+Real.log s) ≤ 4 := by
      have Bound := mul_le_mul SmallState (show 1+Real.log s ≤ 2 by linarith)
        PositiveDen.le (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at Bound
      exact Bound
    have RightValue : (1/2)*(8/(n : ℝ))/(1+Real.log s)=4/((n : ℝ)*(1+Real.log s)) := by
      field_simp
      norm_num
    rw [RightValue]
    apply (div_le_div_iff₀ PositiveN (mul_pos PositiveN PositiveDen)).mpr
    have Scaled := mul_le_mul_of_nonneg_left ProductBound PositiveN.le
    nlinarith
  · have IndicatorZero : I =ᵐ[ν] 0 := by
      filter_upwards [Binary, Current] with Path Drop CurrentValue
      have NotLarge : Path ∉ RelativeDecreaseEvent X (1/2) t := by
        change ¬ (1/2)*X t Path ≤ X t Path-X (t+1) Path
        rw [CurrentValue]
        rw [CurrentValue] at Drop
        rcases Drop with ZeroDrop | OneDrop
        · rw [ZeroDrop]
          nlinarith
        · rw [OneDrop]
          linarith
      simp only [I, Set.indicator_of_notMem NotLarge, Pi.zero_apply]
    rw [integral_congr_ae IndicatorZero]
    simp only [Pi.zero_apply, integral_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (div_nonneg (by norm_num) PositiveN.le)) PositiveDen.le

/-- A verified use of the rare-large-jump theorem on actual RLS, with β=1/2 and δ=8/n. -/
theorem RuntimeMultiplicativeLowerBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ENNReal.ofReal (((n : ℝ)/24)*(∫ x, MultiplicativeDriftPotential 1 1 (Potential x) ∂Initial.toMeasure)) ≤
      ExpectedHittingTime (Step PositiveLength) IsTarget Initial := by
  classical
  let μ := PathMeasure (Step PositiveLength) Initial
  let X : ℕ → (ℕ → Bits n) → ℝ := fun t Path => Potential (Path t)
  let S : Finset ℝ := insert 0 (Finset.univ.image (Potential (n := n)))
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have StateLower : ∀ s ∈ S, s=0 ∨ (1 : ℝ) ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | InImage
    · exact Or.inl Zero
    · obtain ⟨x, _InUniv, rfl⟩ := Finset.mem_image.mp InImage
      by_cases Zero : ZeroCount x=0
      · exact Or.inl (Nat.cast_eq_zero.mpr Zero)
      · right
        change (1 : ℝ) ≤ (ZeroCount x : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero
  have ValuesInS (t : ℕ) (Path : ℕ → Bits n) : X t Path ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩)
  have CoordinatesMeasurable (t : ℕ) : Measurable (X t) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply t)
  have Nonincreasing (t : ℕ) : ∀ᵐ Path ∂μ, X (t+1) Path ≤ X t Path :=
    PathMeasureFollowsTransition (Step PositiveLength) Initial
      (fun x y => Potential y ≤ Potential x) (StepPotentialNonincreasing PositiveLength) t
  have Drift (t : ℕ) (s : ℝ) (InS : s ∈ S) (Nonzero : s ≠ 0)
      (PositiveEvent : 0 < μ (StateEvent X t s)) : StateDrift μ X t s ≤ (8/(n : ℝ))*s := by
    have Local (x : Bits n) : (∫ y, Potential x-Potential y ∂(Step PositiveLength x).toMeasure)=Potential x/(n : ℝ) :=
      OneStepDrift PositiveLength x
    have Exact := PathMeasureStateDrift (Step PositiveLength) Initial Potential (fun s => s/(n : ℝ))
      Local t s PositiveEvent
    rw [Exact]
    have NonnegativeS : 0 ≤ s := zero_le_one.trans ((StateLower s InS).resolve_left Nonzero)
    have RatioNonnegative : 0 ≤ s/(n : ℝ) := div_nonneg NonnegativeS PositiveN.le
    have Rearrange : (8/(n : ℝ))*s=8*(s/(n : ℝ)) := by ring
    rw [Rearrange]
    linarith
  have LargeJump (t : ℕ) (s : ℝ) (InS : s ∈ S) (Nonzero : s ≠ 0)
      (PositiveEvent : 0 < μ (StateEvent X t s)) :
      EventConditionalExpectation μ ((RelativeDecreaseEvent X (1/2) t).indicator (fun _ => (1 : ℝ)))
        (StateEvent X t s) ≤ (1/2)*(8/(n : ℝ))/(1+Real.log (s/1)) :=
    PathHalfDecreaseProbability PositiveLength Initial t s ((StateLower s InS).resolve_left Nonzero) PositiveEvent
  have Bound := MultiplicativeDriftLowerBound μ X S 1 (1/2) (8/(n : ℝ)) CoordinatesMeasurable
    (Finset.mem_insert_self _ _) zero_lt_one (by norm_num) (by norm_num)
    (div_pos (by norm_num) PositiveN) StateLower ValuesInS Nonincreasing Drift LargeJump
  have InitialMean : ExpectedValue μ (fun Path => MultiplicativeDriftPotential 1 1 (X 0 Path)) =
      ∫ x, MultiplicativeDriftPotential 1 1 (Potential x) ∂Initial.toMeasure :=
    PathMeasureInitialIntegral (Step PositiveLength) Initial (fun x => MultiplicativeDriftPotential 1 1 (Potential x))
  rw [InitialMean] at Bound
  have Coefficient (m : ℝ) : (((1 : ℝ)-1/2)/(1+1/2))*(m/(8/(n : ℝ)))=((n : ℝ)/24)*m := by
    field_simp
    ring
  rw [Coefficient] at Bound
  rw [ExpectedHittingTimeEqExpectedZero (Step PositiveLength) Initial Potential IsTarget PotentialEqZeroIffTarget]
  exact Bound

/-- The actual fixed-start RLS consequence of Theorem 2.4.3; the constant is deliberately conservative. -/
theorem FixedRuntimeMultiplicativeLowerBound {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitialPositive : 0 < ZeroCount InitialState) :
    ENNReal.ofReal (((n : ℝ)/24)*(1+Real.log (ZeroCount InitialState : ℝ))) ≤
      ExpectedRuntime PositiveLength InitialState := by
  have Bound := RuntimeMultiplicativeLowerBound PositiveLength (PMF.pure InitialState)
  rw [PMF.toMeasure_pure, integral_dirac] at Bound
  have Nonzero : Potential InitialState ≠ 0 := (Nat.cast_pos.mpr InitialPositive).ne'
  simp only [MultiplicativeDriftPotential, if_neg Nonzero, div_one] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
