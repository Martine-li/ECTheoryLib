import ECTheoryLib.Analysis.RandomDecline.LogarithmicDrift
import ECTheoryLib.Tools.Runtime.LocalDrift
import ECTheoryLib.Tools.Runtime.Geometric
import ECTheoryLib.Probability.Processes.InitialMixture

/-! Runtime bounds on the same actual finite trajectories. Finiteness is a
conclusion; initialization and clipped transitions are retained. -/
namespace ECTheoryLib.Analysis.RandomDecline
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open scoped unitInterval
noncomputable section

def ExpectedRuntime {N : ℕ} (a : ℝ) (Initial : PMF (Fin (N + 1))) : ENNReal :=
  ExpectedHittingTime (Step a) (fun y => y.val = 0) Initial

theorem AtGoalRuntime {N : ℕ} (a : ℝ) (s : Fin (N + 1)) (Zero : s.val = 0) :
    ExpectedRuntime a (PMF.pure s) = 0 :=
  ExpectedHittingTimeOfPureTarget (Step a) (fun y => y.val = 0) s Zero

theorem GeometricRuntimeUpper {N : ℕ} (a : ℝ) (Initial : PMF (Fin (N + 1))) :
    ExpectedRuntime a Initial ≤ ENNReal.ofReal ((N : ℝ) + 1) := by
  let p : I := ⟨1 / ((N : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (N : ℝ) + 1)).mpr
      linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]⟩
  have Bound := Tools.Runtime.PathWaitingExpectedRuntime (Step a) Initial
    (fun y => y.val = 0) (fun _ => True) p (by dsimp [p]; positivity)
    (fun _ => ae_of_all _ (fun _ => trivial)) (StepPreservesZero a)
    (fun s _ _ => SuccessProbabilityLower a s)
  simpa only [ExpectedRuntime, p, one_div_one_div] using Bound

theorem RuntimeFinite {N : ℕ} (a : ℝ) (Initial : PMF (Fin (N + 1))) :
    ExpectedRuntime a Initial ≠ ⊤ :=
  (lt_of_le_of_lt (GeometricRuntimeUpper a Initial) ENNReal.ofReal_lt_top).ne

theorem InitialFailureRuntimeUpper {N : ℕ} (a : ℝ) (Initial : PMF (Fin (N + 1))) :
    ExpectedRuntime a Initial ≤
      ENNReal.ofReal (((N : ℝ) + 1) * Initial.toMeasure.real {s | s.val ≠ 0}) := by
  let f : Fin (N + 1) → ℝ := fun s => if s.val = 0 then 0 else (N : ℝ) + 1
  have Nonnegative : ∀ s, 0 ≤ f s := by
    intro s
    simp only [f]
    split_ifs <;> positivity
  have IntegralValue : (∫ s, f s ∂Initial.toMeasure) =
      ((N : ℝ) + 1) * Initial.toMeasure.real {s | s.val ≠ 0} := by
    have AsIndicator : f = {s : Fin (N + 1) | s.val ≠ 0}.indicator
        (fun _ => (N : ℝ) + 1) := by
      funext s
      by_cases Zero : s.val = 0 <;> simp [f, Set.indicator_apply]
    rw [AsIndicator, integral_indicator_const _ (Set.to_countable _).measurableSet, smul_eq_mul]
    ring
  calc
    ExpectedRuntime a Initial = ∫⁻ s, ExpectedRuntime a (PMF.pure s) ∂Initial.toMeasure :=
      ExpectedHittingTimeInitialMixture (Step a) (fun s => s.val = 0) Initial
    _ ≤ ∫⁻ s, ENNReal.ofReal (f s) ∂Initial.toMeasure := by
      apply lintegral_mono
      intro s
      by_cases Zero : s.val = 0
      · simp [f, AtGoalRuntime a s Zero]
      · simpa only [f, if_neg Zero] using GeometricRuntimeUpper a (PMF.pure s)
    _ = ENNReal.ofReal (∫ s, f s ∂Initial.toMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite (ae_of_all _ Nonnegative)).symm
    _ = _ := by rw [IntegralValue]

theorem MultiplicativeRuntimeUpper {N : ℕ} {a : ℝ} (PositiveA : 0 < a) (Below : a < 2)
    (Initial : PMF (Fin (N + 1))) :
    ExpectedRuntime a Initial ≤ ENNReal.ofReal (∫ s,
      MultiplicativeDriftPotential 1 (1 - a / 2) (s.val : ℝ) ∂Initial.toMeasure) := by
  exact Tools.Runtime.MultiplicativeRuntimeUpperBound (Step a) Initial (fun s => s.val)
    (fun s => s.val = 0) (fun _ => True) (fun _ => Iff.rfl)
    (ae_of_all _ (fun _ => trivial)) (fun _ => ae_of_all _ (fun _ _ => trivial))
    (fun s => by
      filter_upwards [StepPreservesZero a s] with y Preserved
      exact fun _ => Preserved)
    (1 - a / 2) (by linarith) (fun s _ _ => CountDriftLower PositiveA.le s)

theorem FixedMultiplicativeRuntimeUpper {N : ℕ} {a : ℝ} (PositiveA : 0 < a) (Below : a < 2)
    (s : Fin (N + 1)) (PositiveState : 0 < s.val) :
    ExpectedRuntime a (PMF.pure s) ≤ ENNReal.ofReal
      ((1 + Real.log (s.val : ℝ)) / (1 - a / 2)) := by
  have Bound := MultiplicativeRuntimeUpper PositiveA Below (PMF.pure s)
  simpa only [PMF.toMeasure_pure, integral_dirac, MultiplicativeDriftPotential,
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt PositiveState), if_false, div_one] using Bound

theorem AdditiveRuntimeUpper {N : ℕ} {a : ℝ} (PositiveA : 0 < a) (Below : a < Real.exp 1)
    (Initial : PMF (Fin (N + 1))) :
    ExpectedRuntime a Initial ≤ ENNReal.ofReal
      ((∫ s, LogPotential 2 s.val ∂Initial.toMeasure) / LogDelta a) := by
  exact Tools.Runtime.AdditiveRuntimeUpperBound (Step a) Initial (fun s => LogPotential 2 s.val)
    (fun s => s.val = 0) (fun _ => True)
    (fun s => LogPotentialNonnegative (by norm_num) s.val)
    (fun s => LogPotentialZeroIff (by norm_num) s.val)
    (ae_of_all _ (fun _ => trivial)) (fun _ => ae_of_all _ (fun _ _ => trivial))
    (fun s => by
      filter_upwards [StepPreservesZero a s] with y Preserved
      intro _ Zero
      exact (LogPotentialZeroIff (by norm_num : (0 : ℝ) < 2) y.val).mpr
        (Preserved ((LogPotentialZeroIff (by norm_num : (0 : ℝ) < 2) s.val).mp Zero)))
    (LogDelta a) (LogDeltaPositive PositiveA Below) (fun s _ Nonzero =>
      CorrectedDriftLower PositiveA s (Nat.pos_of_ne_zero (fun Zero =>
        Nonzero ((LogPotentialZeroIff (by norm_num : (0 : ℝ) < 2) s.val).mpr Zero))))

theorem FixedAdditiveRuntimeUpper {N : ℕ} {a : ℝ} (PositiveA : 0 < a)
    (Below : a < Real.exp 1) (s : Fin (N + 1)) (PositiveState : 0 < s.val) :
    ExpectedRuntime a (PMF.pure s) ≤
      ENNReal.ofReal ((2 + Real.log (s.val : ℝ)) / LogDelta a) := by
  have Bound := AdditiveRuntimeUpper PositiveA Below (PMF.pure s)
  simpa only [PMF.toMeasure_pure, integral_dirac, LogPotential,
    if_neg (Nat.ne_of_gt PositiveState)] using Bound

/-- For fixed a, an explicit logarithmic coefficient valid from integer state two. -/
theorem FixedLogarithmicRuntimeUpper {N : ℕ} {a : ℝ} (PositiveA : 0 < a)
    (Below : a < Real.exp 1) (s : Fin (N + 1)) (AtLeastTwo : 2 ≤ s.val) :
    ExpectedRuntime a (PMF.pure s) ≤ ENNReal.ofReal
      (((1 + 2 / Real.log 2) / LogDelta a) * Real.log (s.val : ℝ)) := by
  have PositiveLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have LowerLog : Real.log 2 ≤ Real.log (s.val : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast AtLeastTwo)
  have ConstantBound : 2 ≤ (2 / Real.log 2) * Real.log (s.val : ℝ) := by
    calc
      (2 : ℝ) = (2 / Real.log 2) * Real.log 2 :=
        (div_mul_cancel₀ _ PositiveLogTwo.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left LowerLog (by positivity)
  have Size : 2 + Real.log (s.val : ℝ) ≤
      (1 + 2 / Real.log 2) * Real.log (s.val : ℝ) := by nlinarith
  have Bound : (2 + Real.log (s.val : ℝ)) / LogDelta a ≤
      ((1 + 2 / Real.log 2) / LogDelta a) * Real.log (s.val : ℝ) := by
    calc
      _ ≤ ((1 + 2 / Real.log 2) * Real.log (s.val : ℝ)) / LogDelta a :=
        div_le_div_of_nonneg_right Size (LogDeltaPositive PositiveA Below).le
      _ = _ := by ring
  exact (FixedAdditiveRuntimeUpper PositiveA Below s (by omega)).trans
    (ENNReal.ofReal_le_ofReal Bound)

end
end ECTheoryLib.Analysis.RandomDecline

