import ECTheoryLib.Analysis.RandomDecline.CountDrift
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact finite logarithmic drift. The offset two is a disclosed finite-state
correction; the source's offset one is retained as a separate potential. -/
namespace ECTheoryLib.Analysis.RandomDecline
open MeasureTheory ECTheoryLib.Probability
noncomputable section

def LogSum (m : ℕ) : ℝ := ∑ k ∈ Finset.Ico 1 (m + 1), Real.log (k : ℝ)

@[simp] theorem LogSumZero : LogSum 0 = 0 := by simp [LogSum]

def LogPotential (c : ℝ) (s : ℕ) : ℝ := if s = 0 then 0 else c + Real.log (s : ℝ)

@[simp] theorem LogPotentialAtZero (c : ℝ) : LogPotential c 0 = 0 := by
  simp [LogPotential]

theorem LogPotentialNonnegative {c : ℝ} (Nonnegative : 0 ≤ c) (s : ℕ) :
    0 ≤ LogPotential c s := by
  by_cases Zero : s = 0
  · simp [Zero]
  · rw [LogPotential, if_neg Zero]
    exact add_nonneg Nonnegative (Real.log_nonneg (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero))

theorem LogPotentialZeroIff {c : ℝ} (Positive : 0 < c) (s : ℕ) :
    LogPotential c s = 0 ↔ s = 0 := by
  by_cases Zero : s = 0
  · simp [Zero]
  · have NonnegativeLog : 0 ≤ Real.log (s : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero)
    simp only [LogPotential, if_neg Zero]
    constructor
    · intro Equal
      exfalso
      linarith
    · intro Equal
      exact (Zero Equal).elim

/-- Fixed Mathlib monotone integral comparisons, specialized to the actual finite sum. -/
theorem LogSumBounds (m : ℕ) (Positive : 1 ≤ m) :
    (m : ℝ) * Real.log (m : ℝ) - m + 1 ≤ LogSum m ∧
      LogSum m ≤ ((m : ℝ) + 1) * Real.log (m : ℝ) - m + 1 := by
  have Monotone : MonotoneOn Real.log (Set.Icc (1 : ℝ) (m : ℝ)) := by
    intro x InX y _InY Ordered
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one InX.1) Ordered
  have Lower := MonotoneOn.integral_le_sum_Ico (f := Real.log) Positive
    (by simpa only [Nat.cast_one] using Monotone)
  have Upper := MonotoneOn.sum_le_integral_Ico (f := Real.log) Positive
    (by simpa only [Nat.cast_one] using Monotone)
  have Tail : LogSum m = ∑ k ∈ Finset.Ico 2 (m + 1), Real.log (k : ℝ) := by
    rw [LogSum, Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < m + 1)]
    simp
  simp only [Nat.cast_one] at Lower Upper
  rw [Finset.sum_Ico_add' (fun k : ℕ => Real.log (k : ℝ)) 1 m 1, ← Tail] at Lower
  norm_num [integral_log] at Lower Upper
  have Split : LogSum m =
      (∑ k ∈ Finset.Ico 1 m, Real.log (k : ℝ)) + Real.log (m : ℝ) :=
    Finset.sum_Ico_succ_top Positive _
  constructor
  · exact Lower
  · rw [Split]
    nlinarith

theorem LogPotentialStepMean {N : ℕ} (a c : ℝ) (s : Fin (N + 1)) :
    (∫ y, LogPotential c y.val ∂(Step a s).toMeasure) =
      (c * (Cutoff a s : ℝ) + LogSum (Cutoff a s)) / ((Cutoff a s : ℝ) + 1) := by
  have Sum : (∑ k ∈ Finset.range (Cutoff a s + 1), LogPotential c k) =
      c * (Cutoff a s : ℝ) + LogSum (Cutoff a s) := by
    rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos _), LogPotentialAtZero, zero_add]
    calc
      (∑ k ∈ Finset.Ico 1 (Cutoff a s + 1), LogPotential c k) =
          ∑ k ∈ Finset.Ico 1 (Cutoff a s + 1), (c + Real.log (k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k InK
        rw [LogPotential, if_neg (by have := (Finset.mem_Ico.mp InK).1; omega)]
      _ = c * (Cutoff a s : ℝ) + LogSum (Cutoff a s) := by
        rw [Finset.sum_add_distrib]
        simp [LogSum, mul_comm]
  rw [StepNatIntegral, Sum]
  ring

theorem LogDriftExact {N : ℕ} (a c : ℝ) (s : Fin (N + 1)) :
    (∫ y, LogPotential c s.val - LogPotential c y.val ∂(Step a s).toMeasure) =
      LogPotential c s.val -
        (c * (Cutoff a s : ℝ) + LogSum (Cutoff a s)) / ((Cutoff a s : ℝ) + 1) := by
  rw [integral_sub Integrable.of_finite Integrable.of_finite, LogPotentialStepMean]
  simp

theorem CorrectedStepMeanUpper {N : ℕ} (a : ℝ) (s : Fin (N + 1))
    (PositiveCutoff : 1 ≤ Cutoff a s) :
    (∫ y, LogPotential 2 y.val ∂(Step a s).toMeasure) ≤ 1 + Real.log (Cutoff a s : ℝ) := by
  rw [LogPotentialStepMean]
  apply (div_le_iff₀ (by positivity : 0 < (Cutoff a s : ℝ) + 1)).mpr
  nlinarith [(LogSumBounds (Cutoff a s) PositiveCutoff).2]

theorem CorrectedDriftLowerOfPositiveCutoff {N : ℕ} {a : ℝ} (PositiveA : 0 < a)
    (s : Fin (N + 1)) (PositiveState : 0 < s.val) (PositiveCutoff : 1 ≤ Cutoff a s) :
    1 - Real.log a ≤
      ∫ y, LogPotential 2 s.val - LogPotential 2 y.val ∂(Step a s).toMeasure := by
  have PositiveS : (0 : ℝ) < s.val := Nat.cast_pos.mpr PositiveState
  have PositiveM : (0 : ℝ) < Cutoff a s :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one PositiveCutoff)
  have LogBound : Real.log (Cutoff a s : ℝ) ≤ Real.log a + Real.log (s.val : ℝ) := by
    calc
      Real.log (Cutoff a s : ℝ) ≤ Real.log (a * (s.val : ℝ)) :=
        Real.log_le_log PositiveM (CutoffRealLe PositiveA.le s)
      _ = _ := Real.log_mul PositiveA.ne' PositiveS.ne'
  have Mean := CorrectedStepMeanUpper a s PositiveCutoff
  rw [LogPotentialStepMean] at Mean
  rw [LogDriftExact, LogPotential, if_neg (Nat.ne_of_gt PositiveState)]
  linarith

def LogDelta (a : ℝ) : ℝ := min 1 (1 - Real.log a)

theorem LogDeltaPositive {a : ℝ} (Positive : 0 < a) (Below : a < Real.exp 1) :
    0 < LogDelta a := by
  have LogLess : Real.log a < 1 := (Real.log_lt_iff_lt_exp Positive).mpr Below
  exact lt_min (by norm_num) (by linarith)

/-- Clipping is retained: no hypothesis excludes visits to the right boundary. -/
theorem CorrectedDriftLower {N : ℕ} {a : ℝ} (PositiveA : 0 < a)
    (s : Fin (N + 1)) (PositiveState : 0 < s.val) :
    LogDelta a ≤
      ∫ y, LogPotential 2 s.val - LogPotential 2 y.val ∂(Step a s).toMeasure := by
  by_cases ZeroCutoff : Cutoff a s = 0
  · rw [LogDriftExact, ZeroCutoff, LogSumZero]
    simp only [Nat.cast_zero, mul_zero, zero_add, zero_div, sub_zero,
      LogPotential, if_neg (Nat.ne_of_gt PositiveState)]
    have NonnegativeLog : 0 ≤ Real.log (s.val : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt PositiveState)
    exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (CorrectedDriftLowerOfPositiveCutoff
      PositiveA s PositiveState (Nat.one_le_iff_ne_zero.mpr ZeroCutoff))

/-- Two finite bounds on the source offset-one expectation, with no asymptotic symbol. -/
theorem SourceStepMeanBounds {N : ℕ} (a : ℝ) (s : Fin (N + 1))
    (PositiveCutoff : 1 ≤ Cutoff a s) :
    Real.log (Cutoff a s : ℝ) +
        (1 - Real.log (Cutoff a s : ℝ)) / ((Cutoff a s : ℝ) + 1) ≤
      (∫ y, LogPotential 1 y.val ∂(Step a s).toMeasure) ∧
    (∫ y, LogPotential 1 y.val ∂(Step a s).toMeasure) ≤
      Real.log (Cutoff a s : ℝ) + 1 / ((Cutoff a s : ℝ) + 1) := by
  have Bounds := LogSumBounds (Cutoff a s) PositiveCutoff
  have Positive : 0 < (Cutoff a s : ℝ) + 1 := by positivity
  have Nonzero := ne_of_gt Positive
  rw [LogPotentialStepMean]
  constructor
  · calc
      Real.log (Cutoff a s : ℝ) +
          (1 - Real.log (Cutoff a s : ℝ)) / ((Cutoff a s : ℝ) + 1) =
          ((Cutoff a s : ℝ) * Real.log (Cutoff a s : ℝ) + 1) /
            ((Cutoff a s : ℝ) + 1) := by
        field_simp [Nonzero]
        ring
      _ ≤ _ := (div_le_div_iff_of_pos_right Positive).mpr (by nlinarith [Bounds.1])
  · calc
      (1 * (Cutoff a s : ℝ) + LogSum (Cutoff a s)) / ((Cutoff a s : ℝ) + 1) ≤
          (((Cutoff a s : ℝ) + 1) * Real.log (Cutoff a s : ℝ) + 1) /
            ((Cutoff a s : ℝ) + 1) :=
        (div_le_div_iff_of_pos_right Positive).mpr (by nlinarith [Bounds.2])
      _ = _ := by field_simp [Nonzero]

theorem SourceLogDriftLower {N : ℕ} {a : ℝ} (PositiveA : 0 < a)
    (s : Fin (N + 1)) (PositiveState : 0 < s.val) (PositiveCutoff : 1 ≤ Cutoff a s) :
    1 - Real.log a - 1 / ((Cutoff a s : ℝ) + 1) ≤
      ∫ y, LogPotential 1 s.val - LogPotential 1 y.val ∂(Step a s).toMeasure := by
  have PositiveS : (0 : ℝ) < s.val := Nat.cast_pos.mpr PositiveState
  have PositiveM : (0 : ℝ) < Cutoff a s :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one PositiveCutoff)
  have LogBound : Real.log (Cutoff a s : ℝ) ≤ Real.log a + Real.log (s.val : ℝ) := by
    calc
      Real.log (Cutoff a s : ℝ) ≤ Real.log (a * (s.val : ℝ)) :=
        Real.log_le_log PositiveM (CutoffRealLe PositiveA.le s)
      _ = _ := Real.log_mul PositiveA.ne' PositiveS.ne'
  have Mean := (SourceStepMeanBounds a s PositiveCutoff).2
  rw [LogPotentialStepMean] at Mean
  rw [LogDriftExact, LogPotential, if_neg (Nat.ne_of_gt PositiveState)]
  linarith

theorem SourceLogDriftUpperUnclipped {N : ℕ} {a : ℝ} (PositiveA : 0 < a)
    (s : Fin (N + 1)) (PositiveState : 0 < s.val) (PositiveCutoff : 1 ≤ Cutoff a s)
    (Within : ⌊a * (s.val : ℝ)⌋₊ ≤ N) :
    (∫ y, LogPotential 1 s.val - LogPotential 1 y.val ∂(Step a s).toMeasure) ≤
      1 - Real.log a + 1 / (Cutoff a s : ℝ) +
        Real.log (Cutoff a s : ℝ) / ((Cutoff a s : ℝ) + 1) := by
  have PositiveS : (0 : ℝ) < s.val := Nat.cast_pos.mpr PositiveState
  have PositiveM : (0 : ℝ) < Cutoff a s :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one PositiveCutoff)
  have FloorUpper : a * (s.val : ℝ) < (Cutoff a s : ℝ) + 1 := by
    rw [CutoffUnclipped a s Within]
    exact Nat.lt_floor_add_one _
  have RatioBound : a * (s.val : ℝ) / (Cutoff a s : ℝ) ≤
      1 + 1 / (Cutoff a s : ℝ) := by
    apply (div_le_iff₀ PositiveM).mpr
    have Identity : (1 + 1 / (Cutoff a s : ℝ)) * (Cutoff a s : ℝ) =
        (Cutoff a s : ℝ) + 1 := by field_simp
    rw [Identity]
    exact FloorUpper.le
  have LogRatio := Real.log_le_log (div_pos (mul_pos PositiveA PositiveS) PositiveM) RatioBound
  rw [Real.log_div (mul_ne_zero PositiveA.ne' PositiveS.ne') PositiveM.ne',
    Real.log_mul PositiveA.ne' PositiveS.ne'] at LogRatio
  have Taylor := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 1 + 1 / (Cutoff a s : ℝ))
  have Mean := (SourceStepMeanBounds a s PositiveCutoff).1
  rw [LogPotentialStepMean] at Mean
  simp only [sub_div] at Mean
  have InverseNonnegative : 0 ≤ 1 / ((Cutoff a s : ℝ) + 1) := by positivity
  rw [LogDriftExact, LogPotential, if_neg (Nat.ne_of_gt PositiveState)]
  linarith

theorem LogConditionalDrift {N : ℕ} (a c : ℝ) (Initial : PMF (Fin (N + 1))) (t : ℕ) :
    (PathMeasure (Step a) Initial)[
      fun Path => LogPotential c (Path t).val - LogPotential c (Path (t + 1)).val |
      Filtration.piLE (X := fun _ : ℕ => Fin (N + 1)) t] =ᵐ[PathMeasure (Step a) Initial]
      (fun Path => LogPotential c (Path t).val -
        (c * (Cutoff a (Path t) : ℝ) + LogSum (Cutoff a (Path t))) /
          ((Cutoff a (Path t) : ℝ) + 1)) := by
  classical
  filter_upwards [PathMeasureFinitePotentialConditionalDrift (Step a) Initial
    (fun s => LogPotential c s.val)
    (Finset.univ.image (fun s : Fin (N + 1) => LogPotential c s.val))
    (fun s => Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩) t] with Path Equal
  rw [Equal, LogDriftExact]

end
end ECTheoryLib.Analysis.RandomDecline

