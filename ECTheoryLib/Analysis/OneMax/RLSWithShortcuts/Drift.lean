import ECTheoryLib.Algorithms.RLS.WithShortcuts
import ECTheoryLib.Analysis.Linear.RLS.PositiveWeights
import ECTheoryLib.Probability.Processes.PathDriftBounds
import ECTheoryLib.Probability.Processes.FinitePotentialHistory
import ECTheoryLib.Tools.Drift.Multiplicative

/-!
Example2.3.6: the actual shortcut kernel on weak OneMax minimization.
First hitting includes initialization; each shortcut or ordinary update counts once.
-/
namespace ECTheoryLib.Analysis.RLSWithShortcuts
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open scoped unitInterval Classical
noncomputable section

def Step {n : ℕ} (PositiveLength : 0 < n) : Transition (Bits n) :=
  Algorithms.RLSWithShortcuts.Step PositiveLength
    (Problems.MinNotWorse (Problems.Linear.Score (fun _ => 1))) (fun _ => false)

def ExpectedRuntime {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength) (fun x => (OneMax x : ℝ) = 0) Initial

def Delta (n : ℕ) : ℝ := 2 / (n : ℝ) - 1 / (n : ℝ)^2

def Coefficient (n : ℕ) : ℝ := (n : ℝ)^2 / (2 * (n : ℝ) - 1)

def Bound {n : ℕ} (x : Bits n) : ℝ :=
  MultiplicativeDriftPotential 1 (Delta n) (OneMax x : ℝ)

theorem ComparisonEqOneCount {n : ℕ} (x y : Bits n) :
    Problems.MinNotWorse (Problems.Linear.Score (fun _ => 1)) x y ↔ OneMax x ≤ OneMax y := by
  change Problems.Linear.Score (fun _ => 1) x ≤ Problems.Linear.Score (fun _ => 1) y ↔ _
  rw [Problems.Linear.ScoreUnitWeights, Problems.Linear.ScoreUnitWeights]
  exact Nat.cast_le

theorem CountZeroIff {n : ℕ} (x : Bits n) : (OneMax x : ℝ) = 0 ↔ x = fun _ => false := by
  rw [← Problems.Linear.ScoreUnitWeights x]
  exact RLSLinear.ScoreZeroIff (fun _ => 1) (fun _ => by norm_num) x

theorem DeltaFormula {n : ℕ} (PositiveLength : 0 < n) :
    Delta n = (2 * (n : ℝ) - 1) / (n : ℝ)^2 := by
  have Nonzero : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr PositiveLength)
  unfold Delta
  field_simp

theorem DeltaPositive {n : ℕ} (PositiveLength : 0 < n) : 0 < Delta n := by
  have AtLeastOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt PositiveLength
  rw [DeltaFormula PositiveLength]
  exact div_pos (by linarith) (sq_pos_of_pos (Nat.cast_pos.mpr PositiveLength))

theorem CoefficientEqReciprocal {n : ℕ} (PositiveLength : 0 < n) :
    Coefficient n = 1 / Delta n := by
  rw [DeltaFormula PositiveLength]
  simp only [Coefficient, one_div, inv_div]

theorem CoefficientPositive {n : ℕ} (PositiveLength : 0 < n) : 0 < Coefficient n := by
  rw [CoefficientEqReciprocal PositiveLength]
  exact one_div_pos.mpr (DeltaPositive PositiveLength)

theorem CoefficientBounds {n : ℕ} (PositiveLength : 0 < n) :
    (n : ℝ) / 2 ≤ Coefficient n ∧ Coefficient n ≤ (n : ℝ) := by
  have AtLeastOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt PositiveLength
  have Denominator : 0 < 2 * (n : ℝ) - 1 := by linarith
  constructor
  · rw [Coefficient, le_div_iff₀ Denominator]
    nlinarith
  · rw [Coefficient, div_le_iff₀ Denominator]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sub_nonneg.mpr AtLeastOne)]

/-- Exact local one-count drift of the new mixture, including the zero state. -/
theorem CountDrift {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    (∫ y, (OneMax x : ℝ) - (OneMax y : ℝ) ∂(Step PositiveLength x).toMeasure) =
      Delta n * (OneMax x : ℝ) := by
  have Ordinary := RLSLinear.OneCountDrift PositiveLength (fun _ => 1) (fun _ => by norm_num) x
  change (∫ y, (OneMax x : ℝ) - (OneMax y : ℝ)
    ∂(RLSStep PositiveLength (Problems.MinNotWorse (Problems.Linear.Score (fun _ => 1))) x).toMeasure) = _ at Ordinary
  rw [Step, Algorithms.RLSWithShortcuts.StepIntegral, Ordinary]
  have ZeroCount : OneMax (fun _ : Fin n => false) = 0 := by simp [OneMax]
  rw [ZeroCount, Nat.cast_zero, sub_zero]
  simp only [Delta, div_eq_mul_inv]
  ring

/-- The full natural-history conditional drift is proved from the actual selected kernel. -/
theorem CountConditionalDrift {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) :
    (PathMeasure (Step PositiveLength) Initial)[
      fun Path => (OneMax (Path t) : ℝ) - (OneMax (Path (t + 1)) : ℝ) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) t] =ᵐ[PathMeasure (Step PositiveLength) Initial]
      (fun Path => Delta n * (OneMax (Path t) : ℝ)) := by
  classical
  filter_upwards [PathMeasureFinitePotentialConditionalDrift (Step PositiveLength) Initial
    (fun x => (OneMax x : ℝ)) (Finset.univ.image (fun x : Bits n => (OneMax x : ℝ)))
    (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) t] with Path Equal
  rw [Equal, CountDrift PositiveLength]

theorem StepPreservesZero {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure,
      (OneMax x : ℝ) = 0 → (OneMax y : ℝ) = 0 := by
  apply PMFAEOfSupport (Step PositiveLength x)
  intro y Possible Zero
  change y ∈ ((ProbabilityTheory.bernoulliMeasure true false
    (Algorithms.RLSWithShortcuts.ShortcutProbability PositiveLength)).toPMF.bind
    (fun b => if b then PMF.pure (fun _ => false) else
      RLSStep PositiveLength (Problems.MinNotWorse (Problems.Linear.Score (fun _ => 1))) x)).support at Possible
  obtain ⟨b, _CoinPossible, BranchPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
  cases b with
  | false =>
      simp only [Bool.false_eq_true, if_false] at BranchPossible
      change y ∈ (RLSLinear.Step PositiveLength (fun _ => 1) x).support at BranchPossible
      rw [RLSLinear.StepEqHamming PositiveLength (fun _ => 1) (fun _ => by norm_num)] at BranchPossible
      have ParentZero : RLSHamming.Potential (fun _ => false) x = 0 := by
        simpa only [RLSHamming.Potential, RLSLinear.HammingZeroEqOneMax] using Zero
      simpa only [RLSHamming.Potential, RLSLinear.HammingZeroEqOneMax] using
        RLSHamming.StepPreservesZero PositiveLength (fun _ => false) x y ParentZero BranchPossible
  | true =>
      simp only [if_true] at BranchPossible
      have Equal : y = fun _ => false := (PMF.mem_support_pure_iff _ _).mp BranchPossible
      rw [Equal]
      simp [OneMax]

theorem SuccessProbabilityLower {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    (1 / (n : ℝ)) ≤ (Step PositiveLength x).toMeasure.real {y | (OneMax y : ℝ) = 0} := by
  have GoalSet : {y : Bits n | (OneMax y : ℝ) = 0} = {fun _ => false} := by
    ext y
    exact CountZeroIff y
  rw [GoalSet]
  exact Algorithms.RLSWithShortcuts.StepTargetProbabilityLower PositiveLength
    (Problems.MinNotWorse (Problems.Linear.Score (fun _ => 1))) (fun _ => false) x

theorem BoundAtZero {n : ℕ} : Bound (fun _ : Fin n => false) = 0 := by
  simp [Bound, MultiplicativeDriftPotential, OneMax]

end
end ECTheoryLib.Analysis.RLSWithShortcuts


/-! Exact transformed descent, with the source's s=1 boundary kept separate. -/
namespace ECTheoryLib.Analysis.RLSWithShortcuts
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open scoped Classical
noncomputable section

theorem BoundOfNonzero {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Nonzero : (OneMax x : ℝ) ≠ 0) :
    Bound x = Coefficient n * (1 + Real.log (OneMax x : ℝ)) := by
  simp only [Bound, MultiplicativeDriftPotential, if_neg Nonzero, div_one]
  rw [CoefficientEqReciprocal PositiveLength]
  ring

private theorem OrdinaryFunctionDrift {n : ℕ} (PositiveLength : 0 < n)
    (x : Bits n) (f : ℕ → ℝ) :
    (∫ y, f (OneMax x) - f (OneMax y) ∂(RLSLinear.Step PositiveLength (fun _ => 1) x).toMeasure) =
      ((OneMax x : ℝ) / (n : ℝ)) * (f (OneMax x) - f (OneMax x - 1)) := by
  have CountAfter (i : Fin n) :
      OneMax (RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score (fun _ => 1))) x i) =
        if x i then OneMax x - 1 else OneMax x := by
    cases Bit : x i with
    | false =>
        rw [RLSLinear.UpdateAtZero (fun _ => 1) (fun _ => by norm_num) x i Bit]
        simp
    | true =>
        rw [RLSLinear.UpdateAtOne (fun _ => 1) (fun _ => by norm_num) x i Bit]
        simp only [if_true]
        have Decrease := ECTheoryLib.Analysis.OneMax.OneMaxMutationAtOne x i Bit
        omega
  have SumOnes : (∑ i : Fin n, if x i then (1 : ℝ) else 0) = (OneMax x : ℝ) := by
    rw [OneMax, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> norm_num
  rw [RLSLinear.Step, RLSStepEqUniformUpdate, PMFIntegralMap, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  simp_rw [UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast, CountAfter]
  have Term (i : Fin n) :
      (n : ℝ)⁻¹ * (f (OneMax x) - f (if x i then OneMax x - 1 else OneMax x)) =
        ((n : ℝ)⁻¹ * (f (OneMax x) - f (OneMax x - 1))) * (if x i then 1 else 0) := by
    cases x i <;> simp
  simp_rw [Term]
  rw [← Finset.mul_sum, SumOnes]
  ring

/-- Every function of the count has an exact two-branch local drift formula. -/
theorem CountFunctionDrift {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) (f : ℕ → ℝ) :
    (∫ y, f (OneMax x) - f (OneMax y) ∂(Step PositiveLength x).toMeasure) =
      (1 / (n : ℝ)) * (f (OneMax x) - f 0) +
        (1 - 1 / (n : ℝ)) * ((OneMax x : ℝ) / (n : ℝ)) *
          (f (OneMax x) - f (OneMax x - 1)) := by
  have Ordinary := OrdinaryFunctionDrift PositiveLength x f
  change (∫ y, f (OneMax x) - f (OneMax y)
    ∂(RLSStep PositiveLength (Problems.MinNotWorse (Problems.Linear.Score (fun _ => 1))) x).toMeasure) = _ at Ordinary
  rw [Step, Algorithms.RLSWithShortcuts.StepIntegral, Ordinary]
  have ZeroCount : OneMax (fun _ : Fin n => false) = 0 := by simp [OneMax]
  rw [ZeroCount]
  ring

theorem RescaledDriftFormula {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    (∫ y, Bound x - Bound y ∂(Step PositiveLength x).toMeasure) =
      (1 / (n : ℝ)) * Bound x + (1 - 1 / (n : ℝ)) * ((OneMax x : ℝ) / (n : ℝ)) *
        (Bound x - MultiplicativeDriftPotential 1 (Delta n) (OneMax x - 1 : ℕ)) := by
  have Formula := CountFunctionDrift PositiveLength x
    (fun s => MultiplicativeDriftPotential 1 (Delta n) (s : ℝ))
  have ZeroValue : MultiplicativeDriftPotential 1 (Delta n) (0 : ℝ) = 0 := by
    simp [MultiplicativeDriftPotential]
  simpa only [Bound, Nat.cast_zero, ZeroValue, sub_zero] using Formula

theorem RescaledDriftAtZero {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Zero : OneMax x = 0) : (∫ y, Bound x - Bound y ∂(Step PositiveLength x).toMeasure) = 0 := by
  rw [RescaledDriftFormula]
  simp [Bound, MultiplicativeDriftPotential, Zero]

theorem RescaledDriftAtOne {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (One : OneMax x = 1) : (∫ y, Bound x - Bound y ∂(Step PositiveLength x).toMeasure) = 1 := by
  have Nonzero : (OneMax x : ℝ) ≠ 0 := by rw [One]; norm_num
  rw [RescaledDriftFormula, BoundOfNonzero PositiveLength x Nonzero, One]
  simp only [Nat.cast_one, Real.log_one, add_zero, mul_one, Nat.sub_self, Nat.cast_zero,
    MultiplicativeDriftPotential]
  calc
    _ = Coefficient n * Delta n := by dsimp [Delta]; ring
    _ = 1 := by
      rw [CoefficientEqReciprocal PositiveLength]
      have NonzeroDelta : Delta n ≠ 0 := ne_of_gt (DeltaPositive PositiveLength)
      field_simp

theorem RescaledDriftAtLeastTwo {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (AtLeastTwo : 2 ≤ OneMax x) :
    (∫ y, Bound x - Bound y ∂(Step PositiveLength x).toMeasure) =
      Coefficient n / (n : ℝ) * (1 + Real.log (OneMax x : ℝ)) +
        (1 - 1 / (n : ℝ)) * (OneMax x : ℝ) * Coefficient n / (n : ℝ) *
          Real.log ((OneMax x : ℝ) / ((OneMax x : ℝ) - 1)) := by
  have PositiveCount : (0 : ℝ) < (OneMax x : ℝ) := by exact_mod_cast (by omega : 0 < OneMax x)
  have PositivePred : (0 : ℝ) < ((OneMax x - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < OneMax x - 1)
  have PredCast : ((OneMax x - 1 : ℕ) : ℝ) = (OneMax x : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ OneMax x), Nat.cast_one]
  have PredValue : MultiplicativeDriftPotential 1 (Delta n) (OneMax x - 1 : ℕ) =
      Coefficient n * (1 + Real.log ((OneMax x : ℝ) - 1)) := by
    rw [MultiplicativeDriftPotential, if_neg PositivePred.ne', div_one, PredCast,
      CoefficientEqReciprocal PositiveLength]
    ring
  rw [RescaledDriftFormula, BoundOfNonzero PositiveLength x PositiveCount.ne', PredValue,
    Real.log_div PositiveCount.ne' (by rw [← PredCast]; exact PositivePred.ne')]
  ring

def RescaledDriftValue (n s : ℕ) : ℝ :=
  if s = 0 then 0 else if s = 1 then 1 else
    Coefficient n / (n : ℝ) * (1 + Real.log (s : ℝ)) +
      (1 - 1 / (n : ℝ)) * (s : ℝ) * Coefficient n / (n : ℝ) *
        Real.log ((s : ℝ) / ((s : ℝ) - 1))

theorem RescaledDrift {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    (∫ y, Bound x - Bound y ∂(Step PositiveLength x).toMeasure) = RescaledDriftValue n (OneMax x) := by
  by_cases Zero : OneMax x = 0
  · simpa only [RescaledDriftValue, if_pos Zero] using RescaledDriftAtZero PositiveLength x Zero
  · by_cases One : OneMax x = 1
    · simpa only [RescaledDriftValue, if_neg Zero, if_pos One] using RescaledDriftAtOne PositiveLength x One
    · simpa only [RescaledDriftValue, if_neg Zero, if_neg One] using
        RescaledDriftAtLeastTwo PositiveLength x (by omega)

theorem RescaledConditionalDrift {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) (t : ℕ) :
    (PathMeasure (Step PositiveLength) Initial)[fun Path => Bound (Path t) - Bound (Path (t + 1)) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) t] =ᵐ[PathMeasure (Step PositiveLength) Initial]
      (fun Path => RescaledDriftValue n (OneMax (Path t))) := by
  classical
  filter_upwards [PathMeasureFinitePotentialConditionalDrift (Step PositiveLength) Initial Bound
    (Finset.univ.image Bound) (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) t]
    with Path Equal
  rw [Equal, RescaledDrift PositiveLength]

def ApproximateBound {n : ℕ} (x : Bits n) : ℝ :=
  if OneMax x = 0 then 0 else (n : ℝ) / 2 * (1 + Real.log (OneMax x : ℝ))

/-- At a one-count state the book's asymptotic coefficient has descent strictly below one. -/
theorem ApproximateSingleOneDrift {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (One : OneMax x = 1) :
    (∫ y, ApproximateBound x - ApproximateBound y ∂(Step PositiveLength x).toMeasure) =
      1 - 1 / (2 * (n : ℝ)) := by
  have Formula := CountFunctionDrift PositiveLength x
    (fun s => if s = 0 then 0 else (n : ℝ) / 2 * (1 + Real.log (s : ℝ)))
  change (∫ y, ApproximateBound x - ApproximateBound y ∂(Step PositiveLength x).toMeasure) = _ at Formula
  rw [Formula, One]
  norm_num
  have NonzeroN : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr PositiveLength)
  field_simp
  ring

theorem ApproximateSingleOneDriftBelowOne {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (One : OneMax x = 1) :
    (∫ y, ApproximateBound x - ApproximateBound y ∂(Step PositiveLength x).toMeasure) < 1 := by
  rw [ApproximateSingleOneDrift PositiveLength x One]
  have Positive : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  linarith

end
end ECTheoryLib.Analysis.RLSWithShortcuts


/-! Explicit finite remainder for the source's log(s)/2+O(1) explanation. -/
namespace ECTheoryLib.Analysis.RLSWithShortcuts
open MeasureTheory ECTheoryLib.Probability
noncomputable section

private theorem ApproximateBoundScale {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ApproximateBound x = ((n : ℝ) / (2 * Coefficient n)) * Bound x := by
  by_cases Zero : OneMax x = 0
  · simp [ApproximateBound, Bound, Tools.Drift.MultiplicativeDriftPotential, Zero]
  · have RealNonzero : (OneMax x : ℝ) ≠ 0 := by exact_mod_cast Zero
    rw [ApproximateBound, if_neg Zero, BoundOfNonzero PositiveLength x RealNonzero]
    have CoefficientNonzero : Coefficient n ≠ 0 := ne_of_gt (CoefficientPositive PositiveLength)
    field_simp

theorem ApproximateDriftAtLeastTwo {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (AtLeastTwo : 2 ≤ OneMax x) :
    (∫ y, ApproximateBound x - ApproximateBound y ∂(Step PositiveLength x).toMeasure) =
      (1 / 2 : ℝ) * (1 + Real.log (OneMax x : ℝ)) +
        (1 - 1 / (n : ℝ)) * (OneMax x : ℝ) / 2 *
          Real.log ((OneMax x : ℝ) / ((OneMax x : ℝ) - 1)) := by
  have Functions : (fun y : Bits n => ApproximateBound x - ApproximateBound y) =
      (fun y => ((n : ℝ) / (2 * Coefficient n)) * (Bound x - Bound y)) := by
    funext y
    rw [ApproximateBoundScale PositiveLength x, ApproximateBoundScale PositiveLength y]
    ring
  rw [Functions, integral_const_mul, RescaledDriftAtLeastTwo PositiveLength x AtLeastTwo]
  have NonzeroN : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr PositiveLength)
  have CoefficientNonzero : Coefficient n ≠ 0 := ne_of_gt (CoefficientPositive PositiveLength)
  field_simp

theorem ApproximateDriftFiniteRemainder {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (AtLeastTwo : 2 ≤ OneMax x) :
    Real.log (OneMax x : ℝ) / 2 + 1 / 2 ≤
      (∫ y, ApproximateBound x - ApproximateBound y ∂(Step PositiveLength x).toMeasure) ∧
    (∫ y, ApproximateBound x - ApproximateBound y ∂(Step PositiveLength x).toMeasure) ≤
      Real.log (OneMax x : ℝ) / 2 + 3 / 2 := by
  let s : ℝ := (OneMax x : ℝ)
  have LowerS : (2 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast AtLeastTwo
  have PositiveS : 0 < s := by linarith
  have PositivePred : 0 < s - 1 := by linarith
  have RatioAtLeastOne : 1 ≤ s / (s - 1) := (le_div_iff₀ PositivePred).mpr (by linarith)
  have LogNonnegative : 0 ≤ Real.log (s / (s - 1)) := Real.log_nonneg RatioAtLeastOne
  have ScaledLogUpper : s * Real.log (s / (s - 1)) ≤ 2 := by
    calc
      _ ≤ s * (s / (s - 1) - 1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos PositiveS PositivePred)) PositiveS.le
      _ = s / (s - 1) := by
        field_simp
        ring
      _ ≤ 2 := (div_le_iff₀ PositivePred).mpr (by linarith)
  have FailureNonnegative : 0 ≤ 1 - 1 / (n : ℝ) :=
    sub_nonneg.mpr (Algorithms.RLSWithShortcuts.ShortcutProbability PositiveLength).2.2
  have FailureLeOne : 1 - 1 / (n : ℝ) ≤ 1 := sub_le_self 1 (by positivity)
  have ProductNonnegative : 0 ≤ s * Real.log (s / (s - 1)) := mul_nonneg PositiveS.le LogNonnegative
  have ProductCompared := mul_le_mul_of_nonneg_right FailureLeOne ProductNonnegative
  have OrdinaryNonnegative : 0 ≤ (1 - 1 / (n : ℝ)) * s / 2 * Real.log (s / (s - 1)) := by positivity
  have OrdinaryUpper : (1 - 1 / (n : ℝ)) * s / 2 * Real.log (s / (s - 1)) ≤ 1 := by
    nlinarith
  have Formula := ApproximateDriftAtLeastTwo PositiveLength x AtLeastTwo
  dsimp [s] at OrdinaryNonnegative OrdinaryUpper
  constructor <;> nlinarith [Formula]

end
end ECTheoryLib.Analysis.RLSWithShortcuts

