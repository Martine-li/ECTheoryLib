import ECTheoryLib.Analysis.Linear.OnePlusOneEA.SortedRankDrift
import ECTheoryLib.Analysis.Linear.OnePlusOneEA.Reindex
import ECTheoryLib.Tools.Runtime.NonabsorbingFiniteRange

/-! Weight-independent upper bounds for the original positive-linear EA.
Mathlib's sorting permutation transports only the local kernel integral.
Existing real finite-range history tools keep the original infinite paths,
arbitrary initialization, first hit at time zero/infinity and update units. -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear ECTheoryLib.Tools.Drift
noncomputable section

/-- Complete rank drift on original coordinates, with arbitrary positive weight order and ties. -/
theorem SortedRankDriftLower {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Parent : Bits n) :
    SortedRankPotential Weights Parent/(4*Real.exp 1*(n : ℝ)) ≤
      ∫ Next, SortedRankPotential Weights Parent-SortedRankPotential Weights Next
        ∂(Step PositiveLength Weights Parent).toMeasure := by
  have Sorted : Monotone (fun i => Weights (Tuple.sort Weights i)) := Tuple.monotone_sort Weights
  have Bound := StandardSortedRankDriftLower PositiveLength (fun i => Weights (Tuple.sort Weights i))
    (fun i => Positive (Tuple.sort Weights i)) Sorted (ReindexBits (Tuple.sort Weights) Parent)
  have Equal := StepReindexIntegral PositiveLength Weights Parent (Tuple.sort Weights)
    (fun Next => RankPotential (ReindexBits (Tuple.sort Weights) Parent)-RankPotential Next)
  change _ ≤ ∫ Next, RankPotential (ReindexBits (Tuple.sort Weights) Parent)-
    RankPotential (ReindexBits (Tuple.sort Weights) Next) ∂(Step PositiveLength Weights Parent).toMeasure
  rw [Equal]
  exact Bound

/-- Zero-safe logarithmic upper bound for any initial law, including its initial optimum atom. -/
theorem RankRuntimeUpperBoundOfInitialLog {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Weights Initial ≤
      ENNReal.ofReal (4*Real.exp 1*(n : ℝ)*
        (∫ x, MultiplicativeDriftPotential 1 1 (SortedRankPotential Weights x) ∂Initial.toMeasure)) := by
  let Delta : ℝ := 1/(4*Real.exp 1*(n : ℝ))
  have NPositive : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have DeltaPositive : 0 < Delta := by dsimp only [Delta]; positivity
  have Bound := ECTheoryLib.Tools.Runtime.MultiplicativeRuntimeUpperBoundOfFiniteRangeNonabsorbing
    (Step PositiveLength Weights) Initial (SortedRankPotential Weights) (fun x => Score Weights x = 0)
    (fun _ => True) (RankRange n) 1 Delta (RankRangeZero n) (by norm_num) (RankRangeLower n)
    (SortedRankPotentialInRange Weights) (SortedRankPotentialZeroIffScore Weights Positive)
    (Filter.Eventually.of_forall (fun _ => True.intro))
    (fun _ => Filter.Eventually.of_forall (fun _ _ => True.intro)) DeltaPositive (by
      intro x _ _
      calc
        Delta*SortedRankPotential Weights x = SortedRankPotential Weights x/(4*Real.exp 1*(n : ℝ)) := by
          dsimp only [Delta]
          ring
        _ ≤ _ := SortedRankDriftLower PositiveLength Weights Positive x)
  have Scaling (s : ℝ) : MultiplicativeDriftPotential 1 Delta s =
      (4*Real.exp 1*(n : ℝ))*MultiplicativeDriftPotential 1 1 s := by
    by_cases Zero : s = 0
    · simp [MultiplicativeDriftPotential, Zero]
    · simp only [MultiplicativeDriftPotential, if_neg Zero, div_one]
      simp only [Delta, div_div_eq_mul_div, div_one]
      ring
  have Functions : (fun x => MultiplicativeDriftPotential 1 Delta (SortedRankPotential Weights x)) =
      fun x => (4*Real.exp 1*(n : ℝ))*MultiplicativeDriftPotential 1 1 (SortedRankPotential Weights x) := by
    funext x
    exact Scaling _
  rw [Functions, integral_const_mul] at Bound
  exact Bound

/-- Coarse bound retaining the actual initial failure probability as a factor. -/
theorem RankRuntimeUpperBoundOfInitialFailure {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Weights Initial ≤
      ENNReal.ofReal ((4*Real.exp 1*(n : ℝ))*(1+Real.log (2*(n : ℝ)))*
        Initial.toMeasure.real {x | Score Weights x ≠ 0}) := by
  classical
  let A : Set (Bits n) := {x | Score Weights x ≠ 0}
  have NPositive : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have RangePositive : (1 : ℝ) ≤ 2*(n : ℝ) := by
    have OneN : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr PositiveLength
    linarith
  have Point (x : Bits n) : MultiplicativeDriftPotential 1 1 (SortedRankPotential Weights x) ≤
      A.indicator (fun _ => 1+Real.log (2*(n : ℝ))) x := by
    by_cases Zero : Score Weights x = 0
    · have VZero := (SortedRankPotentialZeroIffScore Weights Positive x).mpr Zero
      have Outside : x ∉ A := fun Member => Member Zero
      rw [Set.indicator_of_notMem Outside]
      simp [MultiplicativeDriftPotential, VZero]
    · have VNonzero : SortedRankPotential Weights x ≠ 0 :=
        fun VZero => Zero ((SortedRankPotentialZeroIffScore Weights Positive x).mp VZero)
      rw [Set.indicator_of_mem (show x ∈ A from Zero)]
      have Bound := MultiplicativePotentialUpperRange 1 (2*(n : ℝ)) (SortedRankPotential Weights x)
        (by norm_num) RangePositive (SortedRankPotentialGap Weights x) (SortedRankPotentialLeTwoN Weights x)
      simpa only [if_neg VNonzero, div_one] using Bound
  have Mean := integral_mono (μ := Initial.toMeasure) Integrable.of_finite Integrable.of_finite Point
  rw [integral_indicator_const _ (Set.to_countable A).measurableSet, smul_eq_mul] at Mean
  calc
    _ ≤ ENNReal.ofReal ((4*Real.exp 1*(n : ℝ))*
        (∫ x, MultiplicativeDriftPotential 1 1 (SortedRankPotential Weights x) ∂Initial.toMeasure)) :=
      RankRuntimeUpperBoundOfInitialLog PositiveLength Weights Positive Initial
    _ ≤ ENNReal.ofReal ((4*Real.exp 1*(n : ℝ))*(Initial.toMeasure.real A*(1+Real.log (2*(n : ℝ))))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left Mean (by positivity))
    _ = _ := by congr 1; ring

/-- Uniform weight-independent 4en(1+log(2n)) upper bound for every initial PMF. -/
theorem RankRuntimeUpperBound {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Weights Initial ≤
      ENNReal.ofReal ((4*Real.exp 1*(n : ℝ))*(1+Real.log (2*(n : ℝ)))) := by
  have NPositive : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have RangePositive : (1 : ℝ) ≤ 2*(n : ℝ) := by
    have OneN : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr PositiveLength
    linarith
  have Nonnegative : 0 ≤ (4*Real.exp 1*(n : ℝ))*(1+Real.log (2*(n : ℝ))) :=
    mul_nonneg (by positivity) (by linarith [Real.log_nonneg RangePositive])
  calc
    _ ≤ _ := RankRuntimeUpperBoundOfInitialFailure PositiveLength Weights Positive Initial
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right Nonnegative measureReal_le_one)

/-- Fixed-state form keeps the optimum at time zero, using the same real logarithmic potential. -/
theorem RankRuntimeUpperBoundFromState {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Parent : Bits n) :
    ExpectedRuntime PositiveLength Weights (PMF.pure Parent) ≤
      ENNReal.ofReal ((4*Real.exp 1*(n : ℝ))*MultiplicativeDriftPotential 1 1 (SortedRankPotential Weights Parent)) := by
  simpa only [PMF.toMeasure_pure, integral_dirac] using
    RankRuntimeUpperBoundOfInitialLog PositiveLength Weights Positive (PMF.pure Parent)

/-- The genuine original hitting time has finite expectation under every initial law. -/
theorem PositiveLinearExpectedRuntimeFinite {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Weights Initial < ⊤ :=
  (RankRuntimeUpperBound PositiveLength Weights Positive Initial).trans_lt ENNReal.ofReal_lt_top

/-- Explicit finite lower/upper comparison on the same original uniformly initialized kernel.
This statement makes no asymptotic BigO/Theta claim. -/
theorem UniformRankRuntimeBounds {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) :
    ENNReal.ofReal ((n : ℝ)*(1+Real.log (n : ℝ))/96) ≤
      ExpectedRuntime PositiveLength Weights (OnePlusOneEAInit n) ∧
    ExpectedRuntime PositiveLength Weights (OnePlusOneEAInit n) ≤
      ENNReal.ofReal ((4*Real.exp 1*(n : ℝ))*(1+Real.log (2*(n : ℝ)))) :=
  ⟨UniformRuntimeLower PositiveLength Weights Positive,
    RankRuntimeUpperBound PositiveLength Weights Positive (OnePlusOneEAInit n)⟩

end
end ECTheoryLib.Analysis.EALinearMinimization

