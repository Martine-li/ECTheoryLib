import ECTheoryLib.Analysis.Linear.OnePlusOneEA.RuntimeUpperBounds
import ECTheoryLib.Tools.Runtime.Multiplicative.NonabsorbingTail

/-! Upper tails of the original standard weak-minimizing positive-linear EA.
Arbitrary initialization retains its initial failure probability. -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open ECTheoryLib.Tools.Runtime
noncomputable section

private theorem NaturalClosedTailEndpoint (k : ℕ) (T : WithTop ℕ) :
    ((k + 1 : ℕ) : WithTop ℕ) ≤ T ↔ (k : WithTop ℕ) < T := by
  change ((k + 1 : ℕ) : ENat) ≤ T ↔ (k : ENat) < T
  simpa only [Nat.cast_add,Nat.cast_one] using (ENat.natCast_add_one_le_iff (m := k) (n := T))

private theorem RankKernelTailDrift {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Parent : Bits n) :
    (1 / (4 * Real.exp 1 * (n : ℝ))) * SortedRankPotential Weights Parent ≤
      ∫ Next, SortedRankPotential Weights Parent - SortedRankPotential Weights Next
        ∂(Step PositiveLength Weights Parent).toMeasure := by
  calc
    _ = SortedRankPotential Weights Parent / (4 * Real.exp 1 * (n : ℝ)) := by ring
    _ ≤ _ := SortedRankDriftLower PositiveLength Weights Positive Parent

/-- The actual initial moment,with initial goals contributing exactly zero. -/
theorem SortedRankInitialMeanUpperBound {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ i, 0 < Weights i) (Initial : PMF (Bits n)) :
    (∫ x, SortedRankPotential Weights x ∂Initial.toMeasure) ≤
      (2 * (n : ℝ)) * Initial.toMeasure.real {x | Score Weights x ≠ 0} := by
  classical
  let A : Set (Bits n) := {x | Score Weights x ≠ 0}
  have Point (x : Bits n) : SortedRankPotential Weights x ≤
      A.indicator (fun _ => 2 * (n : ℝ)) x := by
    by_cases Zero : Score Weights x = 0
    · rw [(SortedRankPotentialZeroIffScore Weights Positive x).mpr Zero,
        Set.indicator_of_notMem (show x ∉ A from fun Member => Member Zero)]
    · rw [Set.indicator_of_mem (show x ∈ A from Zero)]
      exact SortedRankPotentialLeTwoN Weights x
  have Mean := integral_mono (μ := Initial.toMeasure) Integrable.of_finite Integrable.of_finite Point
  rw [integral_indicator_const _ (Set.to_countable A).measurableSet,smul_eq_mul] at Mean
  calc
    _ ≤ Initial.toMeasure.real A * (2 * (n : ℝ)) := Mean
    _ = _ := by ring

/-- True moment upper tail for every initial PMF;no finite-runtime input is used. -/
theorem RankRuntimeTailAtTime {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Initial : PMF (Bits n)) (t : ℕ) :
    (PathMeasure (Step PositiveLength Weights) Initial)
      {Path | (t : WithTop ℕ) < FirstHittingTime (fun x => Score Weights x = 0) Path} ≤
      ENNReal.ofReal (Real.exp (-(t : ℝ) / (4 * Real.exp 1 * (n : ℝ))) *
        (∫ x, SortedRankPotential Weights x ∂Initial.toMeasure)) := by
  have Bound := MultiplicativeRuntimeTailAtTimeOfFiniteRangeNonabsorbing
    (Step PositiveLength Weights) Initial (SortedRankPotential Weights)
    (fun x => Score Weights x = 0) (fun _ => True) (RankRange n)
    1 (1 / (4 * Real.exp 1 * (n : ℝ))) (by norm_num) (RankRangeLower n)
    (SortedRankPotentialInRange Weights) (SortedRankPotentialZeroIffScore Weights Positive)
    (ae_of_all _ (fun _ => True.intro)) (fun _ => ae_of_all _ (fun _ _ => True.intro))
    (fun x _ _ => RankKernelTailDrift PositiveLength Weights Positive x) t
  have Exponent : -(1 / (4 * Real.exp 1 * (n : ℝ))) * (t : ℝ) =
      -(t : ℝ) / (4 * Real.exp 1 * (n : ℝ)) := by ring
  simpa only [Exponent,div_one] using Bound

/-- The common range bound keeps the actual initial failure mass as a factor. -/
theorem RankRuntimeTailAtTimeOfInitialFailure {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Initial : PMF (Bits n)) (t : ℕ) :
    (PathMeasure (Step PositiveLength Weights) Initial)
      {Path | (t : WithTop ℕ) < FirstHittingTime (fun x => Score Weights x = 0) Path} ≤
      ENNReal.ofReal ((2 * (n : ℝ)) * Initial.toMeasure.real {x | Score Weights x ≠ 0} *
        Real.exp (-(t : ℝ) / (4 * Real.exp 1 * (n : ℝ)))) := by
  refine (RankRuntimeTailAtTime PositiveLength Weights Positive Initial t).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ Real.exp (-(t : ℝ) / (4 * Real.exp 1 * (n : ℝ))) *
        ((2 * (n : ℝ)) * Initial.toMeasure.real {x | Score Weights x ≠ 0}) :=
      mul_le_mul_of_nonneg_left (SortedRankInitialMeanUpperBound Weights Positive Initial)
        (Real.exp_pos _).le
    _ = _ := by ring

/-- A natural-ceiling tail derived from the random-initial moment bound.
It holds for every real r;the customary source regime is r>=0. -/
theorem RankRuntimeUpperTailOfInitialFailure {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Initial : PMF (Bits n)) (r : ℝ) :
    (PathMeasure (Step PositiveLength Weights) Initial)
      {Path | (⌈(4 * Real.exp 1 * (n : ℝ)) * (Real.log (2 * (n : ℝ)) + r)⌉₊ : WithTop ℕ) <
        FirstHittingTime (fun x => Score Weights x = 0) Path} ≤
      ENNReal.ofReal (Initial.toMeasure.real {x | Score Weights x ≠ 0} * Real.exp (-r)) := by
  let C : ℝ := 4 * Real.exp 1 * (n : ℝ)
  let B : ℝ := 2 * (n : ℝ)
  let k : ℕ := ⌈C * (Real.log B + r)⌉₊
  have NPositive : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have CPositive : 0 < C := by dsimp [C]; positivity
  have BPositive : 0 < B := by dsimp [B]; positivity
  have CeilBound : C * (Real.log B + r) ≤ (k : ℝ) := Nat.le_ceil _
  have Quotient : Real.log B + r ≤ (k : ℝ) / C :=
    (le_div_iff₀ CPositive).mpr (by simpa only [mul_comm] using CeilBound)
  have Exponent : -(k : ℝ) / C + Real.log B ≤ -r := by
    rw [neg_div]
    linarith only [Quotient]
  have Contract : B * Real.exp (-(k : ℝ) / C) ≤ Real.exp (-r) := by
    calc
      _ = Real.exp (-(k : ℝ) / C + Real.log B) := by
        rw [Real.exp_add,Real.exp_log BPositive]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr Exponent
  refine (RankRuntimeTailAtTimeOfInitialFailure PositiveLength Weights Positive Initial k).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ = Initial.toMeasure.real {x | Score Weights x ≠ 0} *
        (B * Real.exp (-(k : ℝ) / C)) := by dsimp [B,C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left Contract measureReal_nonneg

/-- Coarse weight-independent natural-ceiling tail for every initial law. -/
theorem RankRuntimeUpperTail {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Initial : PMF (Bits n)) (r : ℝ) :
    (PathMeasure (Step PositiveLength Weights) Initial)
      {Path | (⌈(4 * Real.exp 1 * (n : ℝ)) * (Real.log (2 * (n : ℝ)) + r)⌉₊ : WithTop ℕ) <
        FirstHittingTime (fun x => Score Weights x = 0) Path} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  refine (RankRuntimeUpperTailOfInitialFailure PositiveLength Weights Positive Initial r).trans
    (ENNReal.ofReal_le_ofReal ?_)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (measureReal_le_one (μ := Initial.toMeasure)
      (s := {x | Score Weights x ≠ 0})) (Real.exp_pos (-r)).le

/-- Closed integer tails use the strict threshold plus one,including T=infinity. -/
theorem RankClosedRuntimeUpperTailOfInitialFailure {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Initial : PMF (Bits n)) (r : ℝ) :
    (PathMeasure (Step PositiveLength Weights) Initial)
      {Path | ((⌈(4 * Real.exp 1 * (n : ℝ)) * (Real.log (2 * (n : ℝ)) + r)⌉₊ + 1 : ℕ) :
          WithTop ℕ) ≤ FirstHittingTime (fun x => Score Weights x = 0) Path} ≤
      ENNReal.ofReal (Initial.toMeasure.real {x | Score Weights x ≠ 0} * Real.exp (-r)) := by
  have Events :
      {Path : ℕ → Bits n | ((⌈(4 * Real.exp 1 * (n : ℝ)) *
          (Real.log (2 * (n : ℝ)) + r)⌉₊ + 1 : ℕ) : WithTop ℕ) ≤
        FirstHittingTime (fun x => Score Weights x = 0) Path} =
      {Path : ℕ → Bits n | (⌈(4 * Real.exp 1 * (n : ℝ)) *
          (Real.log (2 * (n : ℝ)) + r)⌉₊ : WithTop ℕ) <
        FirstHittingTime (fun x => Score Weights x = 0) Path} := by
    ext Path
    exact NaturalClosedTailEndpoint _ _
  rw [Events]
  exact RankRuntimeUpperTailOfInitialFailure PositiveLength Weights Positive Initial r

/-- Direct fixed-positive-initial scalar-theorem call on the original EA paths. -/
theorem FixedRankRuntimeUpperTail {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Parent : Bits n)
    (Away : Score Weights Parent ≠ 0) (r : ℝ) (NonnegativeR : 0 ≤ r) :
    (PathMeasure (Step PositiveLength Weights) (PMF.pure Parent))
      {Path | (⌈(4 * Real.exp 1 * (n : ℝ)) *
          (Real.log (SortedRankPotential Weights Parent) + r)⌉₊ : WithTop ℕ) <
        FirstHittingTime (fun x => Score Weights x = 0) Path} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have NPositive : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have DeltaPositive : 0 < (1 / (4 * Real.exp 1 * (n : ℝ))) := by positivity
  have InitialPositive : 0 < SortedRankPotential Weights Parent := by
    rcases SortedRankPotentialGap Weights Parent with Zero | Lower
    · exact (Away ((SortedRankPotentialZeroIffScore Weights Positive Parent).mp Zero)).elim
    · linarith
  have Bound := MultiplicativeRuntimeUpperTailOfFiniteRangeNonabsorbing
    (Step PositiveLength Weights) (PMF.pure Parent) (SortedRankPotential Weights)
    (fun x => Score Weights x = 0) (fun _ => True) (RankRange n)
    1 (1 / (4 * Real.exp 1 * (n : ℝ))) (SortedRankPotential Weights Parent)
    (RankRangeZero n) (by norm_num) (RankRangeLower n)
    (SortedRankPotentialInRange Weights) (SortedRankPotentialZeroIffScore Weights Positive)
    (ae_of_all _ (fun _ => True.intro)) (fun _ => ae_of_all _ (fun _ _ => True.intro)) DeltaPositive
    (fun x _ _ => RankKernelTailDrift PositiveLength Weights Positive x)
    (by simp [PMF.toMeasure_pure]) InitialPositive r NonnegativeR
  have Threshold : (r + Real.log (SortedRankPotential Weights Parent / 1)) /
      (1 / (4 * Real.exp 1 * (n : ℝ))) = (4 * Real.exp 1 * (n : ℝ)) *
        (Real.log (SortedRankPotential Weights Parent) + r) := by
    rw [div_one,one_div,div_inv_eq_mul]
    ring
  rwa [Threshold] at Bound

end
end ECTheoryLib.Analysis.EALinearMinimization

