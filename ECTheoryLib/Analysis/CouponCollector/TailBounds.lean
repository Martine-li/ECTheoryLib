import ECTheoryLib.Analysis.CouponCollector.ExactRuntime
import ECTheoryLib.Analysis.OneMax.RLS.TailBounds

/-!
# Coupon-collector upper tails with explicit integer thresholds

Source: Doerr Theorem 1.9.2, printed page 36. The printed closed
thresholds fail at n=2; retain strict ceiling tails or the next-integer
closed event. The geometric contraction also covers delta=1 and time zero.
-/

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Strict tail at an integer number of draws. The initial record may
already contain coupons; its expected missing count is retained. -/
theorem RuntimeTailAtTime {n : ℕ} (Positive : 0<n) (Initial : PMF (CouponCollector.State n)) (t : ℕ) :
    (PathMeasure (CouponCollector.Step n) Initial)
      {Path | (t : WithTop ℕ)<FirstHittingTime CouponCollector.Complete Path}≤
        ENNReal.ofReal (Real.exp (-(t : ℝ)/(n : ℝ))*(∫ x, RLSOnOneMax.Potential x ∂Initial.toMeasure)) := by
  rw [StepEqRLS Positive]
  exact RLSOnOneMax.RuntimeTailAtTime Positive Initial t

/-- A precise rounded version of the additive coupon upper tail.
The strict event is deliberate; the printed closed real threshold can fail. -/
theorem AdditiveUpperTailCeiling {n : ℕ} (Positive : 0<n) (ε : ℝ) (Nonnegative : 0≤ε) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | (⌈(n : ℝ)*Real.log n+ε*n⌉₊ : WithTop ℕ)<FirstHittingTime CouponCollector.Complete Path}≤
        ENNReal.ofReal (Real.exp (-ε)) := by
  have Missing : RLSOnOneMax.ZeroCount (CouponCollector.Empty n)=n := by
    simp [RLSOnOneMax.ZeroCount,Problems.OneMax.ZeroCount,OneMax,CouponCollector.Empty]
  have Bound := RLSOnOneMax.FixedRuntimeUpperTail Positive (CouponCollector.Empty n)
    (by rwa [Missing]) ε Nonnegative
  rw [Missing] at Bound
  have Threshold : (n : ℝ)*(Real.log n+ε)=n*Real.log n+ε*n := by ring
  rw [Threshold,← StepEqRLS Positive] at Bound
  exact Bound

/-- The power-form version uses the same integer ceiling convention. -/
theorem MultiplicativeUpperTailCeiling {n : ℕ} (Positive : 0<n) (ε : ℝ) (Nonnegative : 0≤ε) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | (⌈(1+ε)*(n : ℝ)*Real.log n⌉₊ : WithTop ℕ)<FirstHittingTime CouponCollector.Complete Path}≤
        ENNReal.ofReal ((n : ℝ)^(-ε)) := by
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr Positive
  have LogNonnegative : 0≤Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr Positive)
  have Bound := AdditiveUpperTailCeiling Positive (ε*Real.log n) (mul_nonneg Nonnegative LogNonnegative)
  have Threshold : (n : ℝ)*Real.log n+(ε*Real.log n)*n=(1+ε)*n*Real.log n := by ring
  have Power : Real.exp (-(ε*Real.log n))=(n : ℝ)^(-ε) := by
    rw [Real.rpow_def_of_pos PositiveN]
    congr 1
    ring
  rwa [Threshold,Power] at Bound

/-- For a closed event, move to the next integer draw count explicitly. -/
theorem AdditiveUpperTailClosedNext {n : ℕ} (Positive : 0<n) (ε : ℝ) (Nonnegative : 0≤ε) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | ((⌈(n : ℝ)*Real.log n+ε*n⌉₊+1 : ℕ) : WithTop ℕ)≤FirstHittingTime CouponCollector.Complete Path}≤
        ENNReal.ofReal (Real.exp (-ε)) := by
  have Bound := AdditiveUpperTailCeiling Positive ε Nonnegative
  have Event : {Path : ℕ → CouponCollector.State n | ((⌈(n : ℝ)*Real.log n+ε*n⌉₊+1 : ℕ) : WithTop ℕ)≤FirstHittingTime CouponCollector.Complete Path}=
      {Path | (⌈(n : ℝ)*Real.log n+ε*n⌉₊ : WithTop ℕ)<FirstHittingTime CouponCollector.Complete Path} := by
    ext Path
    change ((⌈(n : ℝ)*Real.log n+ε*n⌉₊+1 : ℕ) : WithTop ℕ)≤FirstHittingTime CouponCollector.Complete Path ↔
      (⌈(n : ℝ)*Real.log n+ε*n⌉₊ : WithTop ℕ)<FirstHittingTime CouponCollector.Complete Path
    generalize FirstHittingTime CouponCollector.Complete Path=z
    cases z with
    | top => simp
    | coe k =>
      exact WithTop.coe_le_coe.trans (Nat.succ_le_iff.trans WithTop.coe_lt_coe.symm)
  rwa [Event]

end
end ECTheoryLib.Analysis.CouponCollector

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Runtime
noncomputable section

/-- Keep the exact contraction factor before replacing it by an exponential.
For a singleton universe the coefficient is zero, including the `t = 0`
boundary where the power is one. -/
theorem RuntimeGeometricTailAtTime {n : ℕ} (Positive : 0<n)
    (Initial : PMF (CouponCollector.State n)) (t : ℕ) :
    (PathMeasure (CouponCollector.Step n) Initial)
      {Path | (t : WithTop ℕ)<FirstHittingTime CouponCollector.Complete Path}≤
        ENNReal.ofReal ((1-1/(n : ℝ))^t*(∫ x, RLSOnOneMax.Potential x ∂Initial.toMeasure)) := by
  rw [StepEqRLS Positive]
  let S : Finset ℝ := Finset.univ.image (RLSOnOneMax.Potential (n := n))
  have Values (x : CouponCollector.State n) : RLSOnOneMax.Potential x∈S :=
    Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  have StateLower : ∀ s∈S, s=0 ∨ (1 : ℝ)≤s := by
    intro s InS
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp InS
    by_cases Zero : RLSOnOneMax.ZeroCount x=0
    · left
      exact Nat.cast_eq_zero.mpr Zero
    · right
      change (1 : ℝ)≤(RLSOnOneMax.ZeroCount x : ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero
  have PreservesZero : ∀ x : CouponCollector.State n,
      ∀ᵐ y ∂(RLSOnOneMax.Step Positive x).toMeasure,
        True → RLSOnOneMax.Potential x=0 → RLSOnOneMax.Potential y=0 := by
    intro x
    filter_upwards [RLSOnOneMax.StepPreservesZeroCount Positive x] with y Preserves
    intro _ Zero
    exact Nat.cast_eq_zero.mpr (Preserves (Nat.cast_eq_zero.mp Zero))
  have LocalDrift : ∀ x : CouponCollector.State n, True → RLSOnOneMax.Potential x≠0 →
      (1/(n : ℝ))*RLSOnOneMax.Potential x≤
        ∫ y, RLSOnOneMax.Potential x-RLSOnOneMax.Potential y ∂(RLSOnOneMax.Step Positive x).toMeasure := by
    intro x _ _
    rw [RLSOnOneMax.OneStepDrift Positive x]
    exact le_of_eq (by ring)
  have Bound := MultiplicativeRuntimeGeometricTailOfFiniteRange
    (RLSOnOneMax.Step Positive) Initial RLSOnOneMax.Potential RLSOnOneMax.IsTarget
    (fun _ => True) S 1 (1/(n : ℝ))
    (by simpa using one_div_le_one_div_of_le (show (0 : ℝ)<1 by norm_num) (Nat.one_le_cast.mpr Positive))
    (by norm_num) StateLower Values RLSOnOneMax.PotentialEqZeroIffTarget
    (Filter.Eventually.of_forall (fun _ => True.intro))
    (fun _ => Filter.Eventually.of_forall (fun _ _ => True.intro)) PreservesZero LocalDrift t
  rw [div_one] at Bound
  exact Bound

/-- The actual empty-start collector satisfies the familiar finite-time
bound `n (1 - 1/n)^t`; no independence of hitting stages is assumed. -/
theorem EmptyRuntimeGeometricTailAtTime {n : ℕ} (Positive : 0<n) (t : ℕ) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | (t : WithTop ℕ)<FirstHittingTime CouponCollector.Complete Path}≤
        ENNReal.ofReal ((n : ℝ)*(1-1/(n : ℝ))^t) := by
  have Bound := RuntimeGeometricTailAtTime Positive (PMF.pure (CouponCollector.Empty n)) t
  have Mean : (∫ x, RLSOnOneMax.Potential x ∂(PMF.pure (CouponCollector.Empty n)).toMeasure)=(n : ℝ) := by
    rw [PMF.toMeasure_pure,integral_dirac]
    simp [RLSOnOneMax.Potential,RLSOnOneMax.ZeroCount,Problems.OneMax.ZeroCount,
      OneMax,CouponCollector.Empty]
  rw [Mean,mul_comm] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.CouponCollector
