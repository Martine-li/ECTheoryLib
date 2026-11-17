import ECTheoryLib.Probability.Sampling.CouponCollector
import ECTheoryLib.Analysis.OneMax.RLS.ExactRuntime
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Exact and asymptotic coupon-collector runtime

Source: Doerr, Theorem 1.9.1, printed page 35, in Theory of Evolutionary
Computation (2020). Prove actual update/kernel equality with RLS before
reusing n H_k; reuse Mathlib harmonic asymptotics for the ratio limit.
-/

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory ECTheoryLib.Probability
open ECTheoryLib.Probability.CouponCollector
noncomputable section

/-- Uniform coupon collection and OneMax RLS have identical deterministic
updates on the Boolean record, including repeated draws. -/
theorem CollectEqRLSUpdate {n : ℕ} (x : CouponCollector.State n) (i : Fin n) :
    CouponCollector.Collect x i=RLSOnOneMax.Update x i := by
  cases Bit : x i with
  | false =>
    rw [RLSOnOneMax.RLSAcceptsZeroFlip x i Bit]
    funext j
    by_cases Same : j=i
    · subst j
      simp [CouponCollector.Collect,OnebitMutation,Bit]
    · simp [CouponCollector.Collect,OnebitMutation,Same]
  | true =>
    rw [RLSOnOneMax.RLSRejectsOneFlip x i Bit]
    funext j
    by_cases Same : j=i
    · subst j
      simp [CouponCollector.Collect,Bit]
    · simp [CouponCollector.Collect,Same]

/-- Equality of actual transition PMFs, not just equality of mean drift. -/
theorem StepEqRLS {n : ℕ} (Positive : 0<n) : CouponCollector.Step n=RLSOnOneMax.Step Positive := by
  funext x
  unfold CouponCollector.Step
  rw [dif_pos Positive,RLSOnOneMax.Step,RLSStepEqUniformUpdate]
  have Updates : CouponCollector.Collect x=RLSOnOneMax.Update x := funext (CollectEqRLSUpdate x)
  rw [Updates]
  rfl

/-- Exact expectation from any initial set of collected coupons. -/
theorem FixedExpectedDraws {n : ℕ} (Positive : 0<n) (x : CouponCollector.State n) :
    ExpectedHittingTime (CouponCollector.Step n) CouponCollector.Complete (PMF.pure x)=
      ENNReal.ofReal ((n : ℝ)*(harmonic (RLSOnOneMax.ZeroCount x) : ℝ)) := by
  rw [StepEqRLS Positive]
  exact RLSOnOneMax.FixedRuntimeExact Positive x

/-- Doerr Theorem 1.9.1: n H_n draws from an empty collection. The empty
coupon universe is also covered and requires no fictitious uniform draw. -/
theorem ExpectedDrawsExact (n : ℕ) : CouponCollector.ExpectedDraws n=
    ENNReal.ofReal ((n : ℝ)*(harmonic n : ℝ)) := by
  by_cases Positive : 0<n
  · have Missing : RLSOnOneMax.ZeroCount (CouponCollector.Empty n)=n := by
      simp [RLSOnOneMax.ZeroCount,Problems.OneMax.ZeroCount,OneMax,CouponCollector.Empty]
    have Equal := FixedExpectedDraws Positive (CouponCollector.Empty n)
    rwa [Missing] at Equal
  · have Zero : n=0 := Nat.eq_zero_of_not_pos Positive
    subst n
    rw [CouponCollector.ExpectedDraws,ExpectedHittingTimeOfPureTarget _ _ _ (by intro i; exact Fin.elim0 i)]
    simp

end
end ECTheoryLib.Analysis.CouponCollector

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory Filter ECTheoryLib.Probability
open scoped Topology
noncomputable section

/-- The expected number of draws is finite, with its exact real value. -/
theorem ExpectedDrawsReal (n : ℕ) : (CouponCollector.ExpectedDraws n).toReal=
    (n : ℝ)*(harmonic n : ℝ) := by
  rw [ExpectedDrawsExact,ENNReal.toReal_ofReal]
  have HarmonicNonnegative : (0 : ℝ)≤harmonic n := by
    have Lower := log_add_one_le_harmonic n
    exact (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))).trans Lower
  exact mul_nonneg (Nat.cast_nonneg _) HarmonicNonnegative

/-- Doerr Theorem 1.9.1's (1+o(1)) n log n statement, expressed as a ratio
limit. Mathlib already proves harmonic n - log n tends to Euler's constant. -/
theorem ExpectedDrawsAsymptotic :
    Tendsto (fun n : ℕ => (CouponCollector.ExpectedDraws n).toReal/((n : ℝ)*Real.log n))
      atTop (𝓝 1) := by
  have LogGrowth : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ErrorDecay := Real.tendsto_harmonic_sub_log.div_atTop LogGrowth
  have Ratio : Tendsto (fun n : ℕ => ((harmonic n : ℝ)-Real.log n)/Real.log n+1) atTop (𝓝 1) := by
    simpa using ErrorDecay.add_const 1
  apply Ratio.congr'
  filter_upwards [eventually_ge_atTop 2] with n Large
  rw [ExpectedDrawsReal]
  have Positive : (0 : ℝ)<n := Nat.cast_pos.mpr (by omega)
  have LogPositive : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast Large)
  field_simp [Positive.ne',LogPositive.ne']
  ring

end
end ECTheoryLib.Analysis.CouponCollector
