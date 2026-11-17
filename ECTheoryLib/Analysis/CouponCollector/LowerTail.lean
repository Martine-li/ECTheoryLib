import ECTheoryLib.Probability.Sampling.CouponCoverage
import ECTheoryLib.Probability.Distributions.GeometricWaiting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Doubly exponential lower tails for actual coupon collection

Source: Doerr Theorem 1.9.3, printed pages 36-37. Integer closed events
use the natural floor; their real-threshold meaning is verified even
for negative thresholds and infinite hitting times. The singleton
universe is handled before using division by n-1.
-/

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- A finite-time lower-tail bound from actual joint coverage. -/
theorem RuntimeLowerTailAtTime {n : ℕ} (Positive : 0<n) (t : ℕ) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | FirstHittingTime CouponCollector.Complete Path≤(t : WithTop ℕ)}≤
        ENNReal.ofReal (Real.exp (-(n : ℝ)*(1-1/(n : ℝ))^t)) := by
  have NPositive : (0 : ℝ)<n := Nat.cast_pos.mpr Positive
  have FactorNonnegative : 0≤1-1/(n : ℝ) := by
    have Small : 1/(n : ℝ)≤1 := by
      simpa using one_div_le_one_div_of_le (show (0 : ℝ)<1 by norm_num) (Nat.one_le_cast.mpr Positive)
    linarith
  have FactorAtMostOne : 1-1/(n : ℝ)≤1 := by
    have := (one_div_pos.mpr NPositive).le
    linarith
  have BaseNonnegative : 0≤1-(1-1/(n : ℝ))^t :=
    sub_nonneg.mpr (pow_le_one₀ FactorNonnegative FactorAtMostOne)
  have Coverage := CouponCollector.CoverageProbabilityUpper Positive Finset.univ t
  rw [Finset.card_univ,Fintype.card_fin] at Coverage
  rw [← CouponCollector.CompleteRuntimeProbability Positive t] at Coverage
  have PowerBound : (1-(1-1/(n : ℝ))^t)^n≤Real.exp (-(n : ℝ)*(1-1/(n : ℝ))^t) := by
    have Linear : 1-(1-1/(n : ℝ))^t≤Real.exp (-(1-1/(n : ℝ))^t) := by
      simpa only [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-(1-1/(n : ℝ))^t)
    calc
      (1-(1-1/(n : ℝ))^t)^n≤(Real.exp (-(1-1/(n : ℝ))^t))^n :=
        pow_le_pow_left₀ BaseNonnegative Linear n
      _=Real.exp (-(n : ℝ)*(1-1/(n : ℝ))^t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact Coverage.trans PowerBound

/-- The missed-coupon probability is bounded below by the standard
exponential expression; reuse Mathlib's logarithmic inequality. -/
theorem MissingProbabilityExponentialLower {n : ℕ} (AtLeastTwo : 2≤n) (t : ℕ) :
    Real.exp (-(t : ℝ)/((n : ℝ)-1))≤(1-1/(n : ℝ))^t := by
  have NAboveOne : (1 : ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have NPositive : (0 : ℝ)<n := by linarith
  have Bound := BernoulliFailurePowerExponentialLower (1/(n : ℝ))
    ((div_lt_one NPositive).mpr NAboveOne) t
  have Exponent : -(t : ℝ)*(1/(n : ℝ))/(1-1/(n : ℝ))= -(t : ℝ)/((n : ℝ)-1) := by
    field_simp
  rwa [Exponent] at Bound


/-- Integer draw counts below the additive logarithmic threshold obey
the doubly exponential lower-tail bound. -/
theorem AdditiveLowerTailAtTime {n : ℕ} (AtLeastTwo : 2≤n) (ε : ℝ) (t : ℕ)
    (Before : (t : ℝ)≤((n : ℝ)-1)*Real.log n-ε*((n : ℝ)-1)) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | FirstHittingTime CouponCollector.Complete Path≤(t : WithTop ℕ)}≤
        ENNReal.ofReal (Real.exp (-Real.exp ε)) := by
  have Positive : 0<n := lt_of_lt_of_le (by decide : 0<2) AtLeastTwo
  apply (RuntimeLowerTailAtTime Positive t).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have NPositive : (0 : ℝ)<n := Nat.cast_pos.mpr Positive
  have DenPositive : (0 : ℝ)<(n : ℝ)-1 := by exact_mod_cast (show 0<(n : ℤ)-1 by omega)
  have Exponent : ε-Real.log n≤ -(t : ℝ)/((n : ℝ)-1) := by
    apply (le_div_iff₀ DenPositive).mpr
    nlinarith
  have Missing := (Real.exp_le_exp.mpr Exponent).trans (MissingProbabilityExponentialLower AtLeastTwo t)
  have Scaled := mul_le_mul_of_nonneg_left Missing NPositive.le
  rw [Real.exp_sub,Real.exp_log NPositive] at Scaled
  have Cancel : (n : ℝ)*(Real.exp ε/(n : ℝ))=Real.exp ε := by field_simp
  rw [Cancel] at Scaled
  linarith

/-- A positive universe is incomplete at the empty initialization. -/
theorem EmptyRuntimeNotZero {n : ℕ} (Positive : 0<n) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | FirstHittingTime CouponCollector.Complete Path≤(0 : WithTop ℕ)}=0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [PathMeasureInitialPure (CouponCollector.Step n) (CouponCollector.Empty n)]
    with Path Initial
  intro Hit
  have Goal := (FirstHittingTimeEqZeroIff CouponCollector.Complete Path).mp
    (le_antisymm Hit bot_le)
  have Seen := Goal ⟨0,Positive⟩
  rw [Initial] at Seen
  simp [CouponCollector.Empty] at Seen

/-- Natural flooring gives a closed lower-tail threshold. For negative
thresholds the natural floor is zero, and the empty start has no mass there.
The singleton universe is handled separately, since n-1 vanishes. -/
theorem AdditiveLowerTailFloor {n : ℕ} (Positive : 0<n) (ε : ℝ) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | FirstHittingTime CouponCollector.Complete Path≤
        (⌊((n : ℝ)-1)*Real.log n-ε*((n : ℝ)-1)⌋₊ : WithTop ℕ)}≤
          ENNReal.ofReal (Real.exp (-Real.exp ε)) := by
  by_cases One : n=1
  · subst n
    norm_num only [Nat.cast_one,sub_self,zero_mul,mul_zero,sub_zero,Nat.floor_zero]
    rw [EmptyRuntimeNotZero (by decide : 0<1)]
    exact zero_le
  · have AtLeastTwo : 2≤n := by omega
    by_cases Nonnegative : 0≤((n : ℝ)-1)*Real.log n-ε*((n : ℝ)-1)
    · exact AdditiveLowerTailAtTime AtLeastTwo ε _ (Nat.floor_le Nonnegative)
    · rw [Nat.floor_of_nonpos (le_of_not_ge Nonnegative)]
      change (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
        {Path | FirstHittingTime CouponCollector.Complete Path≤(0 : WithTop ℕ)}≤_
      rw [EmptyRuntimeNotZero Positive]
      exact zero_le

/-- The equivalent power-form lower tail, with the same closed floor. -/
theorem MultiplicativeLowerTailFloor {n : ℕ} (Positive : 0<n) (ε : ℝ) :
    (PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)))
      {Path | FirstHittingTime CouponCollector.Complete Path≤
        (⌊(1-ε)*((n : ℝ)-1)*Real.log n⌋₊ : WithTop ℕ)}≤
          ENNReal.ofReal (Real.exp (-(n : ℝ)^ε)) := by
  have Bound := AdditiveLowerTailFloor Positive (ε*Real.log n)
  have Threshold : ((n : ℝ)-1)*Real.log n-(ε*Real.log n)*((n : ℝ)-1)=
      (1-ε)*((n : ℝ)-1)*Real.log n := by ring
  have Power : Real.exp (ε*Real.log (n : ℝ))=(n : ℝ)^ε := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr Positive)]
    congr 1
    ring
  rwa [Threshold,Power] at Bound

/-- The floor event has precisely the intended real-threshold semantics,
including negative thresholds and paths that never finish. -/
theorem RuntimeFloorEventIff {n : ℕ} (Positive : 0<n) (a : ℝ) :
    ∀ᵐ Path ∂PathMeasure (CouponCollector.Step n) (PMF.pure (CouponCollector.Empty n)),
      FirstHittingTime CouponCollector.Complete Path≤(⌊a⌋₊ : WithTop ℕ) ↔
        ∃ k : ℕ, FirstHittingTime CouponCollector.Complete Path=(k : WithTop ℕ) ∧ (k : ℝ)≤a := by
  have NoZero := measure_eq_zero_iff_ae_notMem.mp (EmptyRuntimeNotZero Positive)
  filter_upwards [NoZero] with Path NotZero
  have Nonzero : FirstHittingTime CouponCollector.Complete Path≠0 := by
    intro Zero
    exact NotZero (le_of_eq Zero)
  generalize Eq : FirstHittingTime CouponCollector.Complete Path=z at *
  cases z with
  | top => simp
  | coe k =>
    have KNonzero : k≠0 := by
      intro Zero
      subst k
      exact Nonzero rfl
    constructor
    · intro Before
      exact ⟨k,rfl,(Nat.le_floor_iff' KNonzero).mp (WithTop.coe_le_coe.mp Before)⟩
    · rintro ⟨j,Equal,Before⟩
      have Same : k=j := WithTop.coe_inj.mp Equal
      subst j
      exact WithTop.coe_le_coe.mpr ((Nat.le_floor_iff' KNonzero).mpr Before)

end
end ECTheoryLib.Analysis.CouponCollector
