import ECTheoryLib.Tools.Drift.GeometricJumpNegative
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Explicit and asymptotic exponential horizons for negative drift

The geometric-jump parameter is bounded below by a fixed positive constant/r.
Mathlib little-o and logarithmic growth absorb the prefactor under
r=o(L/log L). Base-e and base-two bounds are both given. These numerical
transformations inherit the model assumptions of the supplied finite-time bound.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability Filter Asymptotics
noncomputable section

theorem GeometricJumpMomentBoundScale (eta r : ℝ) :
    GeometricJumpMomentBound eta r=r*GeometricJumpMomentBound eta 1 := by
  dsimp [GeometricJumpMomentBound]
  ring

/-- For r>=1, the chosen exponent is bounded below by a positive constant
depending only on eta and delta, divided by r. -/
theorem GeometricJumpDriftExponentScale (eta Delta r : ℝ) (PositiveEta : 0<eta)
    (OneLeR : 1≤r) :
    GeometricJumpDriftExponent eta Delta 1/r ≤ GeometricJumpDriftExponent eta Delta r := by
  have PositiveR : 0<r := lt_of_lt_of_le zero_lt_one OneLeR
  have PositiveQ := GeometricJumpMomentRadiusPositive eta PositiveEta
  have PositiveC := GeometricJumpMomentBoundPositive eta 1 PositiveEta (by norm_num)
  let q := GeometricJumpMomentRadius eta
  let C := GeometricJumpMomentBound eta 1
  change min (q/2) (Delta*q^2/(8*C))/r ≤
    min (q/2) (Delta*q^2/(8*GeometricJumpMomentBound eta r))
  apply le_min
  · apply (div_le_iff₀ PositiveR).mpr
    apply (min_le_left _ _).trans
    have Scaled := mul_le_mul_of_nonneg_left OneLeR (show 0≤q/2 by positivity)
    simpa only [mul_one] using Scaled
  · calc
      _ ≤ (Delta*q^2/(8*C))/r := div_le_div_of_nonneg_right (min_le_right _ _) PositiveR.le
      _ = _ := by
        rw [GeometricJumpMomentBoundScale]
        dsimp [C]
        ring

/-- Explicit finite-size condition absorbing the prefactor C*r into the
exponential bound. It separates numerical asymptotics from process semantics. -/
theorem NegativeDriftExponentialHorizonValue (t L r C c Lambda : ℝ)
    (NonnegativeL : 0≤L) (PositiveR : 0<r) (PositiveC : 0<C)
    (ExponentLower : c/r≤Lambda)
    (LogPrefactor : Real.log (C*r)≤c*L/(4*r))
    (Horizon : t≤Real.exp (c*L/(2*r))) :
    t*(C*r)*Real.exp (-Lambda*L) ≤ Real.exp (-c*L/(4*r)) := by
  have Prefactor : C*r≤Real.exp (c*L/(4*r)) := by
    rw [← Real.exp_log (mul_pos PositiveC PositiveR)]
    exact Real.exp_le_exp.mpr LogPrefactor
  have Exponent : Real.exp (-Lambda*L)≤Real.exp (-c*L/r) := by
    apply Real.exp_le_exp.mpr
    have Scaled := mul_le_mul_of_nonneg_right ExponentLower NonnegativeL
    rw [div_mul_eq_mul_div] at Scaled
    simpa only [neg_mul, neg_div] using neg_le_neg Scaled
  calc
    _ ≤ Real.exp (c*L/(2*r))*Real.exp (c*L/(4*r))*Real.exp (-c*L/r) :=
      mul_le_mul (mul_le_mul Horizon Prefactor (mul_pos PositiveC PositiveR).le (Real.exp_pos _).le)
        Exponent (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- The corrected source condition r=o(L/log L), together with r>=1 and
L tending to infinity, eventually absorbs every fixed positive prefactor C. -/
theorem NegativeDriftLogPrefactorEventuallySmall {ι : Type*} (l : Filter ι)
    (L r : ι → ℝ) (Growth : Tendsto L l atTop)
    (OneLeR : ∀ᶠ n in l, 1≤r n)
    (SmallR : r =o[l] (fun n => L n/Real.log (L n)))
    (C c : ℝ) (PositiveC : 0<C) (PositiveCst : 0<c) :
    ∀ᶠ n in l, Real.log (C*r n)≤c*L n/(4*r n) := by
  let epsilon := min 1 (c/8)
  have PositiveEpsilon : 0<epsilon := lt_min zero_lt_one (div_pos PositiveCst (by norm_num))
  have EpsilonLeOne : epsilon≤1 := min_le_left _ _
  have EpsilonLeC : epsilon≤c/8 := min_le_right _ _
  have LogGrowth := Real.tendsto_log_atTop.comp Growth
  filter_upwards [OneLeR, Growth.eventually_gt_atTop 0,
    LogGrowth.eventually_ge_atTop (max 1 (Real.log C)), SmallR.bound PositiveEpsilon]
    with n LowerR PositiveL LargeLog RawBound
  have PositiveR : 0<r n := lt_of_lt_of_le zero_lt_one LowerR
  have OneLeLog : 1≤Real.log (L n) := (le_max_left _ _).trans LargeLog
  have ConstantLeLog : Real.log C≤Real.log (L n) := (le_max_right _ _).trans LargeLog
  have PositiveLog : 0<Real.log (L n) := lt_of_lt_of_le zero_lt_one OneLeLog
  have Bound : r n≤epsilon*(L n/Real.log (L n)) := by
    simpa only [Real.norm_eq_abs, abs_of_pos PositiveR,
      abs_of_pos (div_pos PositiveL PositiveLog)] using RawBound
  have ProductBound : r n*Real.log (L n)≤epsilon*L n := by
    apply (le_div_iff₀ PositiveLog).mp
    simpa only [mul_div_assoc] using Bound
  have RLeL : r n≤L n := by
    have LogScaled := mul_le_mul_of_nonneg_left OneLeLog PositiveR.le
    have EpsilonScaled := mul_le_mul_of_nonneg_right EpsilonLeOne PositiveL.le
    nlinarith
  have LogComparison : Real.log (C*r n)≤2*Real.log (L n) := by
    rw [Real.log_mul PositiveC.ne' PositiveR.ne']
    have LogR := Real.log_le_log PositiveR RLeL
    linarith
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<4) PositiveR)).mpr
  have Scaled := mul_le_mul_of_nonneg_left LogComparison PositiveR.le
  have SmallScaled := mul_le_mul_of_nonneg_right EpsilonLeC PositiveL.le
  nlinarith

/-- The same source assumption makes L/r tend to infinity; the resulting
exponential horizon grows and its lower-tail probability decays. -/
theorem NegativeDriftScaleTendsToInfinity {ι : Type*} (l : Filter ι)
    (L r : ι → ℝ) (Growth : Tendsto L l atTop)
    (OneLeR : ∀ᶠ n in l, 1≤r n)
    (SmallR : r =o[l] (fun n => L n/Real.log (L n))) :
    Tendsto (fun n => L n/r n) l atTop := by
  apply tendsto_atTop_mono' l _ (Real.tendsto_log_atTop.comp Growth)
  filter_upwards [OneLeR, Growth.eventually_gt_atTop 1, SmallR.bound zero_lt_one]
    with n LowerR LargeL RawBound
  have PositiveR : 0<r n := lt_of_lt_of_le zero_lt_one LowerR
  have PositiveL : 0<L n := zero_lt_one.trans LargeL
  have PositiveLog : 0<Real.log (L n) := Real.log_pos LargeL
  have Bound : r n≤L n/Real.log (L n) := by
    simpa only [Real.norm_eq_abs, abs_of_pos PositiveR,
      abs_of_pos (div_pos PositiveL PositiveLog), one_mul] using RawBound
  apply (le_div_iff₀ PositiveR).mpr
  have Product := (le_div_iff₀ PositiveLog).mp Bound
  change Real.log (L n)*r n≤L n
  simpa only [mul_comm] using Product

/-- Explicit exponential-time and probability scales under the corrected
r=o(L/log L) assumption. Any family of already established finite-time
geometric-jump bounds can be supplied, without rebuilding its stochastic model. -/
theorem GeometricJumpTailEventuallyExponential {ι : Type*} (l : Filter ι)
    (L r : ι → ℝ) (Growth : Tendsto L l atTop)
    (OneLeR : ∀ᶠ n in l, 1≤r n)
    (SmallR : r =o[l] (fun n => L n/Real.log (L n)))
    (eta Delta : ℝ) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta)
    (P : ι → ℕ → ENNReal)
    (Tail : ∀ᶠ n in l, ∀ t : ℕ, P n t ≤ ENNReal.ofReal
      ((t : ℝ)*GeometricJumpMomentBound eta (r n)*
        Real.exp (-GeometricJumpDriftExponent eta Delta (r n)*L n))) :
    ∀ᶠ n in l, ∀ t : ℕ,
      (t : ℝ)≤Real.exp (GeometricJumpDriftExponent eta Delta 1*L n/(2*r n)) →
      P n t ≤ ENNReal.ofReal (Real.exp (-GeometricJumpDriftExponent eta Delta 1*L n/(4*r n))) := by
  let C := GeometricJumpMomentBound eta 1
  let c := GeometricJumpDriftExponent eta Delta 1
  have PositiveC : 0<C := GeometricJumpMomentBoundPositive eta 1 PositiveEta (by norm_num)
  have PositiveCst : 0<c := GeometricJumpDriftExponentPositive eta Delta 1 PositiveEta PositiveDelta (by norm_num)
  have Prefactor := NegativeDriftLogPrefactorEventuallySmall l L r Growth OneLeR SmallR
    C c PositiveC PositiveCst
  filter_upwards [OneLeR, Growth.eventually_ge_atTop 0, Tail, Prefactor]
    with n LowerR NonnegativeL LocalTail LocalPrefactor
  intro t Horizon
  have PositiveR : 0<r n := lt_of_lt_of_le zero_lt_one LowerR
  have Bound := NegativeDriftExponentialHorizonValue (t : ℝ) (L n) (r n) C c
    (GeometricJumpDriftExponent eta Delta (r n)) NonnegativeL PositiveR PositiveC
    (GeometricJumpDriftExponentScale eta Delta (r n) PositiveEta LowerR) LocalPrefactor Horizon
  apply (LocalTail t).trans
  apply ENNReal.ofReal_le_ofReal
  rw [GeometricJumpMomentBoundScale, mul_comm (r n)]
  exact Bound

/-- Constant jump prefactors satisfy the corrected source asymptotic
condition for every family of interval widths tending to infinity. -/
theorem ConstantJumpPrefactorIsLittleO {ι : Type*} (l : Filter ι) (L : ι → ℝ)
    (Growth : Tendsto L l atTop) (r : ℝ) :
    (fun _ : ι => r) =o[l] (fun n => L n/Real.log (L n)) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [Growth.eventually_gt_atTop 1] with n LargeL
    have PositiveL : 0<L n := zero_lt_one.trans LargeL
    have Nonzero : L n/Real.log (L n)≠0 := div_ne_zero PositiveL.ne' (Real.log_pos LargeL).ne'
    exact fun Equal => (Nonzero Equal).elim
  · have Limit := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Growth).const_mul r
    convert Limit using 1
    · funext n
      simp only [Function.comp_apply, id_eq, div_eq_mul_inv, mul_inv_rev, inv_inv]
    · simp

/-- Base-two presentation of the corrected source conclusion, with one
explicit positive constant valid for both the time and probability exponents. -/
theorem GeometricJumpTailEventuallyDyadic {ι : Type*} (l : Filter ι)
    (L r : ι → ℝ) (Growth : Tendsto L l atTop)
    (OneLeR : ∀ᶠ n in l, 1≤r n)
    (SmallR : r =o[l] (fun n => L n/Real.log (L n)))
    (eta Delta : ℝ) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta)
    (P : ι → ℕ → ENNReal)
    (Tail : ∀ᶠ n in l, ∀ t : ℕ, P n t ≤ ENNReal.ofReal
      ((t : ℝ)*GeometricJumpMomentBound eta (r n)*
        Real.exp (-GeometricJumpDriftExponent eta Delta (r n)*L n))) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n in l, ∀ t : ℕ,
      (t : ℝ)≤(2 : ℝ)^(c*L n/r n) →
      P n t ≤ ENNReal.ofReal ((2 : ℝ)^(-c*L n/r n)) := by
  let k := GeometricJumpDriftExponent eta Delta 1
  let c := k/(4*Real.log 2)
  have PositiveK : 0<k := GeometricJumpDriftExponentPositive eta Delta 1 PositiveEta PositiveDelta (by norm_num)
  have PositiveLog : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have PositiveC : 0<c := div_pos PositiveK (mul_pos (by norm_num) PositiveLog)
  refine ⟨c,PositiveC,?_⟩
  have Bound := GeometricJumpTailEventuallyExponential l L r Growth OneLeR SmallR
    eta Delta PositiveEta PositiveDelta P Tail
  filter_upwards [Bound, OneLeR, Growth.eventually_ge_atTop 0]
    with n LocalBound LowerR NonnegativeL
  intro t Horizon
  have PositiveR : 0<r n := lt_of_lt_of_le zero_lt_one LowerR
  have PositivePower : (2 : ℝ)^(c*L n/r n)=Real.exp (k*L n/(4*r n)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp [c]
    field_simp [PositiveLog.ne']
  have NegativePower : (2 : ℝ)^(-c*L n/r n)=Real.exp (-k*L n/(4*r n)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp [c]
    field_simp [PositiveLog.ne']
  rw [NegativePower]
  apply LocalBound t
  rw [PositivePower] at Horizon
  apply Horizon.trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_left (mul_nonneg PositiveK.le NonnegativeL)
    (mul_pos (by norm_num) PositiveR) (by linarith)

end
end ECTheoryLib.Tools.Drift
