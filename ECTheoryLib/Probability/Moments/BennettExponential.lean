import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

/-!
# One-sided exponential majorants from Mathlib Taylor remainder

The quadratic exponential majorant requires only an upper bound on the
variable. Its negative side is unrestricted. Mathlib supplies the integral
Taylor identity and monotonicity of interval integrals.
-/

namespace ECTheoryLib.Probability
open MeasureTheory Set
noncomputable section

/-- Reuse Mathlib's integral Taylor remainder for the real exponential.
This identity holds on the whole real line. -/
theorem ExponentialQuadraticIntegralRemainder (x : ℝ) :
    Real.exp x=1+x+x^2*(∫ s in (0 : ℝ)..1, (1-s)*Real.exp (s*x)) := by
  have Derivative (n : ℕ) : iteratedDeriv n Real.exp=Real.exp := by
    simpa only [one_mul,one_pow] using iteratedDeriv_exp_const_mul n 1
  have Taylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := Real.exp) (x := 0) (y := x) (n := 1)
    (fun _s _Inside => Real.contDiff_exp.contDiffAt)
  simp_rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,Derivative] at Taylor
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,pow_zero,pow_one,Nat.factorial_zero,Nat.factorial_one,
    Nat.cast_one,inv_one,one_smul,zero_add,Real.exp_zero,mul_one,smul_eq_mul] at Taylor
  have Integrand (s : ℝ) : (1-s)*(x^2*Real.exp (s*x))=x^2*((1-s)*Real.exp (s*x)) := by ring
  simp_rw [Integrand] at Taylor
  simpa only [intervalIntegral.integral_const_mul,one_mul] using Taylor

/-- Bennett's one-sided quadratic exponential majorant. The variable may
be arbitrarily negative; only z≤1 is required. -/
theorem BennettExponentialMajorant (t z : ℝ) (Nonnegative : 0≤t) (Upper : z≤1) :
    Real.exp (t*z)≤1+t*z+z^2*(Real.exp t-1-t) := by
  have IntegralBound : (∫ s in (0 : ℝ)..1, (1-s)*Real.exp (s*(t*z)))≤
      ∫ s in (0 : ℝ)..1, (1-s)*Real.exp (s*t) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ)≤1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro s Inside
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr Inside.2)
    apply Real.exp_le_exp.mpr
    have Bound := mul_le_mul_of_nonneg_left Upper (mul_nonneg Inside.1 Nonnegative)
    nlinarith
  have AtTZ := ExponentialQuadraticIntegralRemainder (t*z)
  have AtT := ExponentialQuadraticIntegralRemainder t
  have Scaled := mul_le_mul_of_nonneg_left IntegralBound (sq_nonneg (t*z))
  have Identity : (t*z)^2=z^2*t^2 := by ring
  rw [Identity] at Scaled AtTZ
  nlinarith [Scaled,AtT,AtTZ]

end
end ECTheoryLib.Probability
