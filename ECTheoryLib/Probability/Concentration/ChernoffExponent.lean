import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Scalar comparisons for Chernoff exponents

The exact logarithmic exponent dominates the rational quadratic expression
of Doerr (1.10.3). Mathlib supplies a logarithm lower bound and derivative
monotonicity on a convex interval; the local argument verifies the rational
derivative comparison. A second estimate gives the min expression (1.10.4).
These are scalar inequalities and do not assert probabilistic assumptions.
-/

namespace ECTheoryLib.Probability
open Set
noncomputable section

/-- The logarithmic Chernoff exponent dominates d^2/(2+2*d/3) on the nonnegative half-line. -/
theorem ChernoffExponentQuadraticLower (d : ℝ) (Nonnegative : 0 ≤ d) :
    d^2/(2+2*d/3) ≤ (1+d)*Real.log (1+d)-d := by
  let f : ℝ → ℝ := fun x => (1+x)*Real.log (1+x)-x-3*x^2/(2*(x+3))
  let g : ℝ → ℝ := fun x => Real.log (1+x)-3*x*(x+6)/(2*(x+3)^2)
  have Derivative (x : ℝ) (NonnegativeX : x ∈ Ici 0) : HasDerivAt f (g x) x := by
    have xNonnegative : 0 ≤ x := NonnegativeX
    have BasePositive : 0 < 1+x := by linarith
    have DenominatorNonzero : 2*(x+3) ≠ 0 := by positivity
    have BaseDerivative : HasDerivAt (fun y : ℝ => 1+y) 1 x :=
      (hasDerivAt_id x).const_add 1
    have LogDerivative := BaseDerivative.log BasePositive.ne'
    have TopDerivative : HasDerivAt (fun y : ℝ => 3*y^2) (3*(2*x)) x := by
      simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, id_eq, Pi.pow_apply] using
        ((hasDerivAt_id x).pow 2).const_mul 3
    have BottomDerivative : HasDerivAt (fun y : ℝ => 2*(y+3)) 2 x := by
      simpa only [mul_one, id_eq] using ((hasDerivAt_id x).add_const 3).const_mul 2
    have RawDerivative := ((BaseDerivative.mul LogDerivative).sub (hasDerivAt_id x)).sub
      (TopDerivative.div BottomDerivative DenominatorNonzero)
    have DerivativeIdentity :
        (1 * Real.log (1+x) + (1+x)*(1/(1+x)) - 1) -
          ((3*(2*x))*(2*(x+3)) - (3*x^2)*2)/(2*(x+3))^2 = g x := by
      dsimp only [g]
      field_simp
      ring
    rw [DerivativeIdentity] at RawDerivative
    exact RawDerivative
  have DerivativeNonnegative (x : ℝ) (NonnegativeX : x ∈ Ici 0) : 0 ≤ g x := by
    have xNonnegative : 0 ≤ x := NonnegativeX
    have LogLower := Real.le_log_one_add_of_nonneg xNonnegative
    have DenominatorPositive : 0 < 2*(x+3)^2 := by positivity
    have SecondPositive : 0 < x+2 := by linarith
    have RatioBound : 3*x*(x+6)/(2*(x+3)^2) ≤ 2*x/(x+2) := by
      apply (div_le_div_iff₀ DenominatorPositive SecondPositive).mpr
      have CubeNonnegative : 0 ≤ x^3 := pow_nonneg xNonnegative 3
      nlinarith
    dsimp only [g]
    linarith
  have MonotoneF : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro x hx
      exact (Derivative x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (Derivative x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact DerivativeNonnegative x (interior_subset hx)
  have Comparison := MonotoneF (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr Nonnegative) Nonnegative
  have RationalIdentity : d^2/(2+2*d/3) = 3*d^2/(2*(d+3)) := by
    field_simp
    ring
  rw [RationalIdentity]
  dsimp only [f] at Comparison
  norm_num only [add_zero, Real.log_one, zero_mul, sub_zero, zero_pow, mul_zero, zero_div] at Comparison
  linarith

/-- The quadratic-rational exponent dominates min(d^2,d)/3. -/
theorem ChernoffQuadraticMinLower (d : ℝ) (Nonnegative : 0 ≤ d) :
    min (d^2) d / 3 ≤ d^2/(2+2*d/3) := by
  have DenominatorPositive : 0 < 2+2*d/3 := by positivity
  by_cases SmallDeviation : d ≤ 1
  · have SquareLe : d^2 ≤ d := by nlinarith
    rw [min_eq_left SquareLe]
    exact div_le_div_of_nonneg_left (sq_nonneg d) DenominatorPositive (by linarith)
  · have LinearLe : d ≤ d^2 := by nlinarith
    rw [min_eq_right LinearLe]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) DenominatorPositive).mpr
    nlinarith

end
end ECTheoryLib.Probability
