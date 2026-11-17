import Mathlib.Probability.Distributions.Binomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Harmonic expectations under binomial laws

A reciprocal-moment identity and a pointwise harmonic-difference bound give
a uniform constant error for success probabilities at least one half.
Finite sums include the zero outcome; no conditioning on positive counts is used.
-/

namespace ECTheoryLib.Probability

open MeasureTheory ProbabilityTheory Finset
open scoped unitInterval

noncomputable section

/-- Binomial reciprocal-moment identity multiplied by `(n+1)p`, avoiding
division by a possibly zero success probability. -/
theorem BinomialReciprocalMoment (n : Nat) (p : I) :
    ((n + 1 : Nat) : ℝ) * (p : ℝ) *
      (∫ k, (1 / (k + 1 : ℝ)) ∂binomial n p) = 1 - (1 - (p : ℝ)) ^ (n + 1) := by
  rw [integral_binomial]
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one, ← Nat.range_succ_eq_Iic]
  rw [mul_sum]
  have Summands : ∀ k ∈ range (n + 1),
      ((n : ℝ) + 1) * (p : ℝ) *
        ((n.choose k : ℝ) * (p : ℝ)^k * (1 - (p : ℝ))^(n-k) * (1 / ((k : ℝ)+1))) =
      ((n+1).choose (k+1) : ℝ) * (p : ℝ)^(k+1) * (1-(p : ℝ))^((n+1)-(k+1)) := by
    intro k _hk
    have ChooseIdentity : ((n : ℝ)+1) * (n.choose k : ℝ) =
        ((n+1).choose (k+1) : ℝ) * ((k : ℝ)+1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    rw [Nat.add_sub_add_right, pow_succ]
    have PositiveDenominator : (k : ℝ)+1 ≠ 0 := by positivity
    field_simp
    calc
      _ = (((n : ℝ)+1) * (n.choose k : ℝ)) *
          ((p : ℝ) * (p : ℝ)^k * (1-(p : ℝ))^(n-k)) := by ring
      _ = _ := by rw [ChooseIdentity]; ring
  rw [sum_congr rfl Summands]
  have BinomialSum := add_pow (p : ℝ) (1-(p : ℝ)) (n+1)
  rw [add_sub_cancel, one_pow, sum_range_succ'] at BinomialSum
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at BinomialSum
  simp only [mul_assoc, mul_left_comm, mul_comm] at BinomialSum ⊢
  linarith

/-- Each harmonic increment above level `k` is at most `1/(k+1)`. -/
theorem HarmonicDeficitLe (n k : Nat) (BelowLength : k ≤ n) :
    (harmonic n : ℝ) - (harmonic k : ℝ) ≤ (n-k : ℝ) / (k+1 : ℝ) := by
  induction n, BelowLength using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [harmonic_succ]
    push_cast
    have DenominatorPositive : (0 : ℝ) < (k : ℝ)+1 := by positivity
    have InverseBound : ((n : ℝ)+1)⁻¹ ≤ ((k : ℝ)+1)⁻¹ := by
      apply inv_anti₀ DenominatorPositive
      exact_mod_cast Nat.add_le_add_right hn 1
    simp only [div_eq_mul_inv] at ih ⊢
    nlinarith

/-- For binomial success probability at least one half, the expected
harmonic number lies within one below `H_n`. -/
theorem BinomialHarmonicBounds (n : Nat) (p : I) (AtLeastHalf : (1/2 : ℝ) ≤ p) :
    (harmonic n : ℝ) - 1 ≤ (∫ k, (harmonic k : ℝ) ∂binomial n p) ∧
      (∫ k, (harmonic k : ℝ) ∂binomial n p) ≤ (harmonic n : ℝ) := by
  have Supported : ∀ᵐ k ∂binomial n p, k ≤ n := by
    apply ae_le_of_hasLaw_binomial
    exact ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have HarmonicMonotone : Monotone (fun k => (harmonic k : ℝ)) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [harmonic_succ]
    push_cast
    exact le_add_of_nonneg_right (by positivity)
  have Upper : (∫ k, (harmonic k : ℝ) ∂binomial n p) ≤ (harmonic n : ℝ) := by
    have Bound := integral_mono_ae (integrable_binomial (fun k => (harmonic k : ℝ)))
      (integrable_const (harmonic n : ℝ))
      (Supported.mono (fun k hk => HarmonicMonotone hk))
    simpa only [integral_const, probReal_univ, one_smul] using Bound
  have Deficit := integral_mono_ae
    (integrable_binomial (fun k => (harmonic n : ℝ) - (harmonic k : ℝ)))
    (integrable_binomial (fun k => ((n : ℝ)+1) * (1 / ((k : ℝ)+1)) - 1))
    (Supported.mono (fun k hk => by
      have Bound := HarmonicDeficitLe n k hk
      have Algebra : ((n : ℝ)-k) / ((k : ℝ)+1) =
          ((n : ℝ)+1) * (1 / ((k : ℝ)+1)) - 1 := by
        field_simp
        ring
      rwa [Algebra] at Bound))
  rw [integral_sub (integrable_const _) (integrable_binomial _),
    integral_sub (integrable_binomial _) (integrable_const _), integral_const_mul] at Deficit
  simp only [integral_const, probReal_univ, one_smul] at Deficit
  have Moment := BinomialReciprocalMoment n p
  have NonnegativeMoment : 0 ≤ ∫ k, (1 / ((k : ℝ)+1)) ∂binomial n p := by
    apply integral_nonneg
    intro k
    positivity
  have NonnegativePower : (0 : ℝ) ≤ (1-(p : ℝ))^(n+1) :=
    pow_nonneg (sub_nonneg.mpr p.2.2) _
  push_cast at Moment
  have ProductNonnegative : 0 ≤ ((n : ℝ)+1) *
      (∫ k, (1 / ((k : ℝ)+1)) ∂binomial n p) := mul_nonneg (by positivity) NonnegativeMoment
  have ScaledBound := mul_le_mul_of_nonneg_right AtLeastHalf ProductNonnegative
  constructor
  · nlinarith [ScaledBound]
  · exact Upper

/-- Explicit logarithmic error bound of one for positive length and
binomial success probability at least one half. -/
theorem BinomialHarmonicLogBound {n : Nat} (PositiveLength : 0 < n)
    (p : I) (AtLeastHalf : (1/2 : ℝ) ≤ p) :
    |(∫ k, (harmonic k : ℝ) ∂binomial n p) - Real.log n| ≤ 1 := by
  obtain ⟨Lower, Upper⟩ := BinomialHarmonicBounds n p AtLeastHalf
  have LogLower : Real.log n ≤ (harmonic n : ℝ) := by
    have Bound := log_add_one_le_harmonic n
    have MonotoneLog : Real.log (n : ℝ) ≤ Real.log ((n+1 : Nat) : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.le_succ n
    exact MonotoneLog.trans Bound
  have LogUpper := harmonic_le_one_add_log n
  apply abs_le.mpr
  constructor
  · linarith
  · linarith

end
end ECTheoryLib.Probability
