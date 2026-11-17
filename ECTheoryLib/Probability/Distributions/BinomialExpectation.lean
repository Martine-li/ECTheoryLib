import Mathlib.Probability.Distributions.Binomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
# Binomial expectation from the existing distribution

Doerr, Lemma 1.6.5 (p. 18), in *Theory of Evolutionary Computation* (2020).
Mathlib 4.33.0 provides the binomial law, its integrability and its integral
expansion, but its named mean statement is still `proof_wanted`. This module
connects those proved interfaces with the existing binomial coefficient identity
and binomial theorem. All parameters are retained: `n = 0`, `p = 0` and `p = 1`.
-/

namespace ECTheoryLib.Probability

open MeasureTheory ProbabilityTheory Finset
open scoped unitInterval

noncomputable section

/-- The mean of Mathlib's binomial distribution is `p * n`. -/
theorem BinomialExpectation (n : ℕ) (p : I) :
    (∫ k : ℕ, (k : ℝ) ∂binomial n p) = (p : ℝ) * n := by
  cases n with
  | zero =>
    rw [binomial_zero, integral_dirac]
    simp only [Nat.cast_zero, mul_zero]
  | succ n =>
    rw [integral_binomial]
    simp only [smul_eq_mul, ← Nat.range_succ_eq_Iic]
    rw [sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, add_zero]
    have Terms : ∀ k ∈ range (n + 1),
        ((n + 1).choose (k + 1) : ℝ) * (p : ℝ) ^ (k + 1) *
            (1 - (p : ℝ)) ^ ((n + 1) - (k + 1)) * ((k + 1 : ℕ) : ℝ) =
          (((n + 1 : ℕ) : ℝ) * p) *
            ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) := by
      intro k _Membership
      have ChooseIdentity :
          (((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ)) =
            ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n k
      rw [Nat.add_sub_add_right, pow_succ]
      calc
        _ = (((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
            ((p : ℝ) ^ k * p * (1 - (p : ℝ)) ^ (n - k)) := by ring
        _ = _ := by
          rw [← ChooseIdentity]
          ring
    rw [sum_congr rfl Terms, ← mul_sum]
    have TotalMass :
        (∑ k ∈ range (n + 1), (n.choose k : ℝ) * (p : ℝ) ^ k *
          (1 - (p : ℝ)) ^ (n - k)) = 1 := by
      calc
        _ = ((p : ℝ) + (1 - (p : ℝ))) ^ n := by
          rw [add_pow]
          apply sum_congr rfl
          intro k _Membership
          ring
        _ = 1 := by rw [add_sub_cancel, one_pow]
    rw [TotalMass, mul_one, mul_comm]

/-- A binomial natural-valued random variable has a finite real expectation. -/
theorem BinomialNatIntegrableOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℕ) (n : ℕ) (p : I)
    (BinomialLaw : HasLaw X (binomial n p) μ) :
    Integrable (fun ω => (X ω : ℝ)) μ := by
  have FiniteMean := integrable_binomial (n := n) (p := p) (fun k : ℕ => (k : ℝ))
  rw [← BinomialLaw.map_eq] at FiniteMean
  exact FiniteMean.comp_aemeasurable BinomialLaw.aemeasurable

/-- Transfer the mean to a natural-valued random variable with a proved binomial law. -/
theorem BinomialNatExpectationOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℕ) (n : ℕ) (p : I)
    (BinomialLaw : HasLaw X (binomial n p) μ) :
    (∫ ω, (X ω : ℝ) ∂μ) = (p : ℝ) * n := by
  have Transfer := BinomialLaw.integral_comp (f := fun k : ℕ => (k : ℝ)) (by fun_prop)
  change (∫ ω, (X ω : ℝ) ∂μ) = ∫ k : ℕ, (k : ℝ) ∂binomial n p at Transfer
  rw [Transfer, BinomialExpectation]

/-- A real-valued binomial random variable has a finite expectation. -/
theorem BinomialRealIntegrableOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (n : ℕ) (p : I)
    (BinomialLaw : HasLaw X ((binomial n p).map (Nat.cast : ℕ → ℝ)) μ) :
    Integrable X μ := by
  have FiniteMean := integrable_map_cast_binomial (n := n) (p := p) (fun x : ℝ => x)
  rw [← BinomialLaw.map_eq] at FiniteMean
  exact FiniteMean.comp_aemeasurable BinomialLaw.aemeasurable

/-- Transfer the mean to a real-valued binomial random variable, matching
the type of the unproved upstream mean statement without depending on it. -/
theorem BinomialRealExpectationOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (n : ℕ) (p : I)
    (BinomialLaw : HasLaw X ((binomial n p).map (Nat.cast : ℕ → ℝ)) μ) :
    (∫ ω, X ω ∂μ) = (p : ℝ) * n := by
  rw [BinomialLaw.integral_eq, integral_map (by fun_prop) (by fun_prop)]
  exact BinomialExpectation n p

end
end ECTheoryLib.Probability
