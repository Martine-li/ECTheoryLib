import ECTheoryLib.Probability.Moments.ExponentialTailExpectation
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Finite examples showing why integer centers and nonnegative variables matter in tail-to-mean bounds. See docs/SOURCE_NOTES.md or docs/COVERAGE.md for source relations. -/





namespace BookExponentialTailSourceAudit

open MeasureTheory ProbabilityTheory
noncomputable section

namespace RealCenterUpper

def P : Measure Unit := Measure.dirac ()
instance : IsProbabilityMeasure P :=
  inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))

def X (_ : Unit) : ℤ := 1

theorem MeasurableX : Measurable X := measurable_const

theorem IntegrableX : Integrable (fun ω => (X ω : ℝ)) P := by
  simpa only [X, Int.cast_one] using (integrable_const (μ := P) (1 : ℝ))

theorem Expectation : (∫ ω, (X ω : ℝ) ∂P) = 1 := by
  simp [X]

/-- T = 1/2, alpha = 1, beta = 1/10 satisfy the printed parameter domain. -/
theorem Parameters : (0 : ℝ) ≤ 1 / 2 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 10 := by
  norm_num

/-- All natural lambda are covered, including zero; positive lambda give an
empty event, since the next admissible threshold is already at least 3/2. -/
theorem UpperTail (j : ℕ) :
    P.real {ω | (1 / 2 : ℝ) + (j : ℝ) ≤ (X ω : ℝ)} ≤
      (1 : ℝ) * Real.exp (-(j : ℝ) / (1 / 10)) := by
  by_cases Zero : j = 0
  · subst j
    norm_num [X, Measure.real]
  · have OneLe : (1 : ℝ) ≤ (j : ℝ) :=
      Nat.one_le_cast.mpr (Nat.pos_of_ne_zero Zero)
    have TooLarge : ¬ (1 / 2 : ℝ) + (j : ℝ) ≤ 1 := by linarith
    have Empty : {ω : Unit | (1 / 2 : ℝ) + (j : ℝ) ≤ (X ω : ℝ)} = ∅ := by
      ext ω
      simpa only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, X, Int.cast_one] using
        (iff_false_intro TooLarge)
    rw [Empty]
    simpa only [measureReal_empty, one_mul] using Real.exp_nonneg (-(j : ℝ) / (1 / 10))

theorem PrintedUpperConclusionFails :
    ¬ (∫ ω, (X ω : ℝ) ∂P) ≤ (1 / 2 : ℝ) + 1 * (1 / 10) := by
  rw [Expectation]
  norm_num

/-- The same actual law satisfies measurability, finite expectation and every
printed natural-threshold premise, but its expectation is strictly too large. -/
theorem Counterexample :
    Measurable X ∧ Integrable (fun ω => (X ω : ℝ)) P ∧
    (∀ j : ℕ, P.real {ω | (1 / 2 : ℝ) + (j : ℝ) ≤ (X ω : ℝ)} ≤
      (1 : ℝ) * Real.exp (-(j : ℝ) / (1 / 10))) ∧
    (1 / 2 : ℝ) + 1 * (1 / 10) < (∫ ω, (X ω : ℝ) ∂P) := by
  refine ⟨MeasurableX, IntegrableX, UpperTail, ?_⟩
  rw [Expectation]
  norm_num

end RealCenterUpper

namespace SignedLower

def Samples : PMF (Fin 4) := PMF.uniformOfFintype (Fin 4)
def P : Measure (Fin 4) := Samples.toMeasure
instance : IsProbabilityMeasure P :=
  inferInstanceAs (IsProbabilityMeasure Samples.toMeasure)

/-- The source's X is signed: the four equiprobable values are -4,1,1,1. -/
def X (i : Fin 4) : ℤ := if i = 0 then -4 else 1

theorem MeasurableX : Measurable X := measurable_of_finite _

theorem IntegrableX : Integrable (fun i => (X i : ℝ)) P := Integrable.of_finite

theorem Expectation : (∫ i, (X i : ℝ) ∂P) = -(1 / 4 : ℝ) := by
  unfold P
  rw [PMF.integral_eq_sum]
  norm_num [Samples, PMF.uniformOfFintype_apply, Fin.sum_univ_succ, X]

theorem Parameters : (0 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 := by
  norm_num

/-- For every allowed real epsilon the event is exactly the negative atom. -/
theorem LowerTailEvent (ε : ℝ) (Positive : 0 < ε) (AtMostOne : ε ≤ 1) :
    {i : Fin 4 | (X i : ℝ) ≤ (1 - ε) * 1} = {0} := by
  have NegativeAtom : (-4 : ℝ) ≤ 1 - ε := by linarith
  have PositiveAtoms : ¬ (1 : ℝ) ≤ 1 - ε := by linarith
  ext i
  by_cases Zero : i = 0
  · subst i
    simp [X, NegativeAtom]
  · simp [X, Zero, PositiveAtoms]

theorem LowerTailProbability (ε : ℝ) (Positive : 0 < ε) (AtMostOne : ε ≤ 1) :
    P.real {i | (X i : ℝ) ≤ (1 - ε) * 1} = (1 / 4 : ℝ) := by
  rw [LowerTailEvent ε Positive AtMostOne]
  norm_num [P, Samples, Measure.real, PMF.toMeasure_apply_singleton,
    PMF.uniformOfFintype_apply]

theorem QuarterLtExpNegOne : (1 / 4 : ℝ) < Real.exp (-1) := by
  rw [Real.exp_neg]
  have Upper : Real.exp 1 < (4 : ℝ) :=
    Real.exp_one_lt_three.trans (by norm_num)
  have Reciprocal := one_div_lt_one_div_of_lt (Real.exp_pos 1) Upper
  simpa only [one_div] using Reciprocal

/-- This is the original real-epsilon premise, not an integer-only restriction. -/
theorem LowerTail (ε : ℝ) (Positive : 0 < ε) (AtMostOne : ε ≤ 1) :
    P.real {i | (X i : ℝ) ≤ (1 - ε) * 1} ≤
      (1 : ℝ) * Real.exp (-ε / 1) := by
  rw [LowerTailProbability ε Positive AtMostOne]
  simp only [one_mul, div_one]
  exact QuarterLtExpNegOne.le.trans (Real.exp_le_exp.mpr (by linarith))

theorem PrintedLowerConclusionFails :
    ¬ ((1 : ℝ) - 1 * 1) * 1 ≤ (∫ i, (X i : ℝ) ∂P) := by
  rw [Expectation]
  norm_num

/-- The failure is finite and integrable on the very same probability space;
no undefined expectation or negative infinite value is used. -/
theorem Counterexample :
    Measurable X ∧ Integrable (fun i => (X i : ℝ)) P ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      P.real {i | (X i : ℝ) ≤ (1 - ε) * 1} ≤ (1 : ℝ) * Real.exp (-ε / 1)) ∧
    (∫ i, (X i : ℝ) ∂P) < ((1 : ℝ) - 1 * 1) * 1 := by
  refine ⟨MeasurableX, IntegrableX, LowerTail, ?_⟩
  rw [Expectation]
  norm_num

end SignedLower

end
end BookExponentialTailSourceAudit
