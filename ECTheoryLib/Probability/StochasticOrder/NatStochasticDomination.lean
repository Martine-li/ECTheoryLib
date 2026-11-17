import ECTheoryLib.Probability.StochasticOrder.StochasticExpectation

/-!
# Natural-valued stochastic order and real expectations

Natural inclusion in the reals preserves and reflects the distribution order.
Negative real thresholds have empty lower tails; nonnegative thresholds use
Mathlib's natural floor. No finite-support premise is imposed.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- Inclusion into the reals preserves natural-valued stochastic domination. -/
theorem StochasticDominatedNatCast (μ ν : Measure ℕ)
    (Dominated : StochasticDominated μ ν) :
    StochasticDominated (μ.map (Nat.cast : ℕ → ℝ)) (ν.map (Nat.cast : ℕ → ℝ)) := by
  intro a
  rw [Measure.map_apply (measurable_of_countable _) measurableSet_Iic,
    Measure.map_apply (measurable_of_countable _) measurableSet_Iic]
  by_cases Nonnegative : 0 ≤ a
  · have Preimage : (Nat.cast : ℕ → ℝ) ⁻¹' Iic a = Iic ⌊a⌋₊ := by
      ext j
      exact (Nat.le_floor_iff Nonnegative).symm
    rw [Preimage]
    exact Dominated ⌊a⌋₊
  · have Preimage : (Nat.cast : ℕ → ℝ) ⁻¹' Iic a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro j Member
      exact Nonnegative (le_trans (Nat.cast_nonneg j) Member)
    rw [Preimage, measure_empty, measure_empty]

/-- Casting does not lose information about the law order. -/
theorem StochasticDominatedNatCastIff (μ ν : Measure ℕ) :
    StochasticDominated (μ.map (Nat.cast : ℕ → ℝ)) (ν.map (Nat.cast : ℕ → ℝ)) ↔
      StochasticDominated μ ν := by
  constructor
  · intro Dominated j
    have Bound := Dominated (j : ℝ)
    rw [Measure.map_apply (measurable_of_countable _) measurableSet_Iic,
      Measure.map_apply (measurable_of_countable _) measurableSet_Iic] at Bound
    have Preimage : (Nat.cast : ℕ → ℝ) ⁻¹' Iic (j : ℝ) = Iic j := by
      ext k
      change (k : ℝ) ≤ (j : ℝ) ↔ k ≤ j
      exact Nat.cast_le
    rw [Preimage] at Bound
    exact Bound
  · exact StochasticDominatedNatCast μ ν

/-- A finite-mean comparison, with integrability made explicit. -/
theorem StochasticDominatedNatIntegralLE (μ ν : Measure ℕ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν)
    (Integrableμ : Integrable (Nat.cast : ℕ → ℝ) μ)
    (Integrableν : Integrable (Nat.cast : ℕ → ℝ) ν) :
    (∫ j, (j : ℝ) ∂μ) ≤ ∫ j, (j : ℝ) ∂ν := by
  exact StochasticDominatedExpectationLE μ ν _ _ Integrableμ Integrableν
    (StochasticDominatedNatCast μ ν Dominated)

end
end ECTheoryLib.Probability
