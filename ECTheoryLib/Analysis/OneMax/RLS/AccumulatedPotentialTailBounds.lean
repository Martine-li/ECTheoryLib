import ECTheoryLib.Probability.Distributions.BinomialTail
import ECTheoryLib.Analysis.OneMax.RLS.AccumulatedPotentialBinomial

/-!
# Explicit tails for last-bit RLS accumulated potential

The actual dependent trajectory is compared with its proved binomial reference.
The sum counts residual potential after updates 1 through t; it is not a claim
that those trajectory coordinates are independent.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- A closed-tail estimate from one initial zero bit, including k = 0 and k > t. -/
theorem LastBitAccumulatedPotentialChooseTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t k : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState)).real
      {Path | (k : ℝ) ≤ ∑ i ∈ Finset.range t, Potential (Path (i + 1))} ≤
        (t.choose k : ℝ) * (1 - 1 / (n : ℝ)) ^ k := by
  have MeasurableSum : Measurable (fun Path : ℕ → Bits n =>
      ∑ i ∈ Finset.range t, Potential (Path (i + 1))) :=
    Finset.measurable_sum _ (fun i _ => (measurable_of_finite Potential).comp
      (measurable_pi_apply (i + 1)))
  have ProbabilitySum : IsProbabilityMeasure
      ((PathMeasure (Step PositiveLength) (PMF.pure InitialState)).map
        (fun Path => ∑ i ∈ Finset.range t, Potential (Path (i + 1)))) :=
    Measure.isProbabilityMeasure_map MeasurableSum.aemeasurable
  have Tail := (StochasticDominatedIffClosedTail _ _).mp
    (LastBitAccumulatedPotentialBinomialBound PositiveLength InitialState OneZero t) (k : ℝ)
  have RealTail := ENNReal.toReal_mono (measure_ne_top _ _) Tail
  change ((PathMeasure (Step PositiveLength) (PMF.pure InitialState)).map
      (fun Path => ∑ i ∈ Finset.range t, Potential (Path (i + 1)))).real (Set.Ici (k : ℝ)) ≤
    ((binomial t (LastBitRemainingProbability n PositiveLength)).map (Nat.cast : ℕ → ℝ)).real
      (Set.Ici (k : ℝ)) at RealTail
  rw [map_measureReal_apply MeasurableSum measurableSet_Ici] at RealTail
  exact RealTail.trans (BinomialRealChooseUpperTail t k (LastBitRemainingProbability n PositiveLength))

end
end ECTheoryLib.Analysis.RLSOnOneMax

