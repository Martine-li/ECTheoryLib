import ECTheoryLib.Probability.StochasticOrder.StochasticDomination
import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Stochastic domination and extended-natural expectations

The lower-integral comparison retains infinite times and infinite means.
It reuses the tail-sum identity and probability-law strict-tail comparison;
no termination or integrability premise is introduced.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped unitInterval
noncomputable section

/-- Stochastic domination orders extended-natural expectations, including infinity. -/
theorem StochasticDominatedExtendedNatLIntegralLE
    (μ ν : Measure (WithTop ℕ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν) :
    (∫⁻ t, ENat.toENNReal t ∂μ) ≤ ∫⁻ t, ENat.toENNReal t ∂ν := by
  calc
    (∫⁻ t, ENat.toENNReal t ∂μ) = ∑' t : ℕ, μ {x | (t : WithTop ℕ) < x} :=
      ExpectedWithTopNatEqTailSum μ id measurable_id
    _ ≤ ∑' t : ℕ, ν {x | (t : WithTop ℕ) < x} :=
      ENNReal.tsum_le_tsum fun t =>
        (StochasticDominatedIffStrictTail μ ν).mp Dominated (t : WithTop ℕ)
    _ = ∫⁻ t, ENat.toENNReal t ∂ν :=
      (ExpectedWithTopNatEqTailSum ν id measurable_id).symm

/-- Transfer the law comparison to a measurable time without assuming a finite mean. -/
theorem StochasticDominatedExtendedNatExpectationLE {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → WithTop ℕ)
    (TimeMeasurable : Measurable T) (ν : Measure (WithTop ℕ)) [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated (P.map T) ν) :
    (∫⁻ ω, ENat.toENNReal (T ω) ∂P) ≤ ∫⁻ t, ENat.toENNReal t ∂ν := by
  have : IsProbabilityMeasure (P.map T) :=
    Measure.isProbabilityMeasure_map TimeMeasurable.aemeasurable
  calc
    (∫⁻ ω, ENat.toENNReal (T ω) ∂P) = ∫⁻ t, ENat.toENNReal t ∂P.map T :=
      (lintegral_map (measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t))
        TimeMeasurable).symm
    _ ≤ ∫⁻ t, ENat.toENNReal t ∂ν :=
      StochasticDominatedExtendedNatLIntegralLE (P.map T) ν Dominated

end
end ECTheoryLib.Probability
