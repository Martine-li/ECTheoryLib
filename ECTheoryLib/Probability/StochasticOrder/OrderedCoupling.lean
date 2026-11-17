import ECTheoryLib.Probability.StochasticOrder.Quantile
import ECTheoryLib.Probability.StochasticOrder.StochasticDomination

/-!
# Existence of ordered couplings

Doerr, Theorem 1.8.10 (p. 31), in *Theory of Evolutionary Computation*.
Quantiles construct an ordered coupling on a fixed common probability space.
The marginal laws are verified for arbitrary real probability measures; no
continuity, discreteness, boundedness or finite-expectation condition is needed.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Ordered real laws have pointwise ordered quantiles at every interior level. -/
theorem StochasticDominatedQuantileLE (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν) (u : OpenUnitInterval) :
    RealQuantile μ u ≤ RealQuantile ν u := by
  apply (QuantileLeIffCDF μ u (RealQuantile ν u)).mpr
  exact (QuantileCDFLowerBound ν u).trans
    ((StochasticDominatedIffCDF μ ν).mp Dominated (RealQuantile ν u))

/-- Theorem 1.8.10. A fixed open-unit uniform space suffices for every pair of
real probability laws. The constructed order is pointwise, not only almost sure. -/
theorem StochasticDominatedIffExistsOrderedCoupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticDominated μ ν ↔
      ∃ X Y : OpenUnitInterval → ℝ,
        HasLaw X μ OpenUnitUniform ∧ HasLaw Y ν OpenUnitUniform ∧ ∀ u, X u ≤ Y u := by
  constructor
  · intro Dominated
    exact ⟨RealQuantile μ, RealQuantile ν, QuantileHasLaw μ, QuantileHasLaw ν,
      StochasticDominatedQuantileLE μ ν Dominated⟩
  · rintro ⟨X, Y, FirstLaw, SecondLaw, Ordered⟩
    exact StochasticDominatedOfCoupling OpenUnitUniform μ ν X Y FirstLaw SecondLaw
      (ae_of_all _ Ordered)

/-- Couple variables on different source spaces, retaining Mathlib's
identical-distribution relation with each original variable. -/
theorem ExistsOrderedCouplingOfStochasticDominated {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (Y : Ω' → ℝ)
    (MeasurableX : AEMeasurable X P) (MeasurableY : AEMeasurable Y Q)
    (Dominated : StochasticDominated (P.map X) (Q.map Y)) :
    ∃ X' Y' : OpenUnitInterval → ℝ,
      IdentDistrib X X' P OpenUnitUniform ∧ IdentDistrib Y Y' Q OpenUnitUniform ∧
        ∀ u, X' u ≤ Y' u := by
  have FirstProbability : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map MeasurableX
  have SecondProbability : IsProbabilityMeasure (Q.map Y) :=
    Measure.isProbabilityMeasure_map MeasurableY
  have FirstLaw : HasLaw X (P.map X) P := ⟨MeasurableX, rfl⟩
  have SecondLaw : HasLaw Y (Q.map Y) Q := ⟨MeasurableY, rfl⟩
  obtain ⟨X', Y', FirstCoupledLaw, SecondCoupledLaw, Ordered⟩ :=
    (StochasticDominatedIffExistsOrderedCoupling _ _).mp Dominated
  exact ⟨X', Y', FirstLaw.identDistrib FirstCoupledLaw,
    SecondLaw.identDistrib SecondCoupledLaw, Ordered⟩

end
end ECTheoryLib.Probability
