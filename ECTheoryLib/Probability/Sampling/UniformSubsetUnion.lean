import ECTheoryLib.Probability.Sampling.RandomSubsetUnion
import ECTheoryLib.Probability.Sampling.UniformSubset

/-!
# Independent fixed-size subset unions

Doerr Lemma1.10.26: arbitrary finite numbers of independent uniform draws,
with different fixed sample sizes. External random variables supply their
actual marginal laws and Mathlib independence. Zero-size samples and empty
families extend the printed domain. Exact coverage means and finite-size
upper/lower concentration are consequences of the proved joint law.
-/

namespace ECTheoryLib.Probability.UniformSubsetUnion
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Independent uniform subsets may have different fixed cardinalities.
Zero-cardinality samples and empty families are also permitted. -/
def Law {N k : ℕ} (Sizes : Fin k → ℕ) (Admissible : ∀ j, Sizes j≤N) : PMF (Finset (Fin N)) :=
  RandomSubset.FamilyLaw (fun j => UniformSubset.Law N (Sizes j) (Admissible j))

theorem OneNegativeCorrelation {N k : ℕ} (Sizes : Fin k → ℕ) (Admissible : ∀ j, Sizes j≤N) :
    OneNegativelyCorrelated (Law Sizes Admissible).toMeasure (fun i : Fin N => {U | i∈U}) :=
  RandomSubset.FamilyOneNegativeCorrelation _ (fun j => UniformSubset.OneNegativeCorrelation (Admissible j))

theorem ZeroNegativeCorrelation {N k : ℕ} (Sizes : Fin k → ℕ) (Admissible : ∀ j, Sizes j≤N) :
    ZeroNegativelyCorrelated (Law Sizes Admissible).toMeasure (fun i : Fin N => {U | i∈U}) :=
  RandomSubset.FamilyZeroNegativeCorrelation _ (fun j => UniformSubset.ZeroNegativeCorrelation (Admissible j))

/-- Doerr Lemma1.10.26 for arbitrary external independent random subsets.
The event is literally that a coordinate appears in at least one draw. -/
theorem IndependentUniformSubsetsNegativelyCorrelated {Ω : Type*} [MeasurableSpace Ω]
    (M : Measure Ω) [IsProbabilityMeasure M] {N k : ℕ}
    (Sizes : Fin k → ℕ) (Admissible : ∀ j, Sizes j≤N)
    (X : Fin k → Ω → Finset (Fin N)) (MeasurableX : ∀ j, Measurable (X j))
    (MarginalLaws : ∀ j, HasLaw (X j) (UniformSubset.Law N (Sizes j) (Admissible j)).toMeasure M)
    (Independent : iIndepFun X M) :
    OneNegativelyCorrelated M (fun i : Fin N => {ω | ∃ j, i∈X j ω}) ∧
      ZeroNegativelyCorrelated M (fun i : Fin N => {ω | ∃ j, i∈X j ω}) := by
  have UnionLaw := RandomSubset.FamilyHasLaw M X _ MeasurableX MarginalLaws Independent
  have One := RandomSubset.OneNegativeCorrelationOfHasLaw M _ _ UnionLaw (OneNegativeCorrelation Sizes Admissible)
  have Zero := RandomSubset.ZeroNegativeCorrelationOfHasLaw M _ _ UnionLaw (ZeroNegativeCorrelation Sizes Admissible)
  simpa only [RandomSubset.FamilyUnionMembership] using And.intro One Zero

end
end ECTheoryLib.Probability.UniformSubsetUnion

namespace ECTheoryLib.Probability.UniformSubsetUnion
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem Marginal {N k : ℕ} (Sizes : Fin k → ℕ) (Admissible : ∀ j, Sizes j≤N) (i : Fin N) :
    (Law Sizes Admissible).toMeasure.real {U | i∈U}=1-∏ j, (1-(Sizes j : ℝ)/(N : ℝ)) := by
  rw [Law,RandomSubset.FamilyMarginal]
  simp_rw [UniformSubset.Marginal]

theorem ExpectedCard {N k : ℕ} (Sizes : Fin k → ℕ) (Admissible : ∀ j, Sizes j≤N) :
    (∫ U, (U.card : ℝ) ∂(Law Sizes Admissible).toMeasure)=
      (N : ℝ)*(1-∏ j, (1-(Sizes j : ℝ)/(N : ℝ))) := by
  simp_rw [RandomSubset.CardAsIndicatorSum]
  rw [EventCountExpectation _ _ (fun _ => (Set.to_countable _).measurableSet)]
  simp_rw [Marginal]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem CardFiniteUpperTail {N k : ℕ} (Sizes : Fin k → ℕ) (Admissible : ∀ j, Sizes j≤N)
    (d : ℝ) (Nonnegative : 0≤d) :
    (Law Sizes Admissible).toMeasure.real
      {U | (1+d)*((N : ℝ)*(1-∏ j, (1-(Sizes j : ℝ)/(N : ℝ))))≤(U.card : ℝ)}≤
        FiniteChernoffUpperBound N ((N : ℝ)*(1-∏ j, (1-(Sizes j : ℝ)/(N : ℝ)))) d := by
  have Bound := OneNegativeCorrelationFiniteChernoffUpper (Law Sizes Admissible).toMeasure
    (fun i : Fin N => {U : Finset (Fin N) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (OneNegativeCorrelation Sizes Admissible) d Nonnegative
  simp_rw [Marginal,← RandomSubset.CardAsIndicatorSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

theorem CardFiniteLowerTail {N k : ℕ} (Sizes : Fin k → ℕ) (Admissible : ∀ j, Sizes j≤N)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Law Sizes Admissible).toMeasure.real
      {U | (U.card : ℝ)≤(1-d)*((N : ℝ)*(1-∏ j, (1-(Sizes j : ℝ)/(N : ℝ))))}≤
        FiniteChernoffLowerBound N ((N : ℝ)*(1-∏ j, (1-(Sizes j : ℝ)/(N : ℝ)))) d := by
  have Bound := ZeroNegativeCorrelationFiniteChernoffLower (Law Sizes Admissible).toMeasure
    (fun i : Fin N => {U : Finset (Fin N) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (ZeroNegativeCorrelation Sizes Admissible) d InUnit
  simp_rw [Marginal,← RandomSubset.CardAsIndicatorSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

end
end ECTheoryLib.Probability.UniformSubsetUnion
