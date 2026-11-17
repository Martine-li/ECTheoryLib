import ECTheoryLib.Probability.StochasticOrder.StochasticExpectation
import Mathlib.Order.UpperLower.Basic

/-!
# Monotone transformations and the expectation characterization

Doerr, Lemma 1.8.2 (p. 26), in *Theory of Evolutionary Computation*.
The finite-expectation convention on p. 16 is explicit in the integral premises.
Monotonicity is non-strict; discontinuities and atoms are allowed. Real lower
sets are handled using Mathlib's existing order completeness and interval APIs.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Every real lower set has larger probability under the smaller law. -/
theorem StochasticDominatedMeasureLowerSetLE (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν) (S : Set ℝ) (Lower : IsLowerSet S) :
    ν S ≤ μ S := by
  by_cases Empty : S = ∅
  · rw [Empty, measure_empty, measure_empty]
  have Nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr Empty
  by_cases Bounded : BddAbove S
  · by_cases Endpoint : sSup S ∈ S
    · have ClosedCut : S = Iic (sSup S) := by
        ext x
        constructor
        · intro Member
          exact le_csSup Bounded Member
        · intro Below
          exact Lower Below Endpoint
      rw [ClosedCut]
      exact Dominated (sSup S)
    · have OpenCut : S = Iio (sSup S) := by
        ext x
        constructor
        · intro Member
          apply lt_of_le_of_ne (le_csSup Bounded Member)
          intro Equal
          apply Endpoint
          rw [← Equal]
          exact Member
        · intro Below
          obtain ⟨y, Member, Above⟩ := (lt_csSup_iff Bounded Nonempty).mp Below
          exact Lower Above.le Member
      have Complement (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
          ρ (Iio (sSup S)) = 1 - ρ (Ici (sSup S)) := by
        rw [← compl_Ici, prob_compl_eq_one_sub measurableSet_Ici]
      rw [OpenCut, Complement ν, Complement μ]
      exact tsub_le_tsub_left ((StochasticDominatedIffClosedTail μ ν).mp Dominated (sSup S)) 1
  · have WholeSpace : S = univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, Member, Above⟩ := not_bddAbove_iff.mp Bounded x
      exact Lower Above.le Member
    rw [WholeSpace, measure_univ, measure_univ]

/-- A nondecreasing real function preserves stochastic order. Its measurability
comes from Mathlib; continuity is not required. -/
theorem StochasticDominatedMapMonotone (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν) (f : ℝ → ℝ) (Increasing : Monotone f) :
    StochasticDominated (μ.map f) (ν.map f) := by
  intro a
  rw [Measure.map_apply Increasing.measurable measurableSet_Iic,
    Measure.map_apply Increasing.measurable measurableSet_Iic]
  exact StochasticDominatedMeasureLowerSetLE μ ν Dominated (f ⁻¹' Iic a)
    ((isLowerSet_Iic a).preimage Increasing)

/-- The forward implication of Lemma 1.8.2 for integrable monotone costs. -/
theorem StochasticDominatedMonotoneIntegralLE (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν) (f : ℝ → ℝ) (Increasing : Monotone f)
    (FirstIntegrable : Integrable f μ) (SecondIntegrable : Integrable f ν) :
    (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
  exact StochasticDominatedExpectationLE μ ν f f FirstIntegrable SecondIntegrable
    (StochasticDominatedMapMonotone μ ν Dominated f Increasing)

/-- Lemma 1.8.2 under the book's finite-expectation convention. The converse
uses upper-tail indicators, so the quantifier includes discontinuous functions. -/
theorem StochasticDominatedIffMonotoneIntegrals (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticDominated μ ν ↔
      ∀ f : ℝ → ℝ, Monotone f → Integrable f μ → Integrable f ν →
        (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
  constructor
  · intro Dominated f Increasing FirstIntegrable SecondIntegrable
    exact StochasticDominatedMonotoneIntegralLE μ ν Dominated f Increasing
      FirstIntegrable SecondIntegrable
  · intro ExpectationOrder
    apply (StochasticDominatedIffStrictTail μ ν).mpr
    intro a
    let f : ℝ → ℝ := (Ioi a).indicator (fun _ => 1)
    have Increasing : Monotone f := by
      intro x y Ordered
      by_cases FirstAbove : x ∈ Ioi a
      · have SecondAbove : y ∈ Ioi a := lt_of_lt_of_le FirstAbove Ordered
        change (Ioi a).indicator (fun _ : ℝ => (1 : ℝ)) x ≤
          (Ioi a).indicator (fun _ : ℝ => (1 : ℝ)) y
        rw [indicator_of_mem FirstAbove, indicator_of_mem SecondAbove]
      · change (Ioi a).indicator (fun _ : ℝ => (1 : ℝ)) x ≤
          (Ioi a).indicator (fun _ : ℝ => (1 : ℝ)) y
        rw [indicator_of_notMem FirstAbove]
        exact indicator_nonneg (fun _ _ => zero_le_one) _
    have FirstIntegrable : Integrable f μ :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
    have SecondIntegrable : Integrable f ν :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
    have Bound := ExpectationOrder f Increasing FirstIntegrable SecondIntegrable
    change (∫ x, (Ioi a).indicator (fun _ : ℝ => (1 : ℝ)) x ∂μ) ≤
      (∫ x, (Ioi a).indicator (fun _ : ℝ => (1 : ℝ)) x ∂ν) at Bound
    rw [integral_indicator_const 1 measurableSet_Ioi,
      integral_indicator_const 1 measurableSet_Ioi] at Bound
    simp only [smul_eq_mul, mul_one] at Bound
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top ν _)).mp Bound

/-- Apply a monotone cost to variables on different probability spaces.
Only the transformed variables need finite expectations. -/
theorem StochasticDominatedMonotoneExpectationLE {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (Y : Ω' → ℝ)
    (MeasurableX : AEMeasurable X P) (MeasurableY : AEMeasurable Y Q)
    (Dominated : StochasticDominated (P.map X) (Q.map Y))
    (f : ℝ → ℝ) (Increasing : Monotone f)
    (FirstIntegrable : Integrable (fun ω => f (X ω)) P)
    (SecondIntegrable : Integrable (fun ω => f (Y ω)) Q) :
    (∫ ω, f (X ω) ∂P) ≤ ∫ ω, f (Y ω) ∂Q := by
  have FirstProbability : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map MeasurableX
  have SecondProbability : IsProbabilityMeasure (Q.map Y) :=
    Measure.isProbabilityMeasure_map MeasurableY
  have Transformed := StochasticDominatedMapMonotone _ _ Dominated f Increasing
  rw [AEMeasurable.map_map_of_aemeasurable Increasing.measurable.aemeasurable MeasurableX,
    AEMeasurable.map_map_of_aemeasurable Increasing.measurable.aemeasurable MeasurableY]
    at Transformed
  exact StochasticDominatedExpectationLE P Q _ _ FirstIntegrable SecondIntegrable Transformed

end
end ECTheoryLib.Probability
