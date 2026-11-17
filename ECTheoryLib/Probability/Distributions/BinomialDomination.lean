import ECTheoryLib.Probability.StochasticOrder.Quantile
import ECTheoryLib.Probability.StochasticOrder.StochasticDomination
import Mathlib.Probability.Distributions.Binomial

/-!
# Binomial stochastic comparison by uniform threshold coupling

Doerr, Lemma 1.8.9(a,b), p. 31, in *Theory of Evolutionary Computation*.
Mathlib supplies Bernoulli random sets, finite product measures and the law of
their cardinality. Shared open-unit uniforms couple both the success probability
and the number of trials. All probability endpoints and zero trials are retained.
The conditional-binomial and geometric parts of 1.8.9 are separate tasks.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- A threshold test is measurable even at probabilities zero and one. -/
theorem UniformThresholdMeasurable (p : I) :
    Measurable (fun u : OpenUnitInterval => (u : ℝ) ≤ (p : ℝ)) := by
  apply measurable_to_prop
  simpa only [Set.preimage_singleton_true] using
    (measurableSet_le measurable_subtype_coe measurable_const :
      MeasurableSet {u : OpenUnitInterval | (u : ℝ) ≤ (p : ℝ)})

/-- A threshold of an open-unit uniform has the existing Bernoulli proposition law. -/
theorem UniformThresholdLaw (p : I) :
    OpenUnitUniform.map (fun u : OpenUnitInterval => (u : ℝ) ≤ (p : ℝ)) =
      unitInterval.toNNReal p • Measure.dirac True +
        unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (UniformThresholdMeasurable p) (measurableSet_singleton b)]
  rw [Measure.add_apply, Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
  by_cases hb : b
  · have EqTrue : b = True := propext (iff_true_intro hb)
    subst b
    simp only [Set.preimage_singleton_true]
    rw [OpenUnitUniformLowerTail (p : ℝ) p.2.2]
    simp only [Measure.dirac_apply' _ (measurableSet_singleton _)]
    simp only [Set.indicator_of_mem (show True ∈ ({True} : Set Prop) by simp),
      Set.indicator_of_notMem (show False ∉ ({True} : Set Prop) by simp), Pi.one_apply,
      mul_one, mul_zero, add_zero]
    rw [← unitInterval.coe_toNNReal p, ENNReal.ofReal_coe_nnreal]
  · have EqFalse : b = False := propext (iff_false_intro hb)
    subst b
    have EventEq : (fun u : OpenUnitInterval => (u : ℝ) ≤ (p : ℝ)) ⁻¹' {False} =
        {u : OpenUnitInterval | (u : ℝ) ≤ (p : ℝ)}ᶜ := by
      ext u
      simp
    rw [EventEq, measure_compl (measurableSet_le measurable_subtype_coe measurable_const)
      (measure_ne_top _ _), measure_univ, OpenUnitUniformLowerTail (p : ℝ) p.2.2]
    simp only [Measure.dirac_apply' _ (measurableSet_singleton _)]
    simp only [Set.indicator_of_notMem (show True ∉ ({False} : Set Prop) by simp),
      Set.indicator_of_mem (show False ∈ ({False} : Set Prop) by simp), Pi.one_apply,
      mul_one, mul_zero, zero_add]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 p.2.1]
    rw [← unitInterval.coe_symm_eq p, ← unitInterval.coe_toNNReal (unitInterval.symm p),
      ENNReal.ofReal_coe_nnreal]

/-- Independent open-unit uniforms, using Mathlib finite product measures. -/
abbrev UniformTrials (ι : Type*) [Fintype ι] : Measure (ι → OpenUnitInterval) :=
  Measure.pi (fun _ : ι => OpenUnitUniform)

/-- Successes among the selected coordinates under a common probability threshold. -/
def ThresholdSet {ι : Type*} (S : Set ι) (p : I) (u : ι → OpenUnitInterval) : Set ι :=
  {i | i ∈ S ∧ (u i : ℝ) ≤ (p : ℝ)}

/-- The full random success set is measurable. -/
theorem ThresholdSetMeasurable {ι : Type*} [Fintype ι] (S : Set ι) (p : I) :
    Measurable (ThresholdSet S p) := by
  apply measurable_setOfPred.comp
  apply measurable_pi_lambda
  intro i
  by_cases Member : i ∈ S
  · simpa only [Member, true_and, Function.comp_def] using
      (UniformThresholdMeasurable p).comp (measurable_pi_apply i)
  · simpa only [Member, false_and] using (measurable_const :
      Measurable (fun _ : ι → OpenUnitInterval => False))

/-- The threshold construction has exactly the Mathlib Bernoulli random-set law. -/
theorem ThresholdSetLaw {ι : Type*} [Fintype ι] (S : Set ι) (p : I) :
    (UniformTrials ι).map (ThresholdSet S p) = setBernoulli S p := by
  have CoordinateMeasurable : ∀ i : ι,
      Measurable (fun u : OpenUnitInterval => i ∈ S ∧ (u : ℝ) ≤ (p : ℝ)) := by
    intro i
    by_cases Member : i ∈ S
    · simpa only [Member, true_and] using UniformThresholdMeasurable p
    · simpa only [Member, false_and] using
        (measurable_const : Measurable (fun _ : OpenUnitInterval => False))
  have MeasurablePred : Measurable (fun u : ι → OpenUnitInterval =>
      fun i => i ∈ S ∧ (u i : ℝ) ≤ (p : ℝ)) :=
    measurable_pi_lambda _ (fun i => (CoordinateMeasurable i).comp (measurable_pi_apply i))
  rw [setBernoulli_eq_map, Measure.infinitePi_eq_pi]
  change Measure.map ((fun b : ι → Prop => {i | b i}) ∘
    (fun u : ι → OpenUnitInterval => fun i => i ∈ S ∧ (u i : ℝ) ≤ (p : ℝ))) _ = _
  rw [← Measure.map_map measurable_setOfPred
    MeasurablePred,
    Measure.pi_map_pi (fun i => (CoordinateMeasurable i).aemeasurable)]
  congr 2
  funext i
  by_cases Member : i ∈ S
  · simpa only [Member, true_and] using UniformThresholdLaw p
  · simp only [Member, false_and, Measure.map_const, measure_univ, one_smul,
      ← add_smul, unitInterval.toNNReal_add_toNNReal_symm]

/-- Counting the threshold successes gives the full binomial law. -/
theorem ThresholdCountLaw {ι : Type*} [Fintype ι] (S : Set ι) (p : I) :
    HasLaw (fun u => (ThresholdSet S p u).ncard) (binomial S.ncard p) (UniformTrials ι) := by
  have MeasurableCount := measurable_ncard.comp (ThresholdSetMeasurable S p)
  refine ⟨MeasurableCount.aemeasurable, ?_⟩
  change Measure.map (Set.ncard ∘ ThresholdSet S p) _ = _
  rw [← Measure.map_map measurable_ncard (ThresholdSetMeasurable S p), ThresholdSetLaw]
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [map_ncard_setBernoulli_real_singleton (Set.toFinite S), binomial_real_singleton]

/-- Adding coordinates and raising their common threshold increases the count pointwise. -/
theorem ThresholdCountStochasticDominated {ι : Type*} [Fintype ι]
    (S T : Set ι) (p q : I) (Subset : S ⊆ T) (Parameters : p ≤ q) :
    StochasticDominated (binomial S.ncard p) (binomial T.ncard q) := by
  apply StochasticDominatedOfCoupling (UniformTrials ι)
    (binomial S.ncard p) (binomial T.ncard q)
    (fun u => (ThresholdSet S p u).ncard) (fun u => (ThresholdSet T q u).ncard)
    (ThresholdCountLaw S p) (ThresholdCountLaw T q)
  apply Filter.Eventually.of_forall
  intro u
  apply Set.ncard_mono
  intro i Member
  exact ⟨Subset Member.1, le_trans Member.2 Parameters⟩

/-- Lemma 1.8.9(a,b), combined: binomial laws increase with both parameters. -/
theorem BinomialStochasticDominated (n m : ℕ) (p q : I)
    (Trials : n ≤ m) (Parameters : p ≤ q) :
    StochasticDominated (binomial n p) (binomial m q) := by
  classical
  let S : Finset (Fin m) := Finset.univ.map (Fin.castLEEmb Trials)
  have SmallCard : (S : Set (Fin m)).ncard = n := by
    rw [Set.ncard_coe_finset, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have LargeCard : (Set.univ : Set (Fin m)).ncard = m := by
    rw [Set.ncard_univ, Nat.card_fin]
  have Domination := ThresholdCountStochasticDominated (S : Set (Fin m)) Set.univ
    p q (Set.subset_univ _) Parameters
  rw [SmallCard, LargeCard] at Domination
  exact Domination

end
end ECTheoryLib.Probability
