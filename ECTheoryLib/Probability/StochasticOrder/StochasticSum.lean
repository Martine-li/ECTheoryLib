import ECTheoryLib.Probability.StochasticOrder.StochasticDomination
import Mathlib.Probability.Independence.Basic

/-!
# Stochastic domination of independent sums

Doerr, Lemma 1.8.4 (p. 27), in *Theory of Evolutionary Computation*.
Mathlib supplies convolution, product measures and laws of independent sums.
Each family is internally independent; the two families need not be jointly
independent and may be defined on different probability spaces. No finite
expectation, discreteness or boundedness assumption is required.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Adding a common independent law preserves the order of the other summand. -/
theorem StochasticDominatedConvRight (ρ μ ν : Measure ℝ)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Dominated : StochasticDominated μ ν) :
    StochasticDominated (ρ ∗ μ) (ρ ∗ ν) := by
  have ConvLowerTail (ξ : Measure ℝ) [IsProbabilityMeasure ξ] (a : ℝ) :
      (ρ ∗ ξ) (Iic a) = ∫⁻ x, ξ (Iic (a - x)) ∂ρ := by
    have AddMeasurable : Measurable (fun p : ℝ × ℝ => p.1 + p.2) :=
      measurable_fst.add measurable_snd
    rw [Measure.conv, Measure.map_apply AddMeasurable measurableSet_Iic,
      Measure.prod_apply (measurableSet_Iic.preimage AddMeasurable)]
    apply lintegral_congr
    intro x
    congr 1
    ext y
    change x + y ≤ a ↔ y ≤ a - x
    constructor
    · intro Bound
      linarith
    · intro Bound
      linarith
  intro a
  rw [ConvLowerTail ν a, ConvLowerTail μ a]
  exact lintegral_mono (fun x => Dominated (a - x))

/-- Convolution is monotone in both real probability laws. -/
theorem StochasticDominatedConv (μ ν ρ σ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (First : StochasticDominated μ ν) (Second : StochasticDominated ρ σ) :
    StochasticDominated (μ ∗ ρ) (ν ∗ σ) := by
  have FirstSummand : StochasticDominated (μ ∗ ρ) (ν ∗ ρ) := by
    rw [Measure.conv_comm μ ρ, Measure.conv_comm ν ρ]
    exact StochasticDominatedConvRight ρ μ ν First
  exact StochasticDominatedTrans FirstSummand (StochasticDominatedConvRight ν ρ σ Second)

/-- Compare two sums, requiring independence only within each pair. -/
theorem StochasticDominatedIndependentAdd {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X₁ X₂ : Ω → ℝ) (Y₁ Y₂ : Ω' → ℝ)
    (MeasurableX₁ : AEMeasurable X₁ P) (MeasurableX₂ : AEMeasurable X₂ P)
    (MeasurableY₁ : AEMeasurable Y₁ Q) (MeasurableY₂ : AEMeasurable Y₂ Q)
    (IndependentX : IndepFun X₁ X₂ P) (IndependentY : IndepFun Y₁ Y₂ Q)
    (First : StochasticDominated (P.map X₁) (Q.map Y₁))
    (Second : StochasticDominated (P.map X₂) (Q.map Y₂)) :
    StochasticDominated (P.map (X₁ + X₂)) (Q.map (Y₁ + Y₂)) := by
  have ProbX₁ : IsProbabilityMeasure (P.map X₁) := Measure.isProbabilityMeasure_map MeasurableX₁
  have ProbX₂ : IsProbabilityMeasure (P.map X₂) := Measure.isProbabilityMeasure_map MeasurableX₂
  have ProbY₁ : IsProbabilityMeasure (Q.map Y₁) := Measure.isProbabilityMeasure_map MeasurableY₁
  have ProbY₂ : IsProbabilityMeasure (Q.map Y₂) := Measure.isProbabilityMeasure_map MeasurableY₂
  rw [IndependentX.map_add_eq_map_conv_map₀ MeasurableX₁ MeasurableX₂,
    IndependentY.map_add_eq_map_conv_map₀ MeasurableY₁ MeasurableY₂]
  exact StochasticDominatedConv _ _ _ _ First Second

/-- Lemma 1.8.4 for a finite subfamily. Taking the index type to be Fin n and
the finset to be univ gives the book statement, including the empty sum. -/
theorem StochasticDominatedIndependentSum {ι Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (MeasurableY : ∀ i, AEMeasurable (Y i) Q)
    (IndependentX : iIndepFun X P) (IndependentY : iIndepFun Y Q)
    (Dominated : ∀ i, StochasticDominated (P.map (X i)) (Q.map (Y i))) (S : Finset ι) :
    StochasticDominated (P.map (∑ i ∈ S, X i)) (Q.map (∑ i ∈ S, Y i)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      change StochasticDominated (P.map (fun _ => (0 : ℝ))) (Q.map (fun _ => (0 : ℝ)))
      rw [Measure.map_const, Measure.map_const, measure_univ, measure_univ, one_smul]
      exact StochasticDominatedRefl _
  | insert i S NotMember InductionHypothesis =>
      rw [Finset.sum_insert NotMember, Finset.sum_insert NotMember]
      exact StochasticDominatedIndependentAdd P Q _ _ _ _
        (MeasurableX i) (Finset.aemeasurable_sum S (fun j _ => MeasurableX j))
        (MeasurableY i) (Finset.aemeasurable_sum S (fun j _ => MeasurableY j))
        (IndependentX.indepFun_finsetSum_of_notMem₀ MeasurableX NotMember).symm
        (IndependentY.indepFun_finsetSum_of_notMem₀ MeasurableY NotMember).symm
        (Dominated i) InductionHypothesis

end
end ECTheoryLib.Probability

