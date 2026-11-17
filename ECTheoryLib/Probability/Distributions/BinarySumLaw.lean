import ECTheoryLib.Probability.StochasticOrder.BinaryDomination
import ECTheoryLib.Probability.Distributions.BinomialDomination
import ECTheoryLib.Probability.StochasticOrder.StochasticSum

/-!
# The complete binomial law of independent binary sums

The uniform-threshold construction reuses the existing Bernoulli-set count
law. Independent-sum comparison and antisymmetry then transfer that law to
any independent binary family of a common success probability. Both endpoints
and the empty family are retained, without an assumed sum distribution.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- Numeric indicator of a uniform threshold success; probability endpoints are included. -/
def ThresholdValue (p : I) (u : OpenUnitInterval) : ℝ := if (u : ℝ) ≤ p then 1 else 0

/-- Threshold indicators are measurable on the existing open-unit uniform space. -/
theorem ThresholdValueMeasurable (p : I) : Measurable (ThresholdValue p) := by
  exact Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    measurable_const measurable_const

/-- A threshold indicator is binary pointwise. -/
theorem ThresholdValueBinary (p : I) (u : OpenUnitInterval) :
    ThresholdValue p u = 0 ∨ ThresholdValue p u = 1 := by
  unfold ThresholdValue
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The uniform-threshold success probability is the chosen parameter. -/
theorem ThresholdValueSuccessProbability (p : I) :
    OpenUnitUniform {u | ThresholdValue p u = 1} = ENNReal.ofReal (p : ℝ) := by
  have EventEq : {u | ThresholdValue p u = 1} = {u : OpenUnitInterval | (u : ℝ) ≤ p} := by
    ext u
    unfold ThresholdValue
    by_cases Below : (u : ℝ) ≤ p
    · simp only [Below, if_true, mem_ofPred_eq]
    · simp only [Below, if_false, zero_ne_one, mem_ofPred_eq]
  rw [EventEq]
  exact OpenUnitUniformLowerTail (p : ℝ) p.2.2

/-- The complete real binomial law of independent threshold indicators.
This reuses the already proved law of a Bernoulli random-set cardinality. -/
theorem ThresholdValueSumLaw (n : ℕ) (p : I) :
    HasLaw (fun u : Fin n → OpenUnitInterval => ∑ i, ThresholdValue p (u i))
      ((binomial n p).map (Nat.cast : ℕ → ℝ)) (UniformTrials (Fin n)) := by
  classical
  have SumEq (u : Fin n → OpenUnitInterval) :
      (∑ i, ThresholdValue p (u i)) = ((ThresholdSet univ p u).ncard : ℝ) := by
    have SetEq : ThresholdSet univ p u =
        ((Finset.univ.filter (fun i => (u i : ℝ) ≤ p) : Finset (Fin n)) : Set (Fin n)) := by
      ext i
      simp only [ThresholdSet, mem_ofPred_eq, mem_univ, true_and, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ]
    rw [SetEq, Set.ncard_coe_finset]
    exact Finset.sum_boole _ _
  have CountLaw := ThresholdCountLaw (univ : Set (Fin n)) p
  rw [Set.ncard_univ, Nat.card_fin] at CountLaw
  have CastLaw : HasLaw (fun u : Fin n → OpenUnitInterval =>
      ((ThresholdSet univ p u).ncard : ℝ)) ((binomial n p).map (Nat.cast : ℕ → ℝ))
      (UniformTrials (Fin n)) := by
    have Cast : HasLaw (Nat.cast : ℕ → ℝ) ((binomial n p).map (Nat.cast : ℕ → ℝ))
        (binomial n p) := ⟨(measurable_of_countable _).aemeasurable, rfl⟩
    exact Cast.fun_comp CountLaw
  have FunctionEq : (fun u : Fin n → OpenUnitInterval => ∑ i, ThresholdValue p (u i)) =
      (fun u => ((ThresholdSet univ p u).ncard : ℝ)) := funext SumEq
  rw [FunctionEq]
  exact CastLaw

/-- Independent binary variables with common success probability have the binomial law.
The existing independent-sum comparison transfers the threshold construction law. -/
theorem IndependentBinarySumLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (p : I)
    (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, Measurable (X i))
    (BinaryX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (IndependentX : iIndepFun X P)
    (Success : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal (p : ℝ)) :
    HasLaw (fun ω => ∑ i, X i ω) ((binomial n p).map (Nat.cast : ℕ → ℝ)) P := by
  let Q := UniformTrials (Fin n)
  let Y : Fin n → (Fin n → OpenUnitInterval) → ℝ := fun i u => ThresholdValue p (u i)
  have MeasurableY (i : Fin n) : Measurable (Y i) :=
    (ThresholdValueMeasurable p).comp (measurable_pi_apply i)
  have IndependentY : iIndepFun Y Q :=
    iIndepFun_pi (fun _ : Fin n => (ThresholdValueMeasurable p).aemeasurable)
  have BinaryY (i : Fin n) : ∀ᵐ u ∂Q, Y i u = 0 ∨ Y i u = 1 :=
    ae_of_all _ (fun u => ThresholdValueBinary p (u i))
  have SuccessY (i : Fin n) : Q {u | Y i u = 1} = ENNReal.ofReal (p : ℝ) := by
    have Marginal : Q.map (Y i) = OpenUnitUniform.map (ThresholdValue p) := by
      change Measure.map (ThresholdValue p ∘ Function.eval i) (UniformTrials (Fin n)) = _
      rw [← Measure.map_map (ThresholdValueMeasurable p) (measurable_pi_apply i),
        (measurePreserving_eval (fun _ : Fin n => OpenUnitUniform) i).map_eq]
    have EqualMass := congrArg (fun μ : Measure ℝ => μ {1}) Marginal
    rw [Measure.map_apply (MeasurableY i) (measurableSet_singleton 1),
      Measure.map_apply (ThresholdValueMeasurable p) (measurableSet_singleton 1)] at EqualMass
    exact EqualMass.trans (ThresholdValueSuccessProbability p)
  have Forward (i : Fin n) : StochasticDominated (P.map (X i)) (Q.map (Y i)) := by
    apply (BinaryVariableStochasticDominatedIff P Q (X i) (Y i)
      (MeasurableX i) (MeasurableY i) (BinaryX i) (BinaryY i)).mpr
    rw [Success i, SuccessY i]
  have Backward (i : Fin n) : StochasticDominated (Q.map (Y i)) (P.map (X i)) := by
    apply (BinaryVariableStochasticDominatedIff Q P (Y i) (X i)
      (MeasurableY i) (MeasurableX i) (BinaryY i) (BinaryX i)).mpr
    rw [SuccessY i, Success i]
  have SumForward := StochasticDominatedIndependentSum P Q X Y
    (fun i => (MeasurableX i).aemeasurable) (fun i => (MeasurableY i).aemeasurable)
    IndependentX IndependentY Forward Finset.univ
  have SumBackward := StochasticDominatedIndependentSum Q P Y X
    (fun i => (MeasurableY i).aemeasurable) (fun i => (MeasurableX i).aemeasurable)
    IndependentY IndependentX Backward Finset.univ
  have SumFunctionX : (∑ i, X i) = fun ω => ∑ i, X i ω := by
    funext ω
    exact Finset.sum_apply _ _ _
  have SumFunctionY : (∑ i, Y i) = fun u => ∑ i, Y i u := by
    funext u
    exact Finset.sum_apply _ _ _
  rw [SumFunctionX, SumFunctionY] at SumForward
  rw [SumFunctionX, SumFunctionY] at SumBackward
  have MeasurableSumX : Measurable (fun ω => ∑ i, X i ω) :=
    Finset.measurable_sum _ (fun i _ => MeasurableX i)
  have ProbabilitySumX : IsProbabilityMeasure (P.map (fun ω => ∑ i, X i ω)) :=
    Measure.isProbabilityMeasure_map MeasurableSumX.aemeasurable
  refine ⟨MeasurableSumX.aemeasurable, ?_⟩
  exact (StochasticDominatedAntisymm _ _ SumForward SumBackward).trans
    (ThresholdValueSumLaw n p).map_eq


end
end ECTheoryLib.Probability
