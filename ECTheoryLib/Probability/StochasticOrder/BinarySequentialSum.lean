import ECTheoryLib.Probability.StochasticOrder.BinaryDomination
import ECTheoryLib.Probability.StochasticOrder.SequentialSum

/-!
# Sequential binary success bounds

Doerr, Lemma 1.8.7(a,b), pp. 28-29. Conditional success probabilities are
compared on every possible binary full history. Only the finite reference
family is independent. Positive histories and conditional binary range
are proved from the input variables, then Lemma 1.8.8 is applied.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- A positive-probability full history of binary variables is itself binary. -/
theorem PositiveBinaryPrefix {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X : Fin n → Ω → ℝ)
    (MeasurableX : ∀ i, Measurable (X i))
    (BinaryX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (t : Fin n) (h : Fin t → ℝ)
    (Positive : P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}) ≠ 0) :
    ∀ i, h i = 0 ∨ h i = 1 := by
  let A := VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}
  have MeasurableA : MeasurableSet A := (measurableSet_singleton h).preimage
    (VariablePrefixMeasurable _ (FiniteSequenceExtensionMeasurable X MeasurableX) t)
  have ConditionalProbability : IsProbabilityMeasure (cond P A) := cond_isProbabilityMeasure Positive
  have ConditionalBinary : ∀ᵐ ω ∂cond P A,
      ∀ i : Fin t, FiniteSequenceExtension X i ω = 0 ∨ FiniteSequenceExtension X i ω = 1 := by
    apply ae_all_iff.mpr
    intro i
    have BeforeEnd : (i : ℕ) < n := lt_trans i.isLt t.isLt
    have Original : ∀ᵐ ω ∂cond P A, X ⟨i, BeforeEnd⟩ ω = 0 ∨ X ⟨i, BeforeEnd⟩ ω = 1 :=
      cond_absolutelyContinuous.ae_le (BinaryX ⟨i, BeforeEnd⟩)
    simpa only [FiniteSequenceExtension, dif_pos BeforeEnd] using Original
  obtain ⟨ω, InHistory, Values⟩ := ((ae_cond_mem MeasurableA).and ConditionalBinary).exists
  have HistoryEq : VariablePrefix (FiniteSequenceExtension X) t ω = h := InHistory
  intro i
  rw [← HistoryEq]
  exact Values i

/-- Doerr, Lemma 1.8.7(a), for finite binary inputs and every positive binary history. -/
theorem BinarySequentialSumUpper {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (X : Fin n → Ω → ℝ) (Y : Fin n → Ω' → ℝ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (BinaryX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (BinaryY : ∀ i, ∀ᵐ ω ∂Q, Y i ω = 0 ∨ Y i ω = 1)
    (IndependentY : iIndepFun Y Q)
    (Conditional : ∀ (t : Fin n) (h : Fin t → ℝ),
      (∀ i, h i = 0 ∨ h i = 1) →
      P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}) ≠ 0 →
      (cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h})) {ω | X t ω = 1} ≤
        Q {ω | Y t ω = 1}) :
    StochasticDominated (P.map (fun ω => ∑ i, X i ω)) (Q.map (fun ω => ∑ i, Y i ω)) := by
  apply StochasticDominatedFiniteSequentialSum P Q n X Y MeasurableX MeasurableY IndependentY
  · intro i
    refine ⟨{0, 1}, Set.to_countable _, ?_⟩
    exact BinaryX i
  · intro t h Positive
    have ConditionalProbability : IsProbabilityMeasure
        (cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h})) :=
      cond_isProbabilityMeasure Positive
    have ConditionalBinary : ∀ᵐ ω ∂cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}),
        X t ω = 0 ∨ X t ω = 1 := cond_absolutelyContinuous.ae_le (BinaryX t)
    apply (BinaryVariableStochasticDominatedIff _ Q (X t) (Y t)
      (MeasurableX t) (MeasurableY t) ConditionalBinary (BinaryY t)).mpr
    exact Conditional t h (PositiveBinaryPrefix P n X MeasurableX BinaryX t h Positive) Positive

/-- Doerr, Lemma 1.8.7(b), with the conditional success inequality reversed. -/
theorem BinarySequentialSumLower {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (X : Fin n → Ω → ℝ) (Y : Fin n → Ω' → ℝ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (BinaryX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (BinaryY : ∀ i, ∀ᵐ ω ∂Q, Y i ω = 0 ∨ Y i ω = 1)
    (IndependentY : iIndepFun Y Q)
    (Conditional : ∀ (t : Fin n) (h : Fin t → ℝ),
      (∀ i, h i = 0 ∨ h i = 1) →
      P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}) ≠ 0 →
      Q {ω | Y t ω = 1} ≤
        (cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h})) {ω | X t ω = 1}) :
    StochasticDominated (Q.map (fun ω => ∑ i, Y i ω)) (P.map (fun ω => ∑ i, X i ω)) := by
  apply StochasticDominatedFiniteSequentialSumLower P Q n X Y MeasurableX MeasurableY IndependentY
  · intro i
    refine ⟨{0, 1}, Set.to_countable _, ?_⟩
    exact BinaryX i
  · intro t h Positive
    have ConditionalProbability : IsProbabilityMeasure
        (cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h})) :=
      cond_isProbabilityMeasure Positive
    have ConditionalBinary : ∀ᵐ ω ∂cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}),
        X t ω = 0 ∨ X t ω = 1 := cond_absolutelyContinuous.ae_le (BinaryX t)
    apply (BinaryVariableStochasticDominatedIff Q _ (Y t) (X t)
      (MeasurableY t) (MeasurableX t) (BinaryY t) ConditionalBinary).mpr
    exact Conditional t h (PositiveBinaryPrefix P n X MeasurableX BinaryX t h Positive) Positive


end
end ECTheoryLib.Probability
