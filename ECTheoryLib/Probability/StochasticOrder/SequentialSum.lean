import ECTheoryLib.Probability.StochasticOrder.ConditionalStochasticDomination

/-!
# Sequential domination of sums

Doerr, Lemma 1.8.8(a,b), p. 29. The comparison is conditional on the full
ordered prefix, for every prefix with positive probability. Discrete variables
have almost-sure countable support; their sums need not have finite expectation.
Only the reference family is independent. Finite inputs are supported directly.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
noncomputable section

/-- The complete ordered history strictly before time t; at zero this is an empty vector. -/
def VariablePrefix {Ω : Type*} (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin t → ℝ :=
  fun i => X i ω

/-- Measurability of the full prefix follows from coordinate measurability. -/
theorem VariablePrefixMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (MeasurableX : ∀ i, Measurable (X i)) (t : ℕ) :
    Measurable (VariablePrefix X t) := by
  exact measurable_pi_lambda _ (fun i => MeasurableX i)

/-- The prefix cost equals the corresponding finite partial sum. -/
theorem VariablePrefixSum {Ω : Type*} (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (∑ i : Fin t, VariablePrefix X t ω i) = ∑ i ∈ Finset.range t, X i ω := by
  exact Fin.sum_univ_eq_sum_range (fun i => X i ω) t

/-- Only the first n+1 reference variables need to be independent. -/
theorem IndependentPrefixSum {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (Y : ℕ → Ω → ℝ) (MeasurableY : ∀ i, Measurable (Y i))
    (n : ℕ) (IndependentY : iIndepFun (fun i : Fin (n + 1) => Y i) Q) :
    IndepFun (fun ω => ∑ i ∈ Finset.range n, Y i ω) (Y n) Q := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.map Fin.castSuccEmb
  have LastNotMember : Fin.last n ∉ S := by
    intro Member
    obtain ⟨i, _, Equal⟩ := Finset.mem_map.mp Member
    have Impossible := Fin.castSucc_lt_last i
    change i.castSucc = Fin.last n at Equal
    rw [Equal] at Impossible
    exact (lt_irrefl _ Impossible)
  have IndependentFunctions := IndependentY.indepFun_finsetSum_of_notMem
    (fun i => MeasurableY i) LastNotMember
  have SumFunction : (∑ i ∈ S, Y i) = fun ω => ∑ i ∈ Finset.range n, Y i ω := by
    funext ω
    rw [Finset.sum_apply]
    change (∑ i ∈ Finset.univ.map Fin.castSuccEmb, Y i ω) = _
    rw [Finset.sum_map]
    exact Fin.sum_univ_eq_sum_range (fun i => Y i ω) n
  rw [SumFunction] at IndependentFunctions
  exact IndependentFunctions

/-- Sequential upper comparison for real variables with regular conditional laws.
No discreteness, finite moments or independence of X is needed. -/
theorem StochasticDominatedSequentialSumKernel {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ω' → ℝ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (n : ℕ) (IndependentY : iIndepFun (fun i : Fin n => Y i) Q)
    (Conditional : ∀ t < n, ∀ᵐ h ∂P.map (VariablePrefix X t),
      StochasticDominated (condDistrib (X t) (VariablePrefix X t) P h) (Q.map (Y t))) :
    StochasticDominated (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω))
      (Q.map (fun ω => ∑ i ∈ Finset.range n, Y i ω)) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Measure.map_const,
        measure_univ, one_smul]
      exact StochasticDominatedRefl _
  | succ n InductionHypothesis =>
      have Previous := InductionHypothesis
        (IndependentY.precomp (Fin.castSucc_injective n))
        (fun t ht => Conditional t (Nat.lt_succ_of_lt ht))
      have MeasurableSumX : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
        Finset.measurable_sum _ (fun i _ => MeasurableX i)
      have MeasurableSumY : Measurable (fun ω => ∑ i ∈ Finset.range n, Y i ω) :=
        Finset.measurable_sum _ (fun i _ => MeasurableY i)
      have ProbabilityX : IsProbabilityMeasure (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω)) :=
        Measure.isProbabilityMeasure_map MeasurableSumX.aemeasurable
      have ProbabilityY : IsProbabilityMeasure (Q.map (fun ω => ∑ i ∈ Finset.range n, Y i ω)) :=
        Measure.isProbabilityMeasure_map MeasurableSumY.aemeasurable
      have ProbabilityNext : IsProbabilityMeasure (Q.map (Y n)) :=
        Measure.isProbabilityMeasure_map (MeasurableY n).aemeasurable
      have MeasurableHistorySum : Measurable (fun h : Fin n → ℝ => ∑ i, h i) :=
        Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      have AddBound := StochasticDominatedConditionalAdd P (VariablePrefix X n) (X n)
        (VariablePrefixMeasurable X MeasurableX n) (MeasurableX n)
        (fun h => ∑ i, h i) MeasurableHistorySum (Q.map (Y n))
        (Conditional n (Nat.lt_succ_self n))
      simp only [Function.comp_def, VariablePrefixSum] at AddBound
      have ConvolutionBound := StochasticDominatedConv _ _ _ _ Previous
        (StochasticDominatedRefl (Q.map (Y n)))
      have Compared := StochasticDominatedTrans AddBound ConvolutionBound
      have IndependentSum := IndependentPrefixSum Q Y MeasurableY n IndependentY
      have SumLaw := IndependentSum.map_add_eq_map_conv_map MeasurableSumY (MeasurableY n)
      rw [← SumLaw] at Compared
      change StochasticDominated (P.map (fun ω => (∑ i ∈ Finset.range n, X i ω) + X n ω))
        (Q.map (fun ω => (∑ i ∈ Finset.range n, Y i ω) + Y n ω)) at Compared
      simpa only [Finset.sum_range_succ, Pi.add_apply] using Compared

/-- The reverse sequential comparison, with the conditional order reversed. -/
theorem StochasticDominatedSequentialSumKernelLower {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ω' → ℝ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (n : ℕ) (IndependentY : iIndepFun (fun i : Fin n => Y i) Q)
    (Conditional : ∀ t < n, ∀ᵐ h ∂P.map (VariablePrefix X t),
      StochasticDominated (Q.map (Y t)) (condDistrib (X t) (VariablePrefix X t) P h)) :
    StochasticDominated (Q.map (fun ω => ∑ i ∈ Finset.range n, Y i ω))
      (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω)) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Measure.map_const,
        measure_univ, one_smul]
      exact StochasticDominatedRefl _
  | succ n InductionHypothesis =>
      have Previous := InductionHypothesis
        (IndependentY.precomp (Fin.castSucc_injective n))
        (fun t ht => Conditional t (Nat.lt_succ_of_lt ht))
      have MeasurableSumX : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
        Finset.measurable_sum _ (fun i _ => MeasurableX i)
      have MeasurableSumY : Measurable (fun ω => ∑ i ∈ Finset.range n, Y i ω) :=
        Finset.measurable_sum _ (fun i _ => MeasurableY i)
      have ProbabilityX : IsProbabilityMeasure (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω)) :=
        Measure.isProbabilityMeasure_map MeasurableSumX.aemeasurable
      have ProbabilityY : IsProbabilityMeasure (Q.map (fun ω => ∑ i ∈ Finset.range n, Y i ω)) :=
        Measure.isProbabilityMeasure_map MeasurableSumY.aemeasurable
      have ProbabilityNext : IsProbabilityMeasure (Q.map (Y n)) :=
        Measure.isProbabilityMeasure_map (MeasurableY n).aemeasurable
      have MeasurableHistorySum : Measurable (fun h : Fin n → ℝ => ∑ i, h i) :=
        Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      have AddBound := StochasticDominatedConditionalAddLower P (VariablePrefix X n) (X n)
        (VariablePrefixMeasurable X MeasurableX n) (MeasurableX n)
        (fun h => ∑ i, h i) MeasurableHistorySum (Q.map (Y n))
        (Conditional n (Nat.lt_succ_self n))
      simp only [Function.comp_def, VariablePrefixSum] at AddBound
      have ConvolutionBound := StochasticDominatedConv _ _ _ _ Previous
        (StochasticDominatedRefl (Q.map (Y n)))
      have Compared := StochasticDominatedTrans ConvolutionBound AddBound
      have IndependentSum := IndependentPrefixSum Q Y MeasurableY n IndependentY
      have SumLaw := IndependentSum.map_add_eq_map_conv_map MeasurableSumY (MeasurableY n)
      rw [← SumLaw] at Compared
      change StochasticDominated (Q.map (fun ω => (∑ i ∈ Finset.range n, Y i ω) + Y n ω))
        (P.map (fun ω => (∑ i ∈ Finset.range n, X i ω) + X n ω)) at Compared
      simpa only [Finset.sum_range_succ, Pi.add_apply] using Compared

/-- On a countably supported law, checking every positive atom suffices almost everywhere. -/
theorem AEOfPositiveAtomsOnCountableSupport {H : Type*} [MeasurableSpace H]
    (μ : Measure H) (S : Set H) (CountableS : S.Countable)
    (Supported : ∀ᵐ h ∂μ, h ∈ S) {p : H → Prop}
    (OnAtoms : ∀ h, μ {h} ≠ 0 → p h) : ∀ᵐ h ∂μ, p h := by
  have BadSetNull : μ {h | h ∈ S ∧ ¬p h} = 0 := by
    apply (measure_null_iff_singleton (CountableS.mono (fun h hh => hh.1))).mpr
    intro h Bad
    by_contra Positive
    exact Bad.2 (OnAtoms h Positive)
  have GoodOnS : ∀ᵐ h ∂μ, ¬(h ∈ S ∧ ¬p h) := by
    rw [ae_iff]
    simpa only [not_not] using BadSetNull
  filter_upwards [Supported, GoodOnS] with h InS Good
  by_contra NotGood
  exact Good ⟨InS, NotGood⟩

/-- A finite prefix of discrete variables has countable support almost surely. -/
theorem VariablePrefixCountableSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (MeasurableX : ∀ i, Measurable (X i))
    (t : ℕ) (Discrete : ∀ i < t, ∃ S : Set ℝ, S.Countable ∧ ∀ᵐ ω ∂P, X i ω ∈ S) :
    ∃ S : Set (Fin t → ℝ), S.Countable ∧ ∀ᵐ h ∂P.map (VariablePrefix X t), h ∈ S := by
  classical
  choose S CountableS Supported using (fun i : Fin t => Discrete i i.isLt)
  let Histories : Set (Fin t → ℝ) := {h | ∀ i, h i ∈ S i}
  have CountableHistories : Histories.Countable := Set.countable_pi CountableS
  refine ⟨Histories, CountableHistories, ?_⟩
  apply (ae_map_iff (VariablePrefixMeasurable X MeasurableX t).aemeasurable
    CountableHistories.measurableSet).mpr
  exact ae_all_iff.mpr Supported

/-- Doerr, Lemma 1.8.8(a): conditional comparison on every positive full history.
Discrete means almost-sure countable support; reference variables may even be continuous. -/
theorem StochasticDominatedSequentialSum {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ω' → ℝ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (n : ℕ) (IndependentY : iIndepFun (fun i : Fin n => Y i) Q)
    (Discrete : ∀ i < n, ∃ S : Set ℝ, S.Countable ∧ ∀ᵐ ω ∂P, X i ω ∈ S)
    (Conditional : ∀ t < n, ∀ h : Fin t → ℝ,
      P (VariablePrefix X t ⁻¹' {h}) ≠ 0 →
      StochasticDominated ((cond P (VariablePrefix X t ⁻¹' {h})).map (X t)) (Q.map (Y t))) :
    StochasticDominated (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω))
      (Q.map (fun ω => ∑ i ∈ Finset.range n, Y i ω)) := by
  apply StochasticDominatedSequentialSumKernel P Q X Y MeasurableX MeasurableY n IndependentY
  intro t BeforeEnd
  obtain ⟨S, CountableS, Supported⟩ := VariablePrefixCountableSupport P X MeasurableX t
    (fun i hi => Discrete i (Nat.lt_trans hi BeforeEnd))
  apply AEOfPositiveAtomsOnCountableSupport _ S CountableS Supported
  intro h PositiveAtom
  rw [ConditionalDistributionAtAtom P (VariablePrefix X t) (X t)
    (VariablePrefixMeasurable X MeasurableX t) (MeasurableX t) h PositiveAtom]
  apply Conditional t BeforeEnd h
  rw [Measure.map_apply (VariablePrefixMeasurable X MeasurableX t)
    (measurableSet_singleton h)] at PositiveAtom
  exact PositiveAtom

/-- Doerr, Lemma 1.8.8(b), retaining the same complete-history convention. -/
theorem StochasticDominatedSequentialSumLower {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ω' → ℝ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (n : ℕ) (IndependentY : iIndepFun (fun i : Fin n => Y i) Q)
    (Discrete : ∀ i < n, ∃ S : Set ℝ, S.Countable ∧ ∀ᵐ ω ∂P, X i ω ∈ S)
    (Conditional : ∀ t < n, ∀ h : Fin t → ℝ,
      P (VariablePrefix X t ⁻¹' {h}) ≠ 0 →
      StochasticDominated (Q.map (Y t)) ((cond P (VariablePrefix X t ⁻¹' {h})).map (X t))) :
    StochasticDominated (Q.map (fun ω => ∑ i ∈ Finset.range n, Y i ω))
      (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω)) := by
  apply StochasticDominatedSequentialSumKernelLower P Q X Y MeasurableX MeasurableY n IndependentY
  intro t BeforeEnd
  obtain ⟨S, CountableS, Supported⟩ := VariablePrefixCountableSupport P X MeasurableX t
    (fun i hi => Discrete i (Nat.lt_trans hi BeforeEnd))
  apply AEOfPositiveAtomsOnCountableSupport _ S CountableS Supported
  intro h PositiveAtom
  rw [ConditionalDistributionAtAtom P (VariablePrefix X t) (X t)
    (VariablePrefixMeasurable X MeasurableX t) (MeasurableX t) h PositiveAtom]
  apply Conditional t BeforeEnd h
  rw [Measure.map_apply (VariablePrefixMeasurable X MeasurableX t)
    (measurableSet_singleton h)] at PositiveAtom
  exact PositiveAtom

/-- Extend a finite input by zeros to use the process API. Outside indices are never sampled. -/
def FiniteSequenceExtension {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (i : ℕ) : Ω → ℝ := if hi : i < n then X ⟨i, hi⟩ else fun _ => 0

/-- The extension preserves every supplied variable exactly. -/
theorem FiniteSequenceExtensionAt {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (i : Fin n) : FiniteSequenceExtension X i = X i := by
  exact dif_pos i.isLt

/-- The extension adds only measurable constants. -/
theorem FiniteSequenceExtensionMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (X : Fin n → Ω → ℝ) (MeasurableX : ∀ i, Measurable (X i))
    (i : ℕ) : Measurable (FiniteSequenceExtension X i) := by
  unfold FiniteSequenceExtension
  split
  · exact MeasurableX _
  · exact measurable_const

/-- Extending a finite input does not change its sum. -/
theorem FiniteSequenceExtensionSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (ω : Ω) : (∑ i ∈ Finset.range n, FiniteSequenceExtension X i ω) = ∑ i, X i ω := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [FiniteSequenceExtensionAt]

/-- The book upper theorem for finite inputs: no infinite independent extension is assumed. -/
theorem StochasticDominatedFiniteSequentialSum {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (X : Fin n → Ω → ℝ) (Y : Fin n → Ω' → ℝ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (IndependentY : iIndepFun Y Q)
    (Discrete : ∀ i, ∃ S : Set ℝ, S.Countable ∧ ∀ᵐ ω ∂P, X i ω ∈ S)
    (Conditional : ∀ (t : Fin n) (h : Fin t → ℝ),
      P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}) ≠ 0 →
      StochasticDominated
        ((cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h})).map (X t))
        (Q.map (Y t))) :
    StochasticDominated (P.map (fun ω => ∑ i, X i ω)) (Q.map (fun ω => ∑ i, Y i ω)) := by
  have ExtendedIndependent : iIndepFun (fun i : Fin n => FiniteSequenceExtension Y i) Q := by
    simpa only [FiniteSequenceExtensionAt] using IndependentY
  have ExtendedDiscrete : ∀ i < n, ∃ S : Set ℝ, S.Countable ∧
      ∀ᵐ ω ∂P, FiniteSequenceExtension X i ω ∈ S := by
    intro i hi
    have Original := Discrete ⟨i, hi⟩
    simpa only [FiniteSequenceExtension, dif_pos hi] using Original
  have ExtendedConditional (t : ℕ) (ht : t < n) (h : Fin t → ℝ)
      (Positive : P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}) ≠ 0) :
      StochasticDominated
        ((cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h})).map
          (FiniteSequenceExtension X t)) (Q.map (FiniteSequenceExtension Y t)) := by
    simpa only [FiniteSequenceExtension, dif_pos ht] using Conditional ⟨t, ht⟩ h Positive
  have Compared := StochasticDominatedSequentialSum P Q
    (FiniteSequenceExtension X) (FiniteSequenceExtension Y)
    (FiniteSequenceExtensionMeasurable X MeasurableX)
    (FiniteSequenceExtensionMeasurable Y MeasurableY) n
    ExtendedIndependent ExtendedDiscrete ExtendedConditional
  simpa only [FiniteSequenceExtensionSum] using Compared

/-- The book lower theorem for finite inputs, including the empty family. -/
theorem StochasticDominatedFiniteSequentialSumLower {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (X : Fin n → Ω → ℝ) (Y : Fin n → Ω' → ℝ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (IndependentY : iIndepFun Y Q)
    (Discrete : ∀ i, ∃ S : Set ℝ, S.Countable ∧ ∀ᵐ ω ∂P, X i ω ∈ S)
    (Conditional : ∀ (t : Fin n) (h : Fin t → ℝ),
      P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}) ≠ 0 →
      StochasticDominated (Q.map (Y t))
        ((cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h})).map (X t))) :
    StochasticDominated (Q.map (fun ω => ∑ i, Y i ω)) (P.map (fun ω => ∑ i, X i ω)) := by
  have ExtendedIndependent : iIndepFun (fun i : Fin n => FiniteSequenceExtension Y i) Q := by
    simpa only [FiniteSequenceExtensionAt] using IndependentY
  have ExtendedDiscrete : ∀ i < n, ∃ S : Set ℝ, S.Countable ∧
      ∀ᵐ ω ∂P, FiniteSequenceExtension X i ω ∈ S := by
    intro i hi
    have Original := Discrete ⟨i, hi⟩
    simpa only [FiniteSequenceExtension, dif_pos hi] using Original
  have ExtendedConditional (t : ℕ) (ht : t < n) (h : Fin t → ℝ)
      (Positive : P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h}) ≠ 0) :
      StochasticDominated (Q.map (FiniteSequenceExtension Y t))
        ((cond P (VariablePrefix (FiniteSequenceExtension X) t ⁻¹' {h})).map
          (FiniteSequenceExtension X t)) := by
    simpa only [FiniteSequenceExtension, dif_pos ht] using Conditional ⟨t, ht⟩ h Positive
  have Compared := StochasticDominatedSequentialSumLower P Q
    (FiniteSequenceExtension X) (FiniteSequenceExtension Y)
    (FiniteSequenceExtensionMeasurable X MeasurableX)
    (FiniteSequenceExtensionMeasurable Y MeasurableY) n
    ExtendedIndependent ExtendedDiscrete ExtendedConditional
  simpa only [FiniteSequenceExtensionSum] using Compared


end
end ECTheoryLib.Probability
