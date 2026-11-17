import ECTheoryLib.Probability.StochasticOrder.SequentialSum
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-!
# Stochastic sums of extended-natural times

The real-valued sequential-sum interface cannot represent an infinite duration.
This extension retains infinity throughout conditional laws, convolution, and
finite sums. It reuses Mathlib disintegration, event conditioning, independence,
and countable-measure continuity, and the existing positive-atom reduction.

Only the reference family is independent. A stage may be zero (skipped) or
infinite; neither termination nor a finite mean is an input to the comparisons.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section


/-- A common extended-natural cost preserves lower-tail order, including infinite costs and thresholds. -/
theorem ExtendedNatShiftLowerTail (μ ν : Measure (WithTop ℕ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Ordered : StochasticDominated μ ν) (c a : WithTop ℕ) :
    ν {x | c+x ≤ a} ≤ μ {x | c+x ≤ a} := by
  cases a using WithTop.recTopCoe with
  | top =>
      have Everything : {x : WithTop ℕ | c+x ≤ ⊤} = univ := by ext x; simp
      rw [Everything, measure_univ, measure_univ]
  | coe a =>
      cases c using WithTop.recTopCoe with
      | top =>
          change ν {x : WithTop ℕ | ⊤+x ≤ (a : WithTop ℕ)} ≤
            μ {x : WithTop ℕ | ⊤+x ≤ (a : WithTop ℕ)}
          have Empty : {x : WithTop ℕ | ⊤+x ≤ (a : WithTop ℕ)} = ∅ := by ext x; simp
          rw [Empty, measure_empty, measure_empty]
      | coe c =>
          change ν {x : WithTop ℕ | (c : WithTop ℕ)+x ≤ (a : WithTop ℕ)} ≤
            μ {x : WithTop ℕ | (c : WithTop ℕ)+x ≤ (a : WithTop ℕ)}
          by_cases Before : c ≤ a
          · have Event : {x : WithTop ℕ | (c : WithTop ℕ)+x ≤ (a : WithTop ℕ)} =
                Iic ((a-c : ℕ) : WithTop ℕ) := by
              ext x
              cases x using WithTop.recTopCoe with
              | top => simp
              | coe x =>
                  change (c : WithTop ℕ)+(x : WithTop ℕ) ≤ (a : WithTop ℕ) ↔
                    (x : WithTop ℕ) ≤ ((a-c : ℕ) : WithTop ℕ)
                  norm_cast
                  omega
            rw [Event]
            exact Ordered ((a-c : ℕ) : WithTop ℕ)
          · have Empty : {x : WithTop ℕ | (c : WithTop ℕ)+x ≤ (a : WithTop ℕ)} = ∅ := by
              ext x
              cases x using WithTop.recTopCoe with
              | top => simp
              | coe x =>
                  change ((c : WithTop ℕ)+(x : WithTop ℕ) ≤ (a : WithTop ℕ)) ↔ False
                  norm_cast
                  constructor
                  · intro Bound
                    exact Before ((Nat.le_add_right c x).trans Bound)
                  · intro Impossible
                    exact Impossible.elim
            rw [Empty, measure_empty, measure_empty]

/-- Integrate the conditional lower-tail comparison while retaining the same past cost. -/
theorem ExtendedNatKernelAdd {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (κ η : Kernel H (WithTop ℕ))
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (g : H → WithTop ℕ) (MeasurableG : Measurable g)
    (Ordered : ∀ᵐ h ∂μ, StochasticDominated (κ h) (η h)) :
    StochasticDominated ((μ ⊗ₘ κ).map (fun p => g p.1+p.2))
      ((μ ⊗ₘ η).map (fun p => g p.1+p.2)) := by
  have AddMeasurable : Measurable (fun p : H × WithTop ℕ => g p.1+p.2) :=
    (measurable_of_countable (fun p : WithTop ℕ × WithTop ℕ => p.1+p.2)).comp
      ((MeasurableG.comp measurable_fst).prodMk measurable_snd)
  intro a
  rw [Measure.map_apply AddMeasurable measurableSet_Iic,
    Measure.map_apply AddMeasurable measurableSet_Iic,
    Measure.compProd_apply (measurableSet_Iic.preimage AddMeasurable),
    Measure.compProd_apply (measurableSet_Iic.preimage AddMeasurable)]
  apply lintegral_mono_ae
  filter_upwards [Ordered] with h Bound
  exact ExtendedNatShiftLowerTail (κ h) (η h) Bound (g h) a

/-- Conditional increments are compared on the actual joint law supplied by Mathlib disintegration. -/
theorem ExtendedNatConditionalAdd {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (Hst : Ω → H) (V : Ω → WithTop ℕ)
    (MeasurableHistory : Measurable Hst) (MeasurableV : Measurable V)
    (g : H → WithTop ℕ) (MeasurableG : Measurable g)
    (ν : Measure (WithTop ℕ)) [IsProbabilityMeasure ν]
    (Ordered : ∀ᵐ h ∂P.map Hst, StochasticDominated (condDistrib V Hst P h) ν) :
    StochasticDominated (P.map (fun ω => g (Hst ω)+V ω))
      (((P.map Hst).prod ν).map (fun p => g p.1+p.2)) := by
  have HistoryProbability : IsProbabilityMeasure (P.map Hst) :=
    Measure.isProbabilityMeasure_map MeasurableHistory.aemeasurable
  have Compared := ExtendedNatKernelAdd (P.map Hst) (condDistrib V Hst P)
    (Kernel.const H ν) g MeasurableG Ordered
  have AddMeasurable : Measurable (fun p : H × WithTop ℕ => g p.1+p.2) :=
    (measurable_of_countable (fun p : WithTop ℕ × WithTop ℕ => p.1+p.2)).comp
      ((MeasurableG.comp measurable_fst).prodMk measurable_snd)
  rw [Measure.compProd_const, compProd_map_condDistrib MeasurableV.aemeasurable,
    Measure.map_map AddMeasurable (MeasurableHistory.prodMk MeasurableV)] at Compared
  exact Compared

/-- A constant kernel is the independent convolution law; this reuses Mathlib product and map identities. -/
theorem ExtendedNatConstantKernelAdditionLaw {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (ν : Measure (WithTop ℕ)) [SFinite ν]
    (g : H → (WithTop ℕ)) (MeasurableG : Measurable g) :
    (μ ⊗ₘ Kernel.const H ν).map (fun p => g p.1 + p.2) = (μ.map g) ∗ ν := by
  rw [Measure.compProd_const, Measure.conv]
  have ProductLaw := Measure.map_prod_map μ ν MeasurableG measurable_id
  have MeasurableAdd : Measurable (fun p : (WithTop ℕ) × (WithTop ℕ) => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  rw [Measure.map_id] at ProductLaw
  rw [ProductLaw, Measure.map_map MeasurableAdd
    (MeasurableG.prodMap measurable_id)]
  rfl

/-- At a nonnull history, the regular conditional distribution agrees with event conditioning. -/
theorem ExtendedNatConditionalDistributionAtAtom {Ω H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSingletonClass H]
    (P : Measure Ω) [IsProbabilityMeasure P] (Hst : Ω → H) (V : Ω → (WithTop ℕ))
    (MeasurableHistory : Measurable Hst) (MeasurableV : Measurable V)
    (h : H) (Positive : (P.map Hst) {h} ≠ 0) :
    condDistrib V Hst P h = (cond P (Hst ⁻¹' {h})).map V := by
  apply Measure.ext
  intro A MeasurableA
  rw [condDistrib_apply_of_ne_zero MeasurableV h Positive A,
    Measure.map_apply MeasurableHistory (measurableSet_singleton h),
    Measure.map_apply (MeasurableHistory.prodMk MeasurableV)
      ((measurableSet_singleton h).prod MeasurableA),
    Measure.map_apply MeasurableV MeasurableA,
    cond_apply' (MeasurableA.preimage MeasurableV)]
  rfl

/-- The complete ordered history strictly before time t; at zero this is an empty vector. -/
def ExtendedNatPrefix {Ω : Type*} (X : ℕ → Ω → (WithTop ℕ)) (t : ℕ) (ω : Ω) : Fin t → (WithTop ℕ) :=
  fun i => X i ω

/-- Measurability of the full prefix follows from coordinate measurability. -/
theorem ExtendedNatPrefixMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → (WithTop ℕ)) (MeasurableX : ∀ i, Measurable (X i)) (t : ℕ) :
    Measurable (ExtendedNatPrefix X t) := by
  exact measurable_pi_lambda _ (fun i => MeasurableX i)

/-- The prefix cost equals the corresponding finite partial sum. -/
theorem ExtendedNatPrefixSum {Ω : Type*} (X : ℕ → Ω → (WithTop ℕ)) (t : ℕ) (ω : Ω) :
    (∑ i : Fin t, ExtendedNatPrefix X t ω i) = ∑ i ∈ Finset.range t, X i ω := by
  exact Fin.sum_univ_eq_sum_range (fun i => X i ω) t

/-- Only the first n+1 reference variables need to be independent. -/
theorem ExtendedNatIndependentPrefixSum {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (Y : ℕ → Ω → (WithTop ℕ)) (MeasurableY : ∀ i, Measurable (Y i))
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


/-- Convolution with a common independent cost preserves stochastic order. -/
theorem ExtendedNatConvRight (ρ μ ν : Measure (WithTop ℕ))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Ordered : StochasticDominated μ ν) :
    StochasticDominated (ρ ∗ μ) (ρ ∗ ν) := by
  have Bound := ExtendedNatKernelAdd ρ (Kernel.const (WithTop ℕ) μ)
    (Kernel.const (WithTop ℕ) ν) id measurable_id (ae_of_all _ (fun _ => Ordered))
  rw [ExtendedNatConstantKernelAdditionLaw _ _ _ measurable_id,
    ExtendedNatConstantKernelAdditionLaw _ _ _ measurable_id, Measure.map_id] at Bound
  exact Bound

/-- Convolution is monotone in both extended-natural probability laws. -/
theorem ExtendedNatConv (μ ν ρ σ : Measure (WithTop ℕ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (First : StochasticDominated μ ν) (Second : StochasticDominated ρ σ) :
    StochasticDominated (μ ∗ ρ) (ν ∗ σ) := by
  have FirstSummand : StochasticDominated (μ ∗ ρ) (ν ∗ ρ) := by
    rw [Measure.conv_comm μ ρ, Measure.conv_comm ν ρ]
    exact ExtendedNatConvRight ρ μ ν First
  exact StochasticDominatedTrans FirstSummand (ExtendedNatConvRight ν ρ σ Second)

/-- Replace the next conditional increment by an independent dominating cost. -/
theorem ExtendedNatConditionalConvolution {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (Hst : Ω → H) (V : Ω → WithTop ℕ)
    (MeasurableHistory : Measurable Hst) (MeasurableV : Measurable V)
    (g : H → WithTop ℕ) (MeasurableG : Measurable g)
    (ν : Measure (WithTop ℕ)) [IsProbabilityMeasure ν]
    (Ordered : ∀ᵐ h ∂P.map Hst, StochasticDominated (condDistrib V Hst P h) ν) :
    StochasticDominated (P.map (fun ω => g (Hst ω)+V ω)) ((P.map (g ∘ Hst)) ∗ ν) := by
  have Bound := ExtendedNatConditionalAdd P Hst V MeasurableHistory MeasurableV g MeasurableG ν Ordered
  have HistoryProbability : IsProbabilityMeasure (P.map Hst) :=
    Measure.isProbabilityMeasure_map MeasurableHistory.aemeasurable
  rw [← Measure.compProd_const, ExtendedNatConstantKernelAdditionLaw _ _ _ MeasurableG,
    Measure.map_map MeasurableG MeasurableHistory] at Bound
  exact Bound

/-- Compare finite sums using full-history conditional kernels; only the reference costs are independent. -/
theorem ExtendedNatSequentialSumKernel {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → (WithTop ℕ)) (Y : ℕ → Ω' → (WithTop ℕ))
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (n : ℕ) (IndependentY : iIndepFun (fun i : Fin n => Y i) Q)
    (Conditional : ∀ t < n, ∀ᵐ h ∂P.map (ExtendedNatPrefix X t),
      StochasticDominated (condDistrib (X t) (ExtendedNatPrefix X t) P h) (Q.map (Y t))) :
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
      have MeasurableHistorySum : Measurable (fun h : Fin n → (WithTop ℕ) => ∑ i, h i) :=
        Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      have AddBound := ExtendedNatConditionalConvolution P (ExtendedNatPrefix X n) (X n)
        (ExtendedNatPrefixMeasurable X MeasurableX n) (MeasurableX n)
        (fun h => ∑ i, h i) MeasurableHistorySum (Q.map (Y n))
        (Conditional n (Nat.lt_succ_self n))
      simp only [Function.comp_def, ExtendedNatPrefixSum] at AddBound
      have ConvolutionBound := ExtendedNatConv _ _ _ _ Previous
        (StochasticDominatedRefl (Q.map (Y n)))
      have Compared := StochasticDominatedTrans AddBound ConvolutionBound
      have IndependentSum := ExtendedNatIndependentPrefixSum Q Y MeasurableY n IndependentY
      have SumLaw := IndependentSum.map_add_eq_map_conv_map MeasurableSumY (MeasurableY n)
      rw [← SumLaw] at Compared
      change StochasticDominated (P.map (fun ω => (∑ i ∈ Finset.range n, X i ω) + X n ω))
        (Q.map (fun ω => (∑ i ∈ Finset.range n, Y i ω) + Y n ω)) at Compared
      simpa only [Finset.sum_range_succ, Pi.add_apply] using Compared


/-- The countable-history event formulation. Infinite and skipped stages are retained in the sum. -/
theorem ExtendedNatSequentialSum {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → WithTop ℕ) (Y : ℕ → Ω' → WithTop ℕ)
    (MeasurableX : ∀ i, Measurable (X i)) (MeasurableY : ∀ i, Measurable (Y i))
    (n : ℕ) (IndependentY : iIndepFun (fun i : Fin n => Y i) Q)
    (Conditional : ∀ t < n, ∀ h : Fin t → WithTop ℕ,
      P (ExtendedNatPrefix X t ⁻¹' {h}) ≠ 0 →
      StochasticDominated ((cond P (ExtendedNatPrefix X t ⁻¹' {h})).map (X t)) (Q.map (Y t))) :
    StochasticDominated (P.map (fun ω => ∑ i ∈ Finset.range n, X i ω))
      (Q.map (fun ω => ∑ i ∈ Finset.range n, Y i ω)) := by
  apply ExtendedNatSequentialSumKernel P Q X Y MeasurableX MeasurableY n IndependentY
  intro t BeforeEnd
  apply AEOfPositiveAtomsOnCountableSupport _ univ (Set.to_countable _)
    (ae_of_all _ (fun _ => mem_univ _))
  intro h PositiveAtom
  rw [ExtendedNatConditionalDistributionAtAtom P (ExtendedNatPrefix X t) (X t)
    (ExtendedNatPrefixMeasurable X MeasurableX t) (MeasurableX t) h PositiveAtom]
  apply Conditional t BeforeEnd h
  rw [Measure.map_apply (ExtendedNatPrefixMeasurable X MeasurableX t)
    (measurableSet_singleton h)] at PositiveAtom
  exact PositiveAtom

/-- Two independent pairs may be compared without any finite-mean or termination assumption. -/
theorem ExtendedNatIndependentAdd {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X₁ X₂ : Ω → (WithTop ℕ)) (Y₁ Y₂ : Ω' → (WithTop ℕ))
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
  exact ExtendedNatConv _ _ _ _ First Second

/-- Extended-natural version of Lemma 1.8.4 for a finite subfamily. Taking the index type to be Fin n and
the finset to be univ gives the book statement, including the empty sum. -/
theorem ExtendedNatIndependentSum {ι Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ι → Ω → (WithTop ℕ)) (Y : ι → Ω' → (WithTop ℕ))
    (MeasurableX : ∀ i, AEMeasurable (X i) P)
    (MeasurableY : ∀ i, AEMeasurable (Y i) Q)
    (IndependentX : iIndepFun X P) (IndependentY : iIndepFun Y Q)
    (Dominated : ∀ i, StochasticDominated (P.map (X i)) (Q.map (Y i))) (S : Finset ι) :
    StochasticDominated (P.map (∑ i ∈ S, X i)) (Q.map (∑ i ∈ S, Y i)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      change StochasticDominated (P.map (fun _ => (0 : (WithTop ℕ)))) (Q.map (fun _ => (0 : (WithTop ℕ))))
      rw [Measure.map_const, Measure.map_const, measure_univ, measure_univ, one_smul]
      exact StochasticDominatedRefl _
  | insert i S NotMember InductionHypothesis =>
      rw [Finset.sum_insert NotMember, Finset.sum_insert NotMember]
      exact ExtendedNatIndependentAdd P Q _ _ _ _
        (MeasurableX i) (Finset.aemeasurable_sum S (fun j _ => MeasurableX j))
        (MeasurableY i) (Finset.aemeasurable_sum S (fun j _ => MeasurableY j))
        (IndependentX.indepFun_finsetSum_of_notMem₀ MeasurableX NotMember).symm
        (IndependentY.indepFun_finsetSum_of_notMem₀ MeasurableY NotMember).symm
        (Dominated i) InductionHypothesis

/-- Almost-sure finiteness transfers from a dominating reference law. -/
theorem ExtendedNatFiniteOfDomination (μ ν : Measure (WithTop ℕ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Ordered : StochasticDominated μ ν) (FiniteReference : ∀ᵐ x ∂ν, x ≠ ⊤) :
    ∀ᵐ x ∂μ, x ≠ ⊤ := by
  let FiniteTimes := {x : WithTop ℕ | x ≠ ⊤}
  have FiniteUnion : (⋃ n : ℕ, Iic (n : WithTop ℕ)) = FiniteTimes := by
    ext x
    cases x using WithTop.recTopCoe with
    | top => simp [FiniteTimes]
    | coe n =>
        constructor
        · intro _
          exact WithTop.coe_ne_top
        · intro _
          apply mem_iUnion.mpr
          refine ⟨n, ?_⟩
          change (n : WithTop ℕ) ≤ (n : WithTop ℕ)
          exact le_rfl
  have Increasing : Monotone (fun n : ℕ => Iic (n : WithTop ℕ)) := by
    intro m n Before
    exact Iic_subset_Iic.mpr (by exact_mod_cast Before)
  have FiniteMass : ν FiniteTimes ≤ μ FiniteTimes := by
    rw [← FiniteUnion, Increasing.directed_le.measure_iUnion, Increasing.directed_le.measure_iUnion]
    exact iSup_mono (fun n => Ordered (n : WithTop ℕ))
  have MeasurableFinite : MeasurableSet FiniteTimes := (Set.to_countable FiniteTimes).measurableSet
  have ReferenceMass : ν FiniteTimes = 1 := by
    exact (mem_ae_iff_prob_eq_one MeasurableFinite).mp FiniteReference
  apply (mem_ae_iff_prob_eq_one MeasurableFinite).mpr
  apply le_antisymm (prob_le_one)
  rw [ReferenceMass] at FiniteMass
  exact FiniteMass


end
end ECTheoryLib.Probability
