import ECTheoryLib.Probability.Sampling.UniformSubset

/-!
# Exact hypergeometric count law and size symmetry

A finite partition bijection counts intersections of the actual uniform
fixed-size sample. Mathlib supplies powersetCard counts, product counts
and choose identities. The point formula yields equality of full count
PMFs when draw and observation sizes are swapped, then finite-size
concentration with min(k,m). Impossible cases and empty samples remain
explicit. This extends, but does not complete, all consequences of1.10.25.
-/

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory Set
open scoped Classical
noncomputable section

/-- A k-subset with r observed elements is uniquely a pair of an r-subset
of A and a (k-r)-subset of its complement. Cardinalities use Mathlib's
powersetCard and product rules. -/
theorem IntersectionFamilyCard {N k r : ℕ} (A : Finset (Fin N)) (Fits : r≤k) :
    (((Finset.univ : Finset (Fin N)).powersetCard k).filter (fun U => (U∩A).card=r)).card=
      A.card.choose r * (N-A.card).choose (k-r) := by
  classical
  calc
    _ = (A.powersetCard r ×ˢ ((Finset.univ\A).powersetCard (k-r))).card := by
      apply Finset.card_bij (fun U _ => (U∩A,U\A))
      · intro U InFamily
        obtain ⟨InSize,Count⟩ := Finset.mem_filter.mp InFamily
        obtain ⟨_Subset,Size⟩ := Finset.mem_powersetCard.mp InSize
        apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right,Count⟩
        · apply Finset.mem_powersetCard.mpr
          constructor
          · intro i Inside
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,(Finset.mem_sdiff.mp Inside).2⟩
          · rw [Finset.card_sdiff,Finset.inter_comm A U,Size,Count]
      · intro U _InU V _InV Same
        have Inter := congrArg Prod.fst Same
        have Difference := congrArg Prod.snd Same
        change U∩A=V∩A at Inter
        change U\A=V\A at Difference
        calc
          U = (U\A)∪(U∩A) := (Finset.sdiff_union_inter U A).symm
          _ = (V\A)∪(V∩A) := by rw [Inter,Difference]
          _ = V := Finset.sdiff_union_inter V A
      · intro B InProduct
        obtain ⟨InLeft,InRight⟩ := Finset.mem_product.mp InProduct
        obtain ⟨LeftSubset,LeftSize⟩ := Finset.mem_powersetCard.mp InLeft
        obtain ⟨RightSubset,RightSize⟩ := Finset.mem_powersetCard.mp InRight
        have Apart : Disjoint B.1 B.2 := by
          apply Finset.disjoint_left.mpr
          intro i InLeft InRight
          exact (Finset.mem_sdiff.mp (RightSubset InRight)).2 (LeftSubset InLeft)
        have RecoverLeft : (B.1∪B.2)∩A=B.1 := by
          ext i
          simp only [Finset.mem_inter,Finset.mem_union]
          constructor
          · rintro ⟨InLeft|InRight,InA⟩
            · exact InLeft
            · exact False.elim ((Finset.mem_sdiff.mp (RightSubset InRight)).2 InA)
          · intro Inside
            exact ⟨Or.inl Inside,LeftSubset Inside⟩
        have RecoverRight : (B.1∪B.2)\A=B.2 := by
          ext i
          simp only [Finset.mem_sdiff,Finset.mem_union]
          constructor
          · rintro ⟨InLeft|InRight,Outside⟩
            · exact False.elim (Outside (LeftSubset InLeft))
            · exact InRight
          · intro Inside
            exact ⟨Or.inr Inside,(Finset.mem_sdiff.mp (RightSubset Inside)).2⟩
        refine ⟨B.1∪B.2,?_,?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_powersetCard.mpr
            refine ⟨Finset.subset_univ _,?_⟩
            rw [Finset.card_union_of_disjoint Apart,LeftSize,RightSize]
            omega
          · rw [RecoverLeft,LeftSize]
        · exact Prod.ext RecoverLeft RecoverRight
    _ = _ := by
      rw [Finset.card_product,Finset.card_powersetCard,Finset.card_powersetCard,
        Finset.card_sdiff_of_subset (Finset.subset_univ A)]
      simp only [Finset.card_univ,Fintype.card_fin]

/-- Exact hypergeometric point mass of the actual intersection count.
The guard preserves impossible r>k cases despite natural subtraction. -/
theorem IntersectionProbability {N k : ℕ} (Admissible : k≤N) (A : Finset (Fin N)) (r : ℕ) :
    (Law N k Admissible).toMeasure.real {U | (U∩A).card=r}=
      if r≤k then (A.card.choose r : ℝ)*((N-A.card).choose (k-r) : ℝ)/(N.choose k : ℝ) else 0 := by
  classical
  rw [EventProbability]
  simp only [mem_ofPred_eq]
  by_cases Fits : r≤k
  · rw [if_pos Fits,IntersectionFamilyCard A Fits,Nat.cast_mul]
  · rw [if_neg Fits]
    apply div_eq_zero_iff.mpr
    left
    apply Nat.cast_eq_zero.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro U InFamily Count
    have Size := (Finset.mem_powersetCard.mp InFamily).2
    have Bound := Finset.card_le_card (Finset.inter_subset_left : U∩A⊆U)
    rw [Count,Size] at Bound
    exact Fits Bound

/-- Distinct observed coordinates count exactly the intersection with their image. -/
theorem ObservedCountAsIntersection {N m : ℕ} (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (U : Finset (Fin N)) :
    ObservedCount Observed U=(U∩Finset.univ.image Observed).card := by
  classical
  have Image : (Finset.univ.filter (fun j => Observed j∈U)).image Observed=
      U∩Finset.univ.image Observed := by
    ext i
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter]
    constructor
    · rintro ⟨j,Inside,rfl⟩
      exact ⟨Inside,j,rfl⟩
    · rintro ⟨Inside,j,rfl⟩
      exact ⟨j,Inside,rfl⟩
  rw [← Image,Finset.card_image_of_injective _ Injective]
  simp [ObservedCount]

theorem ObservedCountProbability {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (r : ℕ) :
    (Law N k Admissible).toMeasure.real {U | ObservedCount Observed U=r}=
      if r≤k then (m.choose r : ℝ)*((N-m).choose (k-r) : ℝ)/(N.choose k : ℝ) else 0 := by
  simp_rw [ObservedCountAsIntersection Observed Injective]
  rw [IntersectionProbability,Finset.card_image_of_injective _ Injective]
  simp only [Finset.card_univ,Fintype.card_fin]

end
end ECTheoryLib.Probability.UniformSubset

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory Set
noncomputable section

/-- Two successive disjoint choices may be made in either order. -/
theorem DisjointChooseSymmetry (N a b : ℕ) :
    N.choose a * (N-a).choose b=N.choose b * (N-b).choose a := by
  have First := Nat.choose_mul (n := N) (k := a+b) (s := a) (by omega)
  have Second := Nat.choose_mul (n := N) (k := a+b) (s := b) (by omega)
  rw [Nat.add_sub_cancel_left] at First
  rw [Nat.add_sub_cancel_right] at Second
  have Middle : (a+b).choose a=(a+b).choose b := Nat.choose_symm_add
  rw [Middle] at First
  exact First.symm.trans Second

/-- Scalar hypergeometric point-mass expression, with zero outside the sample
range. Its probability interpretation requires k,m≤N, as in the law theorems. -/
def HypergeometricMass (N k m r : ℕ) : ℝ :=
  if r≤k then (m.choose r : ℝ)*((N-m).choose (k-r) : ℝ)/(N.choose k : ℝ) else 0

/-- Symmetry in the drawn size k and observed size m, including impossible r. -/
theorem HypergeometricMassSymmetry {N k m : ℕ} (DrawFits : k≤N) (ObserveFits : m≤N) (r : ℕ) :
    HypergeometricMass N k m r=HypergeometricMass N m k r := by
  by_cases FitsDraw : r≤k
  · by_cases FitsObserve : r≤m
    · simp only [HypergeometricMass,if_pos FitsDraw,if_pos FitsObserve]
      apply (div_eq_div_iff
        (Nat.cast_ne_zero.mpr (Nat.choose_pos DrawFits).ne')
        (Nat.cast_ne_zero.mpr (Nat.choose_pos ObserveFits).ne')).mpr
      have Left := Nat.choose_mul (n := N) (k := m) FitsObserve
      have Right := Nat.choose_mul (n := N) (k := k) FitsDraw
      have Middle := DisjointChooseSymmetry (N-r) (m-r) (k-r)
      rw [show N-r-(m-r)=N-m by omega,show N-r-(k-r)=N-k by omega] at Middle
      have Counting : (N.choose m*m.choose r)*(N-m).choose (k-r)=
          (N.choose k*k.choose r)*(N-k).choose (m-r) := by
        rw [Left,Right,mul_assoc,mul_assoc,Middle]
      have RealCounting : ((N.choose m : ℝ)*(m.choose r : ℝ))*((N-m).choose (k-r) : ℝ)=
          ((N.choose k : ℝ)*(k.choose r : ℝ))*((N-k).choose (m-r) : ℝ) := by
        exact_mod_cast Counting
      nlinarith [RealCounting]
    · simp [HypergeometricMass,FitsDraw,FitsObserve,Nat.choose_eq_zero_of_lt (lt_of_not_ge FitsObserve)]
  · by_cases FitsObserve : r≤m
    · simp [HypergeometricMass,FitsDraw,FitsObserve,Nat.choose_eq_zero_of_lt (lt_of_not_ge FitsDraw)]
    · simp [HypergeometricMass,FitsDraw,FitsObserve]

theorem IntersectionProbabilityMass {N k : ℕ} (Admissible : k≤N) (A : Finset (Fin N)) (r : ℕ) :
    (Law N k Admissible).toMeasure.real {U | (U∩A).card=r}=HypergeometricMass N k A.card r :=
  IntersectionProbability Admissible A r

end
end ECTheoryLib.Probability.UniformSubset

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory Set
noncomputable section

/-- Distribution of the actual observed count under uniform subset sampling. -/
def ObservedCountLaw {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N) : PMF ℕ :=
  (Law N k Admissible).map (ObservedCount Observed)

theorem ObservedCountLawEvent {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N) (E : Set ℕ) :
    (ObservedCountLaw Admissible Observed).toMeasure.real E=
      (Law N k Admissible).toMeasure.real {U | ObservedCount Observed U∈E} := by
  unfold ObservedCountLaw
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  rfl

theorem ObservedCountLawMass {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (r : ℕ) :
    (ObservedCountLaw Admissible Observed r).toReal=HypergeometricMass N k m r := by
  rw [← PMF.toMeasure_apply_singleton _ r (measurableSet_singleton r)]
  change (ObservedCountLaw Admissible Observed).toMeasure.real {r}=_
  rw [ObservedCountLawEvent]
  simpa only [mem_singleton_iff,HypergeometricMass] using
    ObservedCountProbability Admissible Observed Injective r

/-- Equality of complete count distributions when drawn and observed sizes
are interchanged. The actual coordinate labels may be chosen independently. -/
theorem ObservedCountLawSwap {N k m : ℕ} (DrawFits : k≤N) (ObserveFits : m≤N)
    (Observed : Fin m → Fin N) (OtherObserved : Fin k → Fin N)
    (Injective : Function.Injective Observed) (OtherInjective : Function.Injective OtherObserved) :
    ObservedCountLaw DrawFits Observed=ObservedCountLaw ObserveFits OtherObserved := by
  ext r
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [ObservedCountLawMass DrawFits Observed Injective,ObservedCountLawMass ObserveFits OtherObserved OtherInjective]
  exact HypergeometricMassSymmetry DrawFits ObserveFits r

end
end ECTheoryLib.Probability.UniformSubset

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory Set
noncomputable section

theorem ObservedCountEventSwap {N k m : ℕ} (DrawFits : k≤N) (ObserveFits : m≤N)
    (Observed : Fin m → Fin N) (OtherObserved : Fin k → Fin N)
    (Injective : Function.Injective Observed) (OtherInjective : Function.Injective OtherObserved)
    (E : Set ℕ) :
    (Law N k DrawFits).toMeasure.real {U | ObservedCount Observed U∈E}=
      (Law N m ObserveFits).toMeasure.real {U | ObservedCount OtherObserved U∈E} := by
  rw [← ObservedCountLawEvent,← ObservedCountLawEvent,
    ObservedCountLawSwap DrawFits ObserveFits Observed OtherObserved Injective OtherInjective]

/-- The finite-size upper bound may use min(k,m), via equality of the two
actual count distributions rather than a presumed independent model. -/
theorem ObservedCountMinUpperTail {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (d : ℝ) (Nonnegative : 0≤d) :
    (Law N k Admissible).toMeasure.real
      {U | (1+d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))≤(ObservedCount Observed U : ℝ)}≤
        FiniteChernoffUpperBound (min k m) ((m : ℝ)*((k : ℝ)/(N : ℝ))) d := by
  by_cases ObserveSmaller : m≤k
  · rw [min_eq_right ObserveSmaller]
    exact ObservedCountFiniteUpperTail Admissible Observed Injective d Nonnegative
  · have DrawSmaller : k≤m := by omega
    rw [min_eq_left DrawSmaller]
    have ObserveFits : m≤N := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective Observed Injective
    let Other : Fin k → Fin N := fun i => i.castLE Admissible
    have OtherInjective : Function.Injective Other := by
      intro i j Same
      apply Fin.ext
      exact congrArg (fun x : Fin N => x.val) Same
    have Equal := ObservedCountEventSwap Admissible ObserveFits Observed Other Injective OtherInjective
      {r : ℕ | (1+d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))≤(r : ℝ)}
    change (Law N k Admissible).toMeasure.real
      {U | (1+d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))≤(ObservedCount Observed U : ℝ)}=
      (Law N m ObserveFits).toMeasure.real
      {U | (1+d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))≤(ObservedCount Other U : ℝ)} at Equal
    rw [Equal]
    have Bound := ObservedCountFiniteUpperTail ObserveFits Other OtherInjective d Nonnegative
    have Mean : (k : ℝ)*((m : ℝ)/(N : ℝ))=(m : ℝ)*((k : ℝ)/(N : ℝ)) := by ring
    rw [Mean] at Bound
    exact Bound

theorem ObservedCountMinLowerTail {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Law N k Admissible).toMeasure.real
      {U | (ObservedCount Observed U : ℝ)≤(1-d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))}≤
        FiniteChernoffLowerBound (min k m) ((m : ℝ)*((k : ℝ)/(N : ℝ))) d := by
  by_cases ObserveSmaller : m≤k
  · rw [min_eq_right ObserveSmaller]
    exact ObservedCountFiniteLowerTail Admissible Observed Injective d InUnit
  · have DrawSmaller : k≤m := by omega
    rw [min_eq_left DrawSmaller]
    have ObserveFits : m≤N := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective Observed Injective
    let Other : Fin k → Fin N := fun i => i.castLE Admissible
    have OtherInjective : Function.Injective Other := by
      intro i j Same
      apply Fin.ext
      exact congrArg (fun x : Fin N => x.val) Same
    have Equal := ObservedCountEventSwap Admissible ObserveFits Observed Other Injective OtherInjective
      {r : ℕ | (r : ℝ)≤(1-d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))}
    change (Law N k Admissible).toMeasure.real
      {U | (ObservedCount Observed U : ℝ)≤(1-d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))}=
      (Law N m ObserveFits).toMeasure.real
      {U | (ObservedCount Other U : ℝ)≤(1-d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))} at Equal
    rw [Equal]
    have Bound := ObservedCountFiniteLowerTail ObserveFits Other OtherInjective d InUnit
    have Mean : (k : ℝ)*((m : ℝ)/(N : ℝ))=(m : ℝ)*((k : ℝ)/(N : ℝ)) := by ring
    rw [Mean] at Bound
    exact Bound

end
end ECTheoryLib.Probability.UniformSubset
