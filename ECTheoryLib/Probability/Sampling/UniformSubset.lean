import ECTheoryLib.Probability.PMF.FinitePMF
import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationFinite
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Uniform fixed-size subset sampling

The actual law reuses Mathlib uniformOfFinset and powersetCard. Exact
containment and avoidance probabilities prove both all-subset correlation
conditions. Observed counts have mean mk/N; their two-sided finite-size
concentration requires distinct observations. Empty and full samples are
valid. Theorem 1.10.25 is only partially covered: symmetry in sample and
observation size and all listed variance/weighted consequences remain separate.
-/

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory Set
open scoped Classical
noncomputable section

/-- Uniform sampling of exactly k elements without replacement. Mathlib
supplies both the finite family and its uniform PMF, including k=N=0. -/
def Law (N k : ℕ) (Admissible : k≤N) : PMF (Finset (Fin N)) :=
  PMF.uniformOfFinset ((Finset.univ : Finset (Fin N)).powersetCard k)
    (Finset.powersetCard_nonempty.mpr (by simpa only [Finset.card_univ,Fintype.card_fin] using Admissible))

theorem Support {N k : ℕ} (Admissible : k≤N) (U : Finset (Fin N)) :
    U∈(Law N k Admissible).support ↔ U.card=k := by
  simp [Law]

/-- Exact event probabilities come directly from Mathlib's uniform-law rule. -/
theorem EventProbability {N k : ℕ} (Admissible : k≤N) (E : Set (Finset (Fin N))) :
    (Law N k Admissible).toMeasure.real E=
      ((((Finset.univ : Finset (Fin N)).powersetCard k).filter (fun U => U∈E)).card : ℝ)/(N.choose k : ℝ) := by
  classical
  unfold Law Measure.real
  rw [PMF.toMeasure_uniformOfFinset_apply _ E (Set.to_countable _).measurableSet]
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

/-- Specifying more selected elements than are drawn is impossible; the
guard prevents truncated natural subtraction from disguising that case. -/
theorem ContainsProbability {N k : ℕ} (Admissible : k≤N) (A : Finset (Fin N)) :
    (Law N k Admissible).toMeasure.real {U | A⊆U}=
      if A.card≤k then ((N-A.card).choose (k-A.card) : ℝ)/(N.choose k : ℝ) else 0 := by
  classical
  rw [EventProbability]
  by_cases Fits : A.card≤k
  · rw [if_pos Fits]
    simp only [mem_ofPred_eq]
    rw [Finset.card_filter_powersetCard_subset A Finset.univ k (Finset.subset_univ A) Fits]
    simp only [Finset.card_univ,Fintype.card_fin]
  · rw [if_neg Fits]
    simp only [mem_ofPred_eq]
    apply div_eq_zero_iff.mpr
    left
    apply Nat.cast_eq_zero.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro U InFamily Contains
    have Size := (Finset.mem_powersetCard.mp InFamily).2
    exact Fits (Size ▸ Finset.card_le_card Contains)

end
end ECTheoryLib.Probability.UniformSubset

namespace ECTheoryLib.Probability
noncomputable section

/-- The without-replacement joint-selection ratio is bounded by the
corresponding independent marginal power. All subtraction is guarded. -/
theorem ChooseRatioLePower (N k w : ℕ) (Admissible : k≤N) (WithinUniverse : w≤N) :
    (k.choose w : ℝ)/(N.choose w : ℝ)≤((k : ℝ)/(N : ℝ))^w := by
  by_cases Empty : N=0
  · subst N
    have KZero : k=0 := Nat.eq_zero_of_le_zero Admissible
    have WZero : w=0 := Nat.eq_zero_of_le_zero WithinUniverse
    subst k
    subst w
    norm_num
  have PositiveN : (0 : ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero Empty)
  by_cases TooMany : k<w
  · rw [Nat.choose_eq_zero_of_lt TooMany,Nat.cast_zero,zero_div]
    positivity
  have Fits : w≤k := le_of_not_gt TooMany
  have FactorialNonzero : (w.factorial : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero w)
  have Ratio : (k.choose w : ℝ)/(N.choose w : ℝ)=
      (k.descFactorial w : ℝ)/(N.descFactorial w : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose,
      Nat.cast_mul,Nat.cast_mul,mul_div_mul_left _ _ FactorialNonzero]
  rw [Ratio,Nat.descFactorial_eq_prod_range,Nat.descFactorial_eq_prod_range,
    Nat.cast_prod,Nat.cast_prod,← Finset.prod_div_distrib]
  calc
    _≤∏ _i∈Finset.range w, ((k : ℝ)/(N : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i InRange
        have Small : i<w := Finset.mem_range.mp InRange
        have BelowK : i≤k := Small.le.trans Fits
        have BelowN : i<N := Small.trans_le WithinUniverse
        rw [Nat.cast_sub BelowK,Nat.cast_sub BelowN.le]
        apply (div_le_div_iff₀ (sub_pos.mpr (Nat.cast_lt.mpr BelowN)) PositiveN).mpr
        have KI : (k : ℝ)≤N := Nat.cast_le.mpr Admissible
        have NonnegativeI : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        nlinarith
    _=_ := by simp [div_pow]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory Set
noncomputable section

/-- A second exact form makes the joint-probability comparison transparent,
and is valid even when the requested set is too large to be drawn. -/
theorem ContainsProbabilityRatio {N k : ℕ} (Admissible : k≤N) (A : Finset (Fin N)) :
    (Law N k Admissible).toMeasure.real {U | A⊆U}=
      (k.choose A.card : ℝ)/(N.choose A.card : ℝ) := by
  have SizeBound : A.card≤N := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ A)
  rw [ContainsProbability]
  split_ifs with Fits
  · have ChoosePositive : (0 : ℝ)<N.choose k := Nat.cast_pos.mpr (Nat.choose_pos Admissible)
    have AChoosePositive : (0 : ℝ)<N.choose A.card := Nat.cast_pos.mpr (Nat.choose_pos SizeBound)
    apply (div_eq_div_iff ChoosePositive.ne' AChoosePositive.ne').mpr
    have Count : (N.choose k : ℝ)*(k.choose A.card : ℝ)=
        (N.choose A.card : ℝ)*((N-A.card).choose (k-A.card) : ℝ) := by
      exact_mod_cast Nat.choose_mul (n := N) Fits
    nlinarith
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge Fits),Nat.cast_zero,zero_div]

theorem Marginal {N k : ℕ} (Admissible : k≤N) (i : Fin N) :
    (Law N k Admissible).toMeasure.real {U | i∈U}=(k : ℝ)/(N : ℝ) := by
  have Bound := ContainsProbabilityRatio Admissible {i}
  simpa only [Finset.singleton_subset_iff,Finset.card_singleton,Nat.choose_one_right] using Bound

/-- The complete all-subset one-negative-correlation condition of actual
uniform sampling without replacement, including empty/full samples. -/
theorem OneNegativeCorrelation {N k : ℕ} (Admissible : k≤N) :
    OneNegativelyCorrelated (Law N k Admissible).toMeasure
      (fun i : Fin N => {U : Finset (Fin N) | i∈U}) := by
  intro A
  have Event : (⋂ i∈A, {U : Finset (Fin N) | i∈U})={U | A⊆U} := by
    ext U
    simp [Finset.subset_iff]
  rw [Event,ContainsProbabilityRatio]
  simp_rw [Marginal Admissible]
  simp only [Finset.prod_const]
  have SizeBound : A.card≤N := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ A)
  exact ChooseRatioLePower N k A.card Admissible SizeBound

end
end ECTheoryLib.Probability.UniformSubset

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory Set
noncomputable section

/-- Avoiding a specified set counts fixed-size subsets of its complement.
The binomial coefficient automatically vanishes for an impossible size. -/
theorem MissesProbability {N k : ℕ} (Admissible : k≤N) (A : Finset (Fin N)) :
    (Law N k Admissible).toMeasure.real {U | Disjoint U A}=
      ((N-A.card).choose k : ℝ)/(N.choose k : ℝ) := by
  classical
  rw [EventProbability]
  simp only [mem_ofPred_eq]
  have Family : ((Finset.univ : Finset (Fin N)).powersetCard k).filter (fun U => Disjoint U A)=
      (Finset.univ\A).powersetCard k := by
    ext U
    simp only [Finset.mem_filter,Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_Subset,Size⟩,Apart⟩
      refine ⟨?_,Size⟩
      intro i Inside
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,Finset.disjoint_left.mp Apart Inside⟩
    · rintro ⟨Subset,Size⟩
      refine ⟨⟨Finset.subset_univ U,Size⟩,Finset.disjoint_left.mpr ?_⟩
      intro i Inside InA
      exact (Finset.mem_sdiff.mp (Subset Inside)).2 InA
  rw [Family,Finset.card_powersetCard,Finset.card_sdiff_of_subset (Finset.subset_univ A)]
  simp only [Finset.card_univ,Fintype.card_fin]

theorem MissesProbabilityRatio {N k : ℕ} (Admissible : k≤N) (A : Finset (Fin N)) :
    (Law N k Admissible).toMeasure.real {U | Disjoint U A}=
      ((N-k).choose A.card : ℝ)/(N.choose A.card : ℝ) := by
  have SizeBound : A.card≤N := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ A)
  rw [MissesProbability]
  by_cases Fits : A.card≤N-k
  · have KFits : k≤N-A.card := by omega
    have ChoosePositive : (0 : ℝ)<N.choose k := Nat.cast_pos.mpr (Nat.choose_pos Admissible)
    have AChoosePositive : (0 : ℝ)<N.choose A.card := Nat.cast_pos.mpr (Nat.choose_pos SizeBound)
    apply (div_eq_div_iff ChoosePositive.ne' AChoosePositive.ne').mpr
    have Count := Nat.choose_mul (n := N) Fits
    rw [Nat.choose_symm Admissible,show N-k-A.card=(N-A.card)-k by omega,Nat.choose_symm KFits] at Count
    have RealCount : (N.choose k : ℝ)*((N-k).choose A.card : ℝ)=
        (N.choose A.card : ℝ)*((N-A.card).choose k : ℝ) := by exact_mod_cast Count
    nlinarith
  · have KLarge : N-A.card<k := by omega
    rw [Nat.choose_eq_zero_of_lt KLarge,Nat.choose_eq_zero_of_lt (lt_of_not_ge Fits)]
    simp

theorem MissingMarginal {N k : ℕ} (Admissible : k≤N) (i : Fin N) :
    (Law N k Admissible).toMeasure.real {U | i∉U}=((N-k : ℕ) : ℝ)/(N : ℝ) := by
  have Bound := MissesProbabilityRatio Admissible {i}
  simpa only [Finset.disjoint_singleton_right,Finset.card_singleton,Nat.choose_one_right] using Bound

/-- Actual uniform fixed-size sampling also satisfies the full complementary
product condition, without invoking an independent reference family. -/
theorem ZeroNegativeCorrelation {N k : ℕ} (Admissible : k≤N) :
    ZeroNegativelyCorrelated (Law N k Admissible).toMeasure
      (fun i : Fin N => {U : Finset (Fin N) | i∈U}) := by
  intro A
  have Event : (⋂ i∈A, {U : Finset (Fin N) | i∈U}ᶜ)={U | Disjoint U A} := by
    ext U
    simp only [mem_iInter,mem_compl_iff,mem_ofPred_eq]
    constructor
    · intro Avoid
      apply Finset.disjoint_left.mpr
      intro i InU InA
      exact Avoid i InA InU
    · intro Apart i InA InU
      exact Finset.disjoint_left.mp Apart InU InA
  rw [Event,MissesProbabilityRatio]
  have Complement (i : Fin N) : {U : Finset (Fin N) | i∈U}ᶜ={U | i∉U} := rfl
  simp_rw [Complement,MissingMarginal Admissible]
  simp only [Finset.prod_const]
  have SizeBound : A.card≤N := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ A)
  exact ChooseRatioLePower N (N-k) A.card (Nat.sub_le N k) SizeBound

end
end ECTheoryLib.Probability.UniformSubset

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Count membership along the observation map, counting repeated positions
with multiplicity. Concentration results separately require injectivity. -/
def ObservedCount {N m : ℕ} (Observed : Fin m → Fin N) (U : Finset (Fin N)) : ℕ :=
  ∑ j : Fin m, if Observed j∈U then 1 else 0

theorem ObservedCountAsIndicatorSum {N m : ℕ} (Observed : Fin m → Fin N) (U : Finset (Fin N)) :
    (ObservedCount Observed U : ℝ)=
      ∑ j, {V : Finset (Fin N) | Observed j∈V}.indicator (fun _ => (1 : ℝ)) U := by
  classical
  simp only [ObservedCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro j _
  by_cases Inside : Observed j∈U <;> simp [Inside]

/-- The actual hypergeometric count mean, including empty universe and empty
sample. An observation may be repeated for this expectation identity alone. -/
theorem ObservedCountExpectation {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N) :
    (∫ U, (ObservedCount Observed U : ℝ) ∂(Law N k Admissible).toMeasure)=
      (m : ℝ)*((k : ℝ)/(N : ℝ)) := by
  simp_rw [ObservedCountAsIndicatorSum]
  rw [EventCountExpectation _ _ (fun _ => (Set.to_countable _).measurableSet)]
  simp_rw [Marginal Admissible]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- A genuine without-replacement count supplies all correlation premises
for a Chernoff upper bound; observations must enumerate distinct elements. -/
theorem ObservedCountUpperTail {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (d : ℝ) (Nonnegative : 0≤d) :
    (Law N k Admissible).toMeasure.real
      {U | (1+d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))≤(ObservedCount Observed U : ℝ)}≤
        Real.exp (-((1+d)*Real.log (1+d)-d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))) := by
  have Correlated := OneNegativeCorrelationReindex _ _ (OneNegativeCorrelation Admissible) Observed Injective
  have Bound := OneNegativeCorrelationChernoffUpper _
    (fun j : Fin m => {U : Finset (Fin N) | Observed j∈U})
    (fun _ => (Set.to_countable _).measurableSet) Correlated d Nonnegative
  simp_rw [Marginal Admissible,← ObservedCountAsIndicatorSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

end
end ECTheoryLib.Probability.UniformSubset

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Finite-size upper concentration uses the number of observed distinct
positions. Sample-size/observation-size symmetry is a separate result. -/
theorem ObservedCountFiniteUpperTail {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (d : ℝ) (Nonnegative : 0≤d) :
    (Law N k Admissible).toMeasure.real
      {U | (1+d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))≤(ObservedCount Observed U : ℝ)}≤
        FiniteChernoffUpperBound m ((m : ℝ)*((k : ℝ)/(N : ℝ))) d := by
  have Correlated := OneNegativeCorrelationReindex _ _ (OneNegativeCorrelation Admissible) Observed Injective
  have Bound := OneNegativeCorrelationFiniteChernoffUpper _
    (fun j : Fin m => {U : Finset (Fin N) | Observed j∈U})
    (fun _ => (Set.to_countable _).measurableSet) Correlated d Nonnegative
  simp_rw [Marginal Admissible,← ObservedCountAsIndicatorSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

theorem ObservedCountFiniteLowerTail {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Law N k Admissible).toMeasure.real
      {U | (ObservedCount Observed U : ℝ)≤(1-d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))}≤
        FiniteChernoffLowerBound m ((m : ℝ)*((k : ℝ)/(N : ℝ))) d := by
  have Correlated := ZeroNegativeCorrelationReindex _ _ (ZeroNegativeCorrelation Admissible) Observed Injective
  have Bound := ZeroNegativeCorrelationFiniteChernoffLower _
    (fun j : Fin m => {U : Finset (Fin N) | Observed j∈U})
    (fun _ => (Set.to_countable _).measurableSet) Correlated d InUnit
  simp_rw [Marginal Admissible,← ObservedCountAsIndicatorSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

/-- The usual lower exponential estimate, including zero mean and d=1,
follows from the finite-size expression without a new MGF calculation. -/
theorem ObservedCountLowerTail {N k m : ℕ} (Admissible : k≤N) (Observed : Fin m → Fin N)
    (Injective : Function.Injective Observed) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Law N k Admissible).toMeasure.real
      {U | (ObservedCount Observed U : ℝ)≤(1-d)*((m : ℝ)*((k : ℝ)/(N : ℝ)))}≤
        Real.exp (-(d+(1-d)*Real.log (1-d))*((m : ℝ)*((k : ℝ)/(N : ℝ)))) := by
  have RatioNonnegative : 0≤(k : ℝ)/(N : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have ObservedNonnegative : (0 : ℝ)≤m := Nat.cast_nonneg _
  have RatioAtMostOne : (k : ℝ)/(N : ℝ)≤1 := by
    by_cases Empty : N=0
    · simp [Empty]
    · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero Empty))).mpr (Nat.cast_le.mpr Admissible)
  exact (ObservedCountFiniteLowerTail Admissible Observed Injective d InUnit).trans
    (FiniteChernoffLowerBoundLeExp m _ d
      ⟨mul_nonneg ObservedNonnegative RatioNonnegative,
        by nlinarith⟩ InUnit)

end
end ECTheoryLib.Probability.UniformSubset

namespace ECTheoryLib.Probability.UniformSubset
open MeasureTheory Set
noncomputable section

/-- Uniform fixed-cardinality subsets are invariant under a coordinate
permutation. This is equality of the full PMF. -/
theorem Reindex {N k : ℕ} (Admissible : k≤N) (e : Equiv.Perm (Fin N)) :
    (Law N k Admissible).map e.finsetCongr=Law N k Admissible := by
  ext U
  rw [PMF.map_apply,tsum_eq_single (e.finsetCongr.symm U)]
  · rw [if_pos (e.finsetCongr.apply_symm_apply U).symm]
    simp [Law,PMF.uniformOfFinset_apply,Equiv.finsetCongr_symm,Equiv.finsetCongr_apply]
  · intro V Different
    have NotSame : U≠e.finsetCongr V := by
      intro Equal
      exact Different (by rw [Equal,Equiv.symm_apply_apply])
    simp only [if_neg NotSame]

end
end ECTheoryLib.Probability.UniformSubset
