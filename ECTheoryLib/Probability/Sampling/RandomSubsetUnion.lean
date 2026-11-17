import ECTheoryLib.Probability.PMF.FinitePMF
import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelation
import Mathlib.Probability.HasLaw

/-!
# Independent unions of negatively correlated random subsets

Full PMF laws, exact avoidance probabilities and both all-subset correlation
conditions are preserved by independent union. Mathlib product measures,
independent tuple composition and HasLaw connect arbitrary external random
subsets to the canonical finite-family law. Uniform sampling is not assumed.
-/

namespace ECTheoryLib.Probability.RandomSubset
open MeasureTheory Set
noncomputable section

/-- Union of two independently sampled finite subsets. The second law does
not depend on the first outcome. -/
def UnionLaw {N : ℕ} (P Q : PMF (Finset (Fin N))) : PMF (Finset (Fin N)) :=
  P.bind (fun U => Q.map (fun V => U∪V))

theorem UnionIntegral {N : ℕ} (P Q : PMF (Finset (Fin N))) (f : Finset (Fin N) → ℝ) :
    (∫ W, f W ∂(UnionLaw P Q).toMeasure)=
      ∫ U, (∫ V, f (U∪V) ∂Q.toMeasure) ∂P.toMeasure := by
  rw [UnionLaw,PMFIntegralBind]
  simp_rw [PMFIntegralMap]
  simp only [PMF.integral_eq_sum,smul_eq_mul]

/-- A union avoids A precisely when both independent samples avoid A. -/
theorem UnionMissingProbability {N : ℕ} (P Q : PMF (Finset (Fin N))) (A : Finset (Fin N)) :
    (UnionLaw P Q).toMeasure.real {W | Disjoint W A}=
      P.toMeasure.real {U | Disjoint U A}*Q.toMeasure.real {V | Disjoint V A} := by
  let E : Set (Finset (Fin N)) := {W | Disjoint W A}
  have MeasurableE : MeasurableSet E := (Set.to_countable _).measurableSet
  have Indicator (U V : Finset (Fin N)) :
      E.indicator (fun _ => (1 : ℝ)) (U∪V)=
        E.indicator (fun _ => (1 : ℝ)) U*E.indicator (fun _ => (1 : ℝ)) V := by
    by_cases Left : Disjoint U A <;> by_cases Right : Disjoint V A <;>
      simp [E,Finset.disjoint_union_left,Left,Right]
  have IntegralProbability (R : PMF (Finset (Fin N))) :
      (∫ W, E.indicator (fun _ => (1 : ℝ)) W ∂R.toMeasure)=R.toMeasure.real E := by
    rw [integral_indicator_const _ MeasurableE,smul_eq_mul,mul_one]
  change (UnionLaw P Q).toMeasure.real E=P.toMeasure.real E*Q.toMeasure.real E
  rw [← IntegralProbability (UnionLaw P Q),UnionIntegral]
  simp_rw [Indicator,integral_const_mul,IntegralProbability]
  rw [integral_mul_const,IntegralProbability]

theorem UnionMissingMarginal {N : ℕ} (P Q : PMF (Finset (Fin N))) (i : Fin N) :
    (UnionLaw P Q).toMeasure.real {W | i∉W}=
      P.toMeasure.real {U | i∉U}*Q.toMeasure.real {V | i∉V} := by
  simpa only [Finset.disjoint_singleton_right] using UnionMissingProbability P Q {i}

theorem UnionMarginal {N : ℕ} (P Q : PMF (Finset (Fin N))) (i : Fin N) :
    (UnionLaw P Q).toMeasure.real {W | i∈W}=
      Q.toMeasure.real {V | i∈V}+(1-Q.toMeasure.real {V | i∈V})*P.toMeasure.real {U | i∈U} := by
  have Complement (R : PMF (Finset (Fin N))) :
      R.toMeasure.real {W | i∉W}=1-R.toMeasure.real {W | i∈W} :=
    probReal_compl_eq_one_sub (Set.to_countable _).measurableSet
  have Missing := UnionMissingMarginal P Q i
  simp_rw [Complement] at Missing
  nlinarith

end
end ECTheoryLib.Probability.RandomSubset

namespace ECTheoryLib.Probability.RandomSubset
open MeasureTheory Set
noncomputable section

theorem MembershipIndicatorInUnit {N : ℕ} (i : Fin N) (U : Finset (Fin N)) :
    {W : Finset (Fin N) | i∈W}.indicator (fun _ => (1 : ℝ)) U∈Icc 0 1 := by
  by_cases Inside : i∈U <;> simp [Inside]

theorem MembershipUnionIndicator {N : ℕ} (i : Fin N) (U V : Finset (Fin N)) :
    {W : Finset (Fin N) | i∈W}.indicator (fun _ => (1 : ℝ)) (U∪V)=
      {W : Finset (Fin N) | i∈W}.indicator (fun _ => (1 : ℝ)) U+
      (1-{W : Finset (Fin N) | i∈W}.indicator (fun _ => (1 : ℝ)) U)*
        {W : Finset (Fin N) | i∈W}.indicator (fun _ => (1 : ℝ)) V := by
  by_cases Left : i∈U <;> by_cases Right : i∈V <;> simp [Left,Right]

/-- Independent union preserves the full one-negative-correlation condition.
The proof integrates one actual sample at a time using affine product bounds. -/
theorem UnionOneNegativeCorrelation {N : ℕ} (P Q : PMF (Finset (Fin N)))
    (Left : OneNegativelyCorrelated P.toMeasure (fun i : Fin N => {U | i∈U}))
    (Right : OneNegativelyCorrelated Q.toMeasure (fun i : Fin N => {U | i∈U})) :
    OneNegativelyCorrelated (UnionLaw P Q).toMeasure (fun i : Fin N => {U | i∈U}) := by
  intro A
  let Events := fun i : Fin N => {U : Finset (Fin N) | i∈U}
  have MeasurableEvents (i : Fin N) : MeasurableSet (Events i) := (Set.to_countable _).measurableSet
  have InnerBound (U : Finset (Fin N)) :
      (∫ V, ∏ i∈A, (Events i).indicator (fun _ => (1 : ℝ)) (U∪V) ∂Q.toMeasure)≤
        ∏ i∈A, (Q.toMeasure.real (Events i)+(1-Q.toMeasure.real (Events i))*
          (Events i).indicator (fun _ => (1 : ℝ)) U) := by
    have Bound := OneNegativeCorrelationAffineProduct Q.toMeasure Events MeasurableEvents Right
      (fun i => (Events i).indicator (fun _ => (1 : ℝ)) U)
      (fun i => 1-(Events i).indicator (fun _ => (1 : ℝ)) U)
      (fun i => (MembershipIndicatorInUnit i U).1)
      (fun i => sub_nonneg.mpr (MembershipIndicatorInUnit i U).2) A
    simp only [Events,MembershipUnionIndicator]
    apply Bound.trans_eq
    apply Finset.prod_congr rfl
    intro i _
    ring
  change (UnionLaw P Q).toMeasure.real (⋂ i∈A, Events i)≤∏ i∈A, (UnionLaw P Q).toMeasure.real (Events i)
  rw [← EventIndicatorProductIntegral (UnionLaw P Q).toMeasure Events MeasurableEvents A,UnionIntegral]
  calc
    _ ≤ ∫ U, ∏ i∈A, (Q.toMeasure.real (Events i)+(1-Q.toMeasure.real (Events i))*
        (Events i).indicator (fun _ => (1 : ℝ)) U) ∂P.toMeasure := by
      simp only [PMF.integral_eq_sum,smul_eq_mul]
      apply Finset.sum_le_sum
      intro U _
      have Bound := InnerBound U
      simp only [PMF.integral_eq_sum,smul_eq_mul] at Bound
      exact mul_le_mul_of_nonneg_left Bound ENNReal.toReal_nonneg
    _ ≤ ∏ i∈A, (Q.toMeasure.real (Events i)+(1-Q.toMeasure.real (Events i))*P.toMeasure.real (Events i)) :=
      OneNegativeCorrelationAffineProduct P.toMeasure Events MeasurableEvents Left
        (fun i => Q.toMeasure.real (Events i)) (fun i => 1-Q.toMeasure.real (Events i))
        (fun _ => ENNReal.toReal_nonneg) (fun _ => sub_nonneg.mpr measureReal_le_one) A
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (UnionMarginal P Q i).symm

/-- Independent union also preserves the all-subset zero-negative condition. -/
theorem UnionZeroNegativeCorrelation {N : ℕ} (P Q : PMF (Finset (Fin N)))
    (Left : ZeroNegativelyCorrelated P.toMeasure (fun i : Fin N => {U | i∈U}))
    (Right : ZeroNegativelyCorrelated Q.toMeasure (fun i : Fin N => {U | i∈U})) :
    ZeroNegativelyCorrelated (UnionLaw P Q).toMeasure (fun i : Fin N => {U | i∈U}) := by
  intro A
  have Event : (⋂ i∈A, {U : Finset (Fin N) | i∈U}ᶜ)={U | Disjoint U A} := by
    ext U
    simp only [mem_iInter,mem_compl_iff,mem_ofPred_eq]
    constructor
    · intro Avoid
      exact Finset.disjoint_left.mpr (fun i InU InA => Avoid i InA InU)
    · intro Apart i InA InU
      exact Finset.disjoint_left.mp Apart InU InA
  have LeftBound := Left A
  have RightBound := Right A
  rw [Event] at LeftBound RightBound ⊢
  rw [UnionMissingProbability]
  calc
    _ ≤ (∏ i∈A, P.toMeasure.real {U : Finset (Fin N) | i∈U}ᶜ)*
        (∏ i∈A, Q.toMeasure.real {U : Finset (Fin N) | i∈U}ᶜ) :=
      mul_le_mul LeftBound RightBound ENNReal.toReal_nonneg
        (Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      exact (UnionMissingMarginal P Q i).symm

end
end ECTheoryLib.Probability.RandomSubset

namespace ECTheoryLib.Probability.RandomSubset
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Connect independent PMF union to Mathlib's product measure. -/
theorem UnionMeasure {N : ℕ} (P Q : PMF (Finset (Fin N))) :
    (P.toMeasure.prod Q.toMeasure).map (fun UV => UV.1∪UV.2)=(UnionLaw P Q).toMeasure := by
  ext E MeasurableE
  rw [Measure.map_apply (measurable_of_finite _) MeasurableE,
    Measure.prod_apply (MeasurableE.preimage (measurable_of_finite _)),
    UnionLaw,PMF.toMeasure_bind_apply _ _ _ MeasurableE,lintegral_fintype,tsum_fintype]
  apply Finset.sum_congr rfl
  intro U _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) MeasurableE]
  exact mul_comm _ _

/-- External independent random subsets with the given marginal laws have
the actual union law; independence is an explicit Mathlib premise. -/
theorem IndependentUnionHasLaw {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω)
    [IsProbabilityMeasure M] {N : ℕ} (X Y : Ω → Finset (Fin N))
    (P Q : PMF (Finset (Fin N))) (LawX : HasLaw X P.toMeasure M)
    (LawY : HasLaw Y Q.toMeasure M) (Independent : IndepFun X Y M) :
    HasLaw (fun ω => X ω∪Y ω) (UnionLaw P Q).toMeasure M := by
  have Joint := Independent.hasLaw_prod LawX LawY
  have MapLaw : HasLaw (fun UV : Finset (Fin N)×Finset (Fin N) => UV.1∪UV.2)
      (UnionLaw P Q).toMeasure (P.toMeasure.prod Q.toMeasure) :=
    ⟨(measurable_of_finite _).aemeasurable,UnionMeasure P Q⟩
  exact MapLaw.fun_comp Joint

end
end ECTheoryLib.Probability.RandomSubset

namespace ECTheoryLib.Probability.RandomSubset
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The actual union of a finite ordered family, keeping the empty family. -/
def FamilyUnion {N : ℕ} : {k : ℕ} → (Fin k → Finset (Fin N)) → Finset (Fin N)
  | 0, _ => ∅
  | k+1, U => FamilyUnion (fun i : Fin k => U i.castSucc)∪U (Fin.last k)

/-- The distribution of independent draws with possibly different laws. -/
def FamilyLaw {N : ℕ} : {k : ℕ} → (Fin k → PMF (Finset (Fin N))) → PMF (Finset (Fin N))
  | 0, _ => PMF.pure ∅
  | k+1, P => UnionLaw (FamilyLaw (fun i : Fin k => P i.castSucc)) (P (Fin.last k))

theorem FamilyUnionMembership {N k : ℕ} (U : Fin k → Finset (Fin N)) (i : Fin N) :
    i∈FamilyUnion U ↔ ∃ j, i∈U j := by
  induction k with
  | zero => simp [FamilyUnion]
  | succ k IH =>
    rw [FamilyUnion,Finset.mem_union,IH]
    constructor
    · rintro (⟨j,Member⟩ | Member)
      · exact ⟨j.castSucc,Member⟩
      · exact ⟨Fin.last k,Member⟩
    · rintro ⟨j,Member⟩
      revert Member
      exact Fin.lastCases (fun H => Or.inr H) (fun h H => Or.inl ⟨h,H⟩) j

theorem EmptyOneNegativeCorrelation (N : ℕ) :
    OneNegativelyCorrelated (PMF.pure (∅ : Finset (Fin N))).toMeasure (fun i : Fin N => {U | i∈U}) := by
  intro A
  by_cases Empty : A=∅
  · subst A
    simp
  obtain ⟨i,InA⟩ := Finset.nonempty_iff_ne_empty.mpr Empty
  have Outside : (∅ : Finset (Fin N))∉⋂ j∈A, {U | j∈U} := by
    intro Inside
    have Impossible := Set.mem_iInter.mp (Set.mem_iInter.mp Inside i) InA
    simp at Impossible
  simp [PMF.toMeasure_pure,Measure.real,Outside]

theorem EmptyZeroNegativeCorrelation (N : ℕ) :
    ZeroNegativelyCorrelated (PMF.pure (∅ : Finset (Fin N))).toMeasure (fun i : Fin N => {U | i∈U}) := by
  intro A
  simp [PMF.toMeasure_pure,Measure.real]

theorem FamilyOneNegativeCorrelation {N k : ℕ} (P : Fin k → PMF (Finset (Fin N)))
    (Correlated : ∀ j, OneNegativelyCorrelated (P j).toMeasure (fun i : Fin N => {U | i∈U})) :
    OneNegativelyCorrelated (FamilyLaw P).toMeasure (fun i : Fin N => {U | i∈U}) := by
  induction k with
  | zero => exact EmptyOneNegativeCorrelation N
  | succ k IH => exact UnionOneNegativeCorrelation _ _ (IH _ (fun j => Correlated j.castSucc)) (Correlated (Fin.last k))

theorem FamilyZeroNegativeCorrelation {N k : ℕ} (P : Fin k → PMF (Finset (Fin N)))
    (Correlated : ∀ j, ZeroNegativelyCorrelated (P j).toMeasure (fun i : Fin N => {U | i∈U})) :
    ZeroNegativelyCorrelated (FamilyLaw P).toMeasure (fun i : Fin N => {U | i∈U}) := by
  induction k with
  | zero => exact EmptyZeroNegativeCorrelation N
  | succ k IH => exact UnionZeroNegativeCorrelation _ _ (IH _ (fun j => Correlated j.castSucc)) (Correlated (Fin.last k))

end
end ECTheoryLib.Probability.RandomSubset

namespace ECTheoryLib.Probability.RandomSubset
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Mathlib independence of a tuple and a disjoint coordinate also applies
after forming the actual union of the prefix. -/
theorem PrefixUnionIndependent {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω)
    {N k : ℕ} (X : Fin (k+1) → Ω → Finset (Fin N))
    (MeasurableX : ∀ j, Measurable (X j)) (Independent : iIndepFun X M) :
    IndepFun (fun ω => FamilyUnion (fun i : Fin k => X i.castSucc ω)) (X (Fin.last k)) M := by
  let S : Finset (Fin (k+1)) := Finset.univ.image Fin.castSucc
  have InS (i : Fin k) : i.castSucc∈S := by simp [S]
  have DisjointSets : Disjoint S {Fin.last k} := by
    simp [S,Finset.disjoint_singleton_right]
  have Joint := Independent.indepFun_finset S {Fin.last k} DisjointSets MeasurableX
  let F : (S → Finset (Fin N)) → Finset (Fin N) :=
    fun u => FamilyUnion (fun i : Fin k => u ⟨i.castSucc,InS i⟩)
  have Bound := Joint.comp (measurable_of_finite F)
    (measurable_of_finite (fun u : ({Fin.last k} : Finset (Fin (k+1))) → Finset (Fin N) => u ⟨Fin.last k,by simp⟩))
  exact Bound

/-- Any independent family with specified marginal PMFs has the canonical
union law. This permits use from an arbitrary external probability space. -/
theorem FamilyHasLaw {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω) [IsProbabilityMeasure M]
    {N k : ℕ} (X : Fin k → Ω → Finset (Fin N))
    (P : Fin k → PMF (Finset (Fin N))) (MeasurableX : ∀ j, Measurable (X j))
    (MarginalLaws : ∀ j, HasLaw (X j) (P j).toMeasure M) (Independent : iIndepFun X M) :
    HasLaw (fun ω => FamilyUnion (fun j => X j ω)) (FamilyLaw P).toMeasure M := by
  induction k with
  | zero =>
    simpa only [FamilyUnion,FamilyLaw,PMF.toMeasure_pure] using
      (hasLaw_dirac_of_ae_eq (ae_of_all M (fun _ω => rfl)) :
        HasLaw (fun _ω : Ω => (∅ : Finset (Fin N))) (Measure.dirac ∅) M)
  | succ k IH =>
    have PrefixLaw := IH (fun j => X j.castSucc) (fun j => P j.castSucc)
      (fun j => MeasurableX j.castSucc) (fun j => MarginalLaws j.castSucc)
      (Independent.precomp (Fin.castSucc_injective k))
    exact IndependentUnionHasLaw M _ _ _ _ PrefixLaw (MarginalLaws (Fin.last k))
      (PrefixUnionIndependent M X MeasurableX Independent)

end
end ECTheoryLib.Probability.RandomSubset

namespace ECTheoryLib.Probability.RandomSubset
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem OneNegativeCorrelationOfHasLaw {Ω : Type*} [MeasurableSpace Ω]
    (M : Measure Ω) {N : ℕ} (X : Ω → Finset (Fin N)) (P : PMF (Finset (Fin N)))
    (LawX : HasLaw X P.toMeasure M)
    (Correlated : OneNegativelyCorrelated P.toMeasure (fun i : Fin N => {U | i∈U})) :
    OneNegativelyCorrelated M (fun i : Fin N => {ω | i∈X ω}) := by
  have Transfer (E : Set (Finset (Fin N))) : M.real (X ⁻¹' E)=P.toMeasure.real E :=
    LawX.measureReal_eq (Set.to_countable E).measurableSet
  intro A
  have Bound := Correlated A
  rw [← Transfer] at Bound
  simp_rw [← Transfer] at Bound
  simpa only [Set.preimage_iInter,Set.preimage_ofPred_eq] using Bound

theorem ZeroNegativeCorrelationOfHasLaw {Ω : Type*} [MeasurableSpace Ω]
    (M : Measure Ω) {N : ℕ} (X : Ω → Finset (Fin N)) (P : PMF (Finset (Fin N)))
    (LawX : HasLaw X P.toMeasure M)
    (Correlated : ZeroNegativelyCorrelated P.toMeasure (fun i : Fin N => {U | i∈U})) :
    ZeroNegativelyCorrelated M (fun i : Fin N => {ω | i∈X ω}) := by
  have Transfer (E : Set (Finset (Fin N))) : M.real (X ⁻¹' E)=P.toMeasure.real E :=
    LawX.measureReal_eq (Set.to_countable E).measurableSet
  intro A
  have Bound := Correlated A
  rw [← Transfer] at Bound
  simp_rw [← Transfer] at Bound
  simpa only [Set.preimage_iInter,Set.preimage_compl,Set.preimage_ofPred_eq] using Bound

end
end ECTheoryLib.Probability.RandomSubset

namespace ECTheoryLib.Probability.RandomSubset
open MeasureTheory Set
noncomputable section

theorem UnionLawComm {N : ℕ} (P Q : PMF (Finset (Fin N))) : UnionLaw P Q=UnionLaw Q P := by
  unfold UnionLaw PMF.map
  rw [PMF.bind_comm]
  congr 1
  funext V
  congr 1
  funext U
  simp only [Function.comp_apply,Finset.union_comm]

/-- The exact joint avoidance probability of the actual independent family. -/
theorem FamilyMissingProbability {N k : ℕ} (P : Fin k → PMF (Finset (Fin N))) (A : Finset (Fin N)) :
    (FamilyLaw P).toMeasure.real {U | Disjoint U A}=∏ j, (P j).toMeasure.real {U | Disjoint U A} := by
  induction k with
  | zero => simp [FamilyLaw,PMF.toMeasure_pure,Measure.real]
  | succ k IH => rw [FamilyLaw,UnionMissingProbability,IH,Fin.prod_univ_castSucc]

theorem FamilyMissingMarginal {N k : ℕ} (P : Fin k → PMF (Finset (Fin N))) (i : Fin N) :
    (FamilyLaw P).toMeasure.real {U | i∉U}=∏ j, (P j).toMeasure.real {U | i∉U} := by
  simpa only [Finset.disjoint_singleton_right] using FamilyMissingProbability P {i}

theorem FamilyMarginal {N k : ℕ} (P : Fin k → PMF (Finset (Fin N))) (i : Fin N) :
    (FamilyLaw P).toMeasure.real {U | i∈U}=1-∏ j, (1-(P j).toMeasure.real {U | i∈U}) := by
  have Complement (R : PMF (Finset (Fin N))) :
      R.toMeasure.real {U | i∉U}=1-R.toMeasure.real {U | i∈U} :=
    probReal_compl_eq_one_sub (Set.to_countable _).measurableSet
  have Missing := FamilyMissingMarginal P i
  simp_rw [Complement] at Missing
  linarith

theorem CardAsIndicatorSum {N : ℕ} (U : Finset (Fin N)) :
    (U.card : ℝ)=∑ i : Fin N, {V : Finset (Fin N) | i∈V}.indicator (fun _ => (1 : ℝ)) U := by
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  simp

end
end ECTheoryLib.Probability.RandomSubset
