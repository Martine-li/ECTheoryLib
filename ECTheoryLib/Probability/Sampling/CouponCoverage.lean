import ECTheoryLib.Probability.Sampling.CouponCollector
import ECTheoryLib.Probability.Processes.PathMarginal
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Actual coupon-coverage recurrences and negative correlation

Uniform singleton draws with replacement. Both zero- and one-negative
correlation follow from exact finite-step PMF recurrences. This is the
singleton-draw specialization of Doerr Lemma 1.10.26, not its arbitrary
fixed-size subset model. Current coverage is connected to hitting events
only after proving persistence of the record.
-/

namespace ECTheoryLib.Probability.CouponCollector
open MeasureTheory
noncomputable section

/-- All members of a specified finite collection have appeared. -/
def Covers {n : ℕ} (A : Finset (Fin n)) (x : State n) : Prop := ∀ i∈A, x i=true

theorem CoversCollect {n : ℕ} (A : Finset (Fin n)) (x : State n) (i : Fin n) :
    Covers A (Collect x i) ↔ Covers (A.erase i) x := by
  constructor
  · intro Before j InErase
    obtain ⟨Different,InA⟩ := Finset.mem_erase.mp InErase
    have Seen := Before j InA
    rwa [CollectAway x i j Different] at Seen
  · intro Before j InA
    by_cases Equal : j=i
    · subst j
      exact CollectAt x i
    · rw [CollectAway x i j Equal]
      exact Before j (Finset.mem_erase.mpr ⟨Equal,InA⟩)

def CoverageProbability (n : ℕ) (A : Finset (Fin n)) (t : ℕ) : ℝ :=
  (Evolve (Step n) (PMF.pure (Empty n)) t).toMeasure.real {x | Covers A x}

theorem CoverageProbabilityIntegral (n : ℕ) (A : Finset (Fin n)) (t : ℕ) :
    CoverageProbability n A t=
      ∫ x, {y | Covers A y}.indicator (fun _ => (1 : ℝ)) x
        ∂(Evolve (Step n) (PMF.pure (Empty n)) t).toMeasure := by
  rw [integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
  rfl

theorem StepIntegral {n : ℕ} (Positive : 0<n) (x : State n) (f : State n → ℝ) :
    (∫ y, f y ∂(Step n x).toMeasure)=(n : ℝ)⁻¹*∑ i : Fin n, f (Collect x i) := by
  let : Nonempty (Fin n) := ⟨⟨0,Positive⟩⟩
  unfold Step
  rw [dif_pos Positive,PMFIntegralMap,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,smul_eq_mul,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,Fintype.card_fin,Finset.mul_sum]

/-- A last draw erases at most its own coupon from the required collection.
This exact recurrence uses the actual iterated transition PMF. -/
theorem CoverageProbabilitySucc {n : ℕ} (Positive : 0<n) (A : Finset (Fin n)) (t : ℕ) :
    CoverageProbability n A (t+1)=(n : ℝ)⁻¹*∑ i : Fin n, CoverageProbability n (A.erase i) t := by
  classical
  rw [CoverageProbabilityIntegral,Evolve,PMFIntegralBind]
  simp_rw [StepIntegral Positive]
  have Indicator (x : State n) (i : Fin n) :
      {y | Covers A y}.indicator (fun _ => (1 : ℝ)) (Collect x i)=
        {y | Covers (A.erase i) y}.indicator (fun _ => (1 : ℝ)) x := by
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,CoversCollect]
  simp_rw [Indicator,CoverageProbabilityIntegral,PMF.integral_eq_sum,smul_eq_mul]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem CoversEmptyIff {n : ℕ} (A : Finset (Fin n)) : Covers A (Empty n) ↔ A=∅ := by
  constructor
  · intro Covered
    apply Finset.eq_empty_of_forall_notMem
    intro i InA
    have Impossible := Covered i InA
    simp [Empty] at Impossible
  · rintro rfl
    simp [Covers]

theorem CoverageProbabilityZero (n : ℕ) (A : Finset (Fin n)) :
    CoverageProbability n A 0=if A=∅ then 1 else 0 := by
  classical
  rw [CoverageProbabilityIntegral]
  rw [Evolve,PMF.toMeasure_pure,integral_dirac]
  change (if Covers A (Empty n) then (1 : ℝ) else 0)=_
  rw [CoversEmptyIff]
  split_ifs <;> rfl

theorem SumErasePowers {n : ℕ} (A : Finset (Fin n)) (a : ℝ) :
    (∑ i : Fin n, a^(A.erase i).card)=
      ((n-A.card : ℕ) : ℝ)*a^A.card+(A.card : ℝ)*a^(A.card-1) := by
  classical
  have Each (i : Fin n) : a^(A.erase i).card=if i∈A then a^(A.card-1) else a^A.card := by
    by_cases InA : i∈A
    · simp [InA,Finset.card_erase_of_mem InA]
    · simp [InA]
  simp_rw [Each]
  rw [Finset.sum_ite]
  have PositiveFilter : Finset.univ.filter (fun i : Fin n => i∈A)=A := by ext i; simp
  have NegativeFilter : Finset.univ.filter (fun i : Fin n => i∉A)=Aᶜ := by ext i; simp
  rw [PositiveFilter,NegativeFilter]
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_compl,Fintype.card_fin]
  ring

/-- Joint coverage is at most the product of the identical one-coupon
coverage probabilities. No independence between coupon types is used. -/
theorem CoverageProbabilityUpper {n : ℕ} (Positive : 0<n) (A : Finset (Fin n)) (t : ℕ) :
    CoverageProbability n A t≤(1-(1-1/(n : ℝ))^t)^A.card := by
  classical
  induction t generalizing A with
  | zero =>
    rw [CoverageProbabilityZero]
    by_cases EmptySet : A=∅
    · simp [EmptySet]
    · have CardPositive : 0<A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr EmptySet)
      simp [EmptySet,CardPositive.ne']
  | succ t Before =>
    let a : ℝ := 1-(1-1/(n : ℝ))^t
    have NPositive : (0 : ℝ)<n := Nat.cast_pos.mpr Positive
    have CoefficientNonnegative : 0≤1-1/(n : ℝ) := by
      have Small : 1/(n : ℝ)≤1 := by
        simpa using one_div_le_one_div_of_le (show (0 : ℝ)<1 by norm_num) (Nat.one_le_cast.mpr Positive)
      linarith
    have CoefficientAtMostOne : 1-1/(n : ℝ)≤1 := by
      have := (one_div_pos.mpr NPositive).le
      linarith
    have ANonnegative : 0≤a := sub_nonneg.mpr (pow_le_one₀ CoefficientNonnegative CoefficientAtMostOne)
    have AAtMostOne : a≤1 := by
      dsimp [a]
      have := pow_nonneg CoefficientNonnegative t
      linarith
    have OneStep : a+(1-a)/(n : ℝ)=1-(1-1/(n : ℝ))^(t+1) := by
      dsimp [a]
      rw [pow_succ]
      ring
    rw [CoverageProbabilitySucc Positive]
    calc
      (n : ℝ)⁻¹*∑ i : Fin n, CoverageProbability n (A.erase i) t≤
          (n : ℝ)⁻¹*∑ i : Fin n, a^(A.erase i).card :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => Before (A.erase i))) (inv_nonneg.mpr NPositive.le)
      _≤(a+(1-a)/(n : ℝ))^A.card := by
        rw [SumErasePowers]
        have Size : A.card≤n := by simpa using Finset.card_le_univ A
        rw [Nat.cast_sub Size]
        by_cases CardZero : A.card=0
        · simp [CardZero,NPositive.ne']
        · have PowerStep : a^A.card=a^(A.card-1)*a := by
            conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr CardZero),pow_succ]
          have Bernoulli := pow_add_mul_le_add_pow ANonnegative
            (show 0≤2*a+(1-a)/(n : ℝ) by positivity) A.card
          have Algebra : (n : ℝ)⁻¹*((n-A.card)*a^A.card+A.card*a^(A.card-1))=
              a^A.card+A.card*a^(A.card-1)*((1-a)/(n : ℝ)) := by
            rw [PowerStep]
            field_simp
            ring
          rw [Algebra]
          exact Bernoulli
      _=(1-(1-1/(n : ℝ))^(t+1))^A.card := by rw [OneStep]

/-- An already seen coupon is never lost by a draw. -/
theorem StepPreservesSeen {n : ℕ} (Positive : 0<n) (x : State n) :
    ∀ᵐ y ∂(Step n x).toMeasure, ∀ i, x i=true → y i=true := by
  let : Nonempty (Fin n) := ⟨⟨0,Positive⟩⟩
  let D := PMF.uniformOfFintype (Fin n)
  have Law : (Step n x).toMeasure=D.toMeasure.map (Collect x) := by
    unfold Step
    rw [dif_pos Positive]
    exact (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm
  rw [Law]
  have Range : ∀ᵐ y ∂D.toMeasure.map (Collect x), y∈Set.range (Collect x) :=
    ae_map_mem_range _ (Set.to_countable _).measurableSet _
  filter_upwards [Range] with y InRange
  obtain ⟨j,rfl⟩ := InRange
  intro i Seen
  by_cases Equal : i=j
  · subst i
    exact CollectAt x j
  · rwa [CollectAway x j i Equal]

theorem CompleteAtTimeIffHit {n : ℕ} (Positive : 0<n) (Initial : PMF (State n)) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure (Step n) Initial,
      FirstHittingTime Complete Path≤(t : WithTop ℕ) ↔ Complete (Path t) := by
  have Follows : ∀ᵐ Path ∂PathMeasure (Step n) Initial,
      ∀ j, ∀ i, Path j i=true → Path (j+1) i=true :=
    ae_all_iff.mpr (fun j => PathMeasureFollowsTransition (Step n) Initial
      (fun x y => ∀ i, x i=true → y i=true) (StepPreservesSeen Positive) j)
  filter_upwards [Follows] with Path Preserves
  rw [FirstHittingTimeLeIff]
  constructor
  · rintro ⟨j,Before,AllSeen⟩
    induction t,Before using Nat.le_induction with
    | base => exact AllSeen
    | succ t _ Previous => exact fun i => Preserves t i (Previous i)
  · intro AllSeen
    exact ⟨t,le_rfl,AllSeen⟩

/-- The lower-tail event is identified with the actual current record;
this step uses monotone collection, not merely matching marginals. -/
theorem CompleteRuntimeProbability {n : ℕ} (Positive : 0<n) (t : ℕ) :
    (PathMeasure (Step n) (PMF.pure (Empty n))).real
      {Path | FirstHittingTime Complete Path≤(t : WithTop ℕ)}=
        CoverageProbability n Finset.univ t := by
  have Events : {Path | FirstHittingTime Complete Path≤(t : WithTop ℕ)}=ᵐ[PathMeasure (Step n) (PMF.pure (Empty n))]
      {Path | Complete (Path t)} := by
    filter_upwards [CompleteAtTimeIffHit Positive (PMF.pure (Empty n)) t] with Path Eq
    exact propext Eq
  unfold Measure.real
  rw [measure_congr Events]
  have Marginal : (PathMeasure (Step n) (PMF.pure (Empty n))) {Path | Complete (Path t)}=
      (Evolve (Step n) (PMF.pure (Empty n)) t).toMeasure {x | Complete x} :=
    PathMeasureCoordinateEvent (Step n) (PMF.pure (Empty n)) t {x | Complete x}
  rw [Marginal]
  change _=ENNReal.toReal ((Evolve (Step n) (PMF.pure (Empty n)) t).toMeasure {x | Covers Finset.univ x})
  congr 2
  ext x
  simp [Covers,Complete]

theorem EmptySetCoverageProbability (n t : ℕ) : CoverageProbability n ∅ t=1 := by
  simp [CoverageProbability,Covers,Measure.real]

/-- The marginal probability for one specified coupon is exact. -/
theorem SingletonCoverageProbability {n : ℕ} (Positive : 0<n) (j : Fin n) (t : ℕ) :
    CoverageProbability n {j} t=1-(1-1/(n : ℝ))^t := by
  classical
  induction t with
  | zero => simp [CoverageProbabilityZero]
  | succ t Before =>
    rw [CoverageProbabilitySucc Positive]
    have Each (i : Fin n) : CoverageProbability n (({j} : Finset (Fin n)).erase i) t=
        if i=j then 1 else CoverageProbability n {j} t := by
      by_cases Equal : i=j
      · subst i
        simp [EmptySetCoverageProbability]
      · simp [Equal]
    simp_rw [Each]
    rw [Finset.sum_ite]
    have PositiveFilter : Finset.univ.filter (fun i : Fin n => i=j)={j} := by ext i; simp
    have NegativeFilter : Finset.univ.filter (fun i : Fin n => i≠j)=Finset.univ.erase j := by ext i; simp
    rw [PositiveFilter,NegativeFilter]
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_singleton,Nat.cast_one,mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,Fintype.card_fin]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Positive.ne'),Nat.cast_one,Before,pow_succ]
    have NNonzero : (n : ℝ)≠0 := (Nat.cast_pos.mpr Positive).ne'
    field_simp
    ring

/-- One-negative correlation for uniform singleton draws, expressed using
the actual finite-step marginals rather than independent reference coins. -/
theorem CoverageOneNegativeCorrelation {n : ℕ} (Positive : 0<n) (A : Finset (Fin n)) (t : ℕ) :
    CoverageProbability n A t≤∏ i∈A, CoverageProbability n {i} t := by
  simp_rw [SingletonCoverageProbability Positive]
  rw [Finset.prod_const]
  exact CoverageProbabilityUpper Positive A t

end
end ECTheoryLib.Probability.CouponCollector

namespace ECTheoryLib.Probability.CouponCollector
open MeasureTheory
noncomputable section

/-- No member of the specified finite collection has appeared. -/
def Misses {n : ℕ} (A : Finset (Fin n)) (x : State n) : Prop := ∀ i∈A, x i=false

theorem MissesCollect {n : ℕ} (A : Finset (Fin n)) (x : State n) (i : Fin n) :
    Misses A (Collect x i) ↔ i∉A ∧ Misses A x := by
  constructor
  · intro After
    have Outside : i∉A := by
      intro InA
      have Contradiction := After i InA
      rw [CollectAt] at Contradiction
      cases Contradiction
    refine ⟨Outside,?_⟩
    intro j InA
    have Different : j≠i := by intro Equal; subst j; exact Outside InA
    have NotSeen := After j InA
    rwa [CollectAway x i j Different] at NotSeen
  · rintro ⟨Outside,Before⟩ j InA
    have Different : j≠i := by intro Equal; subst j; exact Outside InA
    rw [CollectAway x i j Different]
    exact Before j InA

def MissingSetProbability (n : ℕ) (A : Finset (Fin n)) (t : ℕ) : ℝ :=
  (Evolve (Step n) (PMF.pure (Empty n)) t).toMeasure.real {x | Misses A x}

theorem MissingSetProbabilityIntegral (n : ℕ) (A : Finset (Fin n)) (t : ℕ) :
    MissingSetProbability n A t=
      ∫ x, {y | Misses A y}.indicator (fun _ => (1 : ℝ)) x
        ∂(Evolve (Step n) (PMF.pure (Empty n)) t).toMeasure := by
  rw [integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
  rfl

theorem MissingSetStepIntegral {n : ℕ} (Positive : 0<n) (A : Finset (Fin n)) (x : State n) :
    (∫ y, {z | Misses A z}.indicator (fun _ => (1 : ℝ)) y ∂(Step n x).toMeasure)=
      (1-(A.card : ℝ)/(n : ℝ))*{z | Misses A z}.indicator (fun _ => (1 : ℝ)) x := by
  classical
  rw [StepIntegral Positive]
  have Each (i : Fin n) : {z | Misses A z}.indicator (fun _ => (1 : ℝ)) (Collect x i)=
      if i∈A then 0 else {z | Misses A z}.indicator (fun _ => (1 : ℝ)) x := by
    by_cases InA : i∈A <;> simp [Set.indicator_apply,MissesCollect,InA]
  simp_rw [Each]
  rw [Finset.sum_ite]
  have NegativeFilter : Finset.univ.filter (fun i : Fin n => i∉A)=Aᶜ := by ext i; simp
  rw [NegativeFilter]
  simp only [Finset.sum_const_zero,zero_add,Finset.sum_const,nsmul_eq_mul,
    Finset.card_compl,Fintype.card_fin]
  have Size : A.card≤n := by simpa using Finset.card_le_univ A
  rw [Nat.cast_sub Size]
  have NNonzero : (n : ℝ)≠0 := (Nat.cast_pos.mpr Positive).ne'
  field_simp

theorem MissingSetProbabilitySucc {n : ℕ} (Positive : 0<n) (A : Finset (Fin n)) (t : ℕ) :
    MissingSetProbability n A (t+1)=
      (1-(A.card : ℝ)/(n : ℝ))*MissingSetProbability n A t := by
  rw [MissingSetProbabilityIntegral,Evolve,PMFIntegralBind]
  simp_rw [MissingSetStepIntegral Positive]
  rw [MissingSetProbabilityIntegral,PMF.integral_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [smul_eq_mul]
  ring

/-- Avoiding an entire specified set has an exact probability, including
the empty and full sets and time zero. -/
theorem MissingSetProbabilityExact {n : ℕ} (Positive : 0<n) (A : Finset (Fin n)) (t : ℕ) :
    MissingSetProbability n A t=(1-(A.card : ℝ)/(n : ℝ))^t := by
  induction t with
  | zero =>
    rw [MissingSetProbabilityIntegral,Evolve,PMF.toMeasure_pure,integral_dirac]
    simp [Set.indicator_apply,Misses,Empty]
  | succ t Before =>
    rw [MissingSetProbabilitySucc Positive,Before,pow_succ]
    ring

/-- Zero-negative correlation for uniform singleton draws. The Bernoulli
comparison is imported from Mathlib. -/
theorem CoverageZeroNegativeCorrelation {n : ℕ} (Positive : 0<n) (A : Finset (Fin n)) (t : ℕ) :
    MissingSetProbability n A t≤∏ i∈A, MissingSetProbability n {i} t := by
  simp_rw [MissingSetProbabilityExact Positive,Finset.card_singleton,Nat.cast_one]
  rw [Finset.prod_const]
  have NPositive : (0 : ℝ)<n := Nat.cast_pos.mpr Positive
  have Size : (A.card : ℝ)≤n := by exact_mod_cast (show A.card≤n by simpa using Finset.card_le_univ A)
  have BaseNonnegative : 0≤1-(A.card : ℝ)/(n : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one NPositive).mpr Size
  have Bernoulli : 1-(A.card : ℝ)/(n : ℝ)≤(1-1/(n : ℝ))^A.card := by
    have Reciprocal : 1/(n : ℝ)≤1 := (div_le_one NPositive).mpr (Nat.one_le_cast.mpr Positive)
    have Bound := one_add_mul_le_pow (show (-2 : ℝ)≤ -1/(n : ℝ) by rw [neg_div]; linarith) A.card
    calc
      1-(A.card : ℝ)/(n : ℝ)=1+(A.card : ℝ)*(-1/(n : ℝ)) := by ring
      _≤(1+(-1/(n : ℝ)))^A.card := Bound
      _=(1-1/(n : ℝ))^A.card := by congr 1; ring
  have Powered := pow_le_pow_left₀ BaseNonnegative Bernoulli t
  rw [← pow_mul,Nat.mul_comm A.card t] at Powered
  rw [← pow_mul]
  exact Powered

end
end ECTheoryLib.Probability.CouponCollector
