import ECTheoryLib.Tools.Drift.ExponentialLowerTail
import ECTheoryLib.Probability.HittingTimes.StoppedHitting
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# General-target exponential lower tails

Corrected counterparts of book Theorem 2.4.8(b) and Lehre-Witt Theorem 2(iv).
Full-history moments are bounded above. A target-side potential comparison
controls overshoots. Stopping retains the original first hit even when the
original process subsequently leaves the target. Arbitrary time-dependent
nonnegative beta is handled by a sum of prefix products; the single-product
form requires beta at least one. No original absorption is assumed.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Average the next exponential only on paths surviving to the current time.
The conditioning is on the original full history, including the hitting step. -/
theorem ActiveExponentialLowerExpectedStepOfCondExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a Lambda beta : ℝ) (g : ℝ → ℝ)
    (Values : ∀ j ω, X j ω ∈ S) (j : ℕ)
    (Moment : ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * (g (X j u) - g (X (j + 1) u))) | F j]) ω ≤ beta) :
    (∫ ω, ({u | a < StopAtFirstHit (fun s : ℝ => s ≤ a) X j u}).indicator
      (fun u => Real.exp (-Lambda * (g (X (j + 1) u) - g a))) ω ∂μ) ≤
      beta * (∫ ω, KilledExponentialPotential a (-Lambda) g
        (StopAtFirstHit (fun s : ℝ => s ≤ a) X j ω) ∂μ) := by
  classical
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  let A := {ω | a < Y j ω}
  let W := fun s => Real.exp (-Lambda * (g s - g a))
  let G := fun ω => KilledExponentialPotential a (-Lambda) g (Y j ω)
  let R := fun ω => Real.exp (Lambda * (g (X j ω) - g (X (j + 1) ω)))
  let H := A.indicator (fun ω => W (X (j + 1) ω))
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ i ω, Y i ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have EventF : MeasurableSet[F j] A := measurableSet_lt measurable_const (AdaptedY j)
  have Event : MeasurableSet A := F.le j _ EventF
  have GMeasurable : Measurable[F j] G :=
    @FiniteStateCompositionMeasurable Ω (F j) (Y j) S (KilledExponentialPotential a (-Lambda) g)
      (AdaptedY j) (YValues j)
  have GIntegrable : Integrable G μ := FiniteStateCompositionIntegrable μ (Y j) S
    (KilledExponentialPotential a (-Lambda) g) AdaptedY.measurable (YValues j)
  have HIntegrable : Integrable H μ := (FiniteStateCompositionIntegrable μ (X (j + 1)) S
    W AdaptedX.measurable (Values (j + 1))).indicator Event
  let D := fun ω => g (X j ω) - g (X (j + 1) ω)
  let V := (S.product S).image (fun p => g p.1 - g p.2)
  have DMeasurable : Measurable D :=
    (FiniteStateCompositionMeasurable (X j) S g AdaptedX.measurable (Values j)).sub
      (FiniteStateCompositionMeasurable (X (j + 1)) S g AdaptedX.measurable (Values (j + 1)))
  have DValues (ω : Ω) : D ω ∈ V := Finset.mem_image.mpr
    ⟨(X j ω, X (j + 1) ω), Finset.mem_product.mpr ⟨Values j ω, Values (j + 1) ω⟩, rfl⟩
  have RIntegrable : Integrable R μ :=
    FiniteStateCompositionIntegrable μ D V (fun z => Real.exp (Lambda * z)) DMeasurable DValues
  have Factor : H = G * R := by
    funext ω
    by_cases Active : ω ∈ A
    · have Above : a < Y j ω := Active
      have Equal := (StopAtFirstHitStepBefore (fun s : ℝ => s ≤ a) X j ω
        (not_le_of_gt Above)).1
      change Y j ω = X j ω at Equal
      change A.indicator (fun u => W (X (j + 1) u)) ω = G ω * R ω
      rw [Set.indicator_of_mem Active]
      dsimp [G, R, W, KilledExponentialPotential]
      rw [if_neg (not_le_of_gt Above), Equal, ← Real.exp_add]
      congr 1
      ring
    · have NotAbove : ¬a < Y j ω := Active
      change H ω = G ω * R ω
      rw [show H ω = 0 from Set.indicator_of_notMem Active _]
      dsimp [G, KilledExponentialPotential]
      rw [if_pos (le_of_not_gt NotAbove), zero_mul]
  have ProductIntegrable : Integrable (G * R) μ := by rwa [← Factor]
  have Pull := condExp_mul_of_stronglyMeasurable_left GMeasurable.stronglyMeasurable
    ProductIntegrable RIntegrable
  have ConditionalBound : (μ[H | F j]) ≤ᵐ[μ] (fun ω => beta * G ω) := by
    have Equal := condExp_congr_ae (m := F j) (ae_of_all μ (congrFun Factor))
    filter_upwards [Equal, Pull, Moment] with ω Equal Pull Moment
    rw [Equal, Pull]
    change G ω * (μ[R | F j]) ω ≤ beta * G ω
    by_cases Above : a < Y j ω
    · have Same := (StopAtFirstHitStepBefore (fun s : ℝ => s ≤ a) X j ω
        (not_le_of_gt Above)).1
      have Active : a < X j ω := by rwa [← Same]
      exact (mul_le_mul_of_nonneg_left (Moment Active)
        (KilledExponentialNonnegative a (-Lambda) g (Y j ω))).trans_eq (mul_comm _ _)
    · have Zero : G ω = 0 := if_pos (le_of_not_gt Above)
      rw [Zero, zero_mul, mul_zero]
  have Integrated := integral_mono_ae (integrable_condExp (f := H))
    (GIntegrable.const_mul beta) ConditionalBound
  rw [integral_condExp (F.le j), integral_const_mul] at Integrated
  exact Integrated

/-- The surviving negative-exponential potential contracts by the arbitrary
nonnegative time-dependent moment bounds. No target-side comparison is used. -/
theorem KilledExponentialLowerExpectationBoundOfCondExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a Lambda : ℝ) (g : ℝ → ℝ)
    (beta : ℕ → ℝ) (Values : ∀ j ω, X j ω ∈ S)
    (NonnegativeBeta : ∀ j, 0 ≤ beta j)
    (Moment : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * (g (X j u) - g (X (j + 1) u))) | F j]) ω ≤ beta j)
    (t : ℕ) :
    (∫ ω, KilledExponentialPotential a (-Lambda) g
      (StopAtFirstHit (fun s : ℝ => s ≤ a) X t ω) ∂μ) ≤
      (∏ j ∈ Finset.range t, beta j) *
        (∫ ω, KilledExponentialPotential a (-Lambda) g (X 0 ω) ∂μ) := by
  classical
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  let K := KilledExponentialPotential a (-Lambda) g
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have IntegrableK (j : ℕ) : Integrable (fun ω => K (Y j ω)) μ :=
    FiniteStateCompositionIntegrable μ (Y j) S K AdaptedY.measurable (YValues j)
  have Step (j : ℕ) : (∫ ω, K (Y (j + 1) ω) ∂μ) ≤
      beta j * (∫ ω, K (Y j ω) ∂μ) := by
    let A := {ω | a < Y j ω}
    let H := A.indicator (fun ω => Real.exp (-Lambda * (g (X (j + 1) ω) - g a)))
    have Event : MeasurableSet A := F.le j _ (measurableSet_lt measurable_const (AdaptedY j))
    have HIntegrable : Integrable H μ := (FiniteStateCompositionIntegrable μ (X (j + 1)) S
      (fun s => Real.exp (-Lambda * (g s - g a))) AdaptedX.measurable (Values (j + 1))).indicator Event
    have Pointwise (ω : Ω) : K (Y (j + 1) ω) ≤ H ω := by
      by_cases Active : ω ∈ A
      · have Above : a < Y j ω := Active
        have Same := (StopAtFirstHitStepBefore (fun s : ℝ => s ≤ a) X j ω
          (not_le_of_gt Above)).2
        change Y (j + 1) ω = X (j + 1) ω at Same
        change K (Y (j + 1) ω) ≤ A.indicator _ ω
        rw [Set.indicator_of_mem Active, Same]
        dsimp [K, KilledExponentialPotential]
        split
        · exact (Real.exp_pos _).le
        · exact le_rfl
      · have AtTarget : Y j ω ≤ a := le_of_not_gt Active
        have Next := StopAtFirstHitAbsorbing (fun s : ℝ => s ≤ a) X j ω AtTarget
        change K (Y (j + 1) ω) ≤ A.indicator _ ω
        rw [Set.indicator_of_notMem Active]
        exact le_of_eq (if_pos Next)
    exact (integral_mono (IntegrableK (j + 1)) HIntegrable Pointwise).trans
      (ActiveExponentialLowerExpectedStepOfCondExp μ X F AdaptedX S a Lambda (beta j) g Values j (Moment j))
  induction t with
  | zero => simp only [Finset.range_zero, Finset.prod_empty, one_mul, StopAtFirstHitInitial, le_refl]
  | succ t Before =>
    calc
      _ ≤ beta t * (∫ ω, K (Y t ω) ∂μ) := Step t
      _ ≤ beta t * ((∏ j ∈ Finset.range t, beta j) * (∫ ω, K (X 0 ω) ∂μ)) :=
        mul_le_mul_of_nonneg_left Before (NonnegativeBeta t)
      _ = _ := by rw [Finset.prod_range_succ]; ring

/-- General-target early-hit bound with a sum of prefix products. The original
process may leave the target. The target-side comparison includes overshoots;
the beta values may be below one. This is an unconditional probability bound. -/
theorem ExponentialDriftLowerTailSumOfCondExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a Lambda : ℝ) (g : ℝ → ℝ)
    (beta : ℕ → ℝ) (Values : ∀ j ω, X j ω ∈ S)
    (NonnegativeLambda : 0 ≤ Lambda) (NonnegativeBeta : ∀ j, 0 ≤ beta j)
    (PotentialBelow : ∀ s ∈ S, s ≤ a → g s ≤ g a)
    (InitiallyAbove : ∀ᵐ ω ∂μ, a < X 0 ω)
    (Moment : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * (g (X j u) - g (X (j + 1) u))) | F j]) ω ≤ beta j)
    (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal (∑ j ∈ Finset.range t, (∏ r ∈ Finset.range (j + 1), beta r) *
        (∫ ω, Real.exp (-Lambda * (g (X 0 ω) - g a)) ∂μ)) := by
  classical
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  let K := KilledExponentialPotential a (-Lambda) g
  let I := ∫ ω, Real.exp (-Lambda * (g (X 0 ω) - g a)) ∂μ
  let P := fun j => ∏ r ∈ Finset.range j, beta r
  let B := fun j => {ω | Y j ω ≤ a}
  let L := fun j => {ω | a < Y j ω ∧ Y (j + 1) ω ≤ a}
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have NonnegativeI : 0 ≤ I := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have NonnegativeP (j : ℕ) : 0 ≤ P j := Finset.prod_nonneg (fun r _ => NonnegativeBeta r)
  have InitialIntegral : (∫ ω, K (X 0 ω) ∂μ) = I := by
    apply integral_congr_ae
    filter_upwards [InitiallyAbove] with ω Above
    exact if_neg (not_le_of_gt Above)
  have Decay (j : ℕ) : (∫ ω, K (Y j ω) ∂μ) ≤ P j * I := by
    have Bound := KilledExponentialLowerExpectationBoundOfCondExp μ X F AdaptedX S a Lambda g beta
      Values NonnegativeBeta Moment j
    rwa [InitialIntegral] at Bound
  have Layer (j : ℕ) : μ (L j) ≤ ENNReal.ofReal (P (j + 1) * I) := by
    let A := {ω | a < Y j ω}
    let H := A.indicator (fun ω => Real.exp (-Lambda * (g (X (j + 1) ω) - g a)))
    have Event : MeasurableSet A := F.le j _ (measurableSet_lt measurable_const (AdaptedY j))
    have HIntegrable : Integrable H μ := (FiniteStateCompositionIntegrable μ (X (j + 1)) S
      (fun s => Real.exp (-Lambda * (g s - g a))) AdaptedX.measurable (Values (j + 1))).indicator Event
    have HNonnegative (ω : Ω) : 0 ≤ H ω := by
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) ω
    have Markov := HIntegrable.measure_le_integral (ae_of_all μ HNonnegative)
      (s := L j) (by
        intro ω InLayer
        obtain ⟨Above, Next⟩ := InLayer
        have Same := (StopAtFirstHitStepBefore (fun s : ℝ => s ≤ a) X j ω
          (not_le_of_gt Above)).2
        change Y (j + 1) ω = X (j + 1) ω at Same
        rw [Same] at Next
        change 1 ≤ A.indicator _ ω
        rw [Set.indicator_of_mem (show ω ∈ A from Above)]
        apply Real.one_le_exp_iff.mpr
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr NonnegativeLambda)
          (sub_nonpos.mpr (PotentialBelow _ (Values (j + 1) ω) Next)))
    have Active := ActiveExponentialLowerExpectedStepOfCondExp μ X F AdaptedX S a Lambda
      (beta j) g Values j (Moment j)
    have IntegralBound : (∫ ω, H ω ∂μ) ≤ P (j + 1) * I := by
      calc
        _ ≤ beta j * (∫ ω, K (Y j ω) ∂μ) := Active
        _ ≤ beta j * (P j * I) := mul_le_mul_of_nonneg_left (Decay j) (NonnegativeBeta j)
        _ = _ := by dsimp [P]; rw [Finset.prod_range_succ]; ring
    exact Markov.trans (ENNReal.ofReal_le_ofReal IntegralBound)
  have Null : μ (B 0) = 0 := by
    have Equal : B 0 =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [InitiallyAbove] with ω Above
      change (Y 0 ω ≤ a) = False
      apply propext
      rw [show Y 0 ω = X 0 ω from StopAtFirstHitInitial _ X ω]
      exact ⟨not_le_of_gt Above, False.elim⟩
    rw [measure_congr Equal, measure_empty]
  have Cumulative (n : ℕ) : μ (B n) ≤ ENNReal.ofReal (∑ j ∈ Finset.range n, P (j + 1) * I) := by
    induction n with
    | zero => simp only [Null, Finset.range_zero, Finset.sum_empty, ENNReal.ofReal_zero, le_refl]
    | succ n Before =>
      have Subset : B (n + 1) ⊆ B n ∪ L n := by
        intro ω Next
        by_cases Current : ω ∈ B n
        · exact Or.inl Current
        · exact Or.inr ⟨lt_of_not_ge Current, Next⟩
      have TermNonnegative : 0 ≤ P (n + 1) * I := mul_nonneg (NonnegativeP _) NonnegativeI
      have SumNonnegative : 0 ≤ ∑ j ∈ Finset.range n, P (j + 1) * I :=
        Finset.sum_nonneg (fun _ _ => mul_nonneg (NonnegativeP _) NonnegativeI)
      calc
        _ ≤ μ (B n ∪ L n) := measure_mono Subset
        _ ≤ μ (B n) + μ (L n) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (∑ j ∈ Finset.range n, P (j + 1) * I) +
            ENNReal.ofReal (P (n + 1) * I) := add_le_add Before (Layer n)
        _ = ENNReal.ofReal ((∑ j ∈ Finset.range n, P (j + 1) * I) + P (n + 1) * I) :=
          (ENNReal.ofReal_add SumNonnegative TermNonnegative).symm
        _ = _ := by rw [Finset.sum_range_succ]
  have Equal : {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)} = B t := by
    ext ω
    exact (StopAtFirstHitGoalIff (fun s : ℝ => s ≤ a) X t ω).symm
  rw [Equal]
  exact Cumulative t

/-- A single-product early-hit bound for beta at least one. The initial term
is clipped to one on the target, so already-successful initial laws are legal.
The original process need not absorb, and the potential may be nonlinear. -/
theorem ExponentialDriftLowerTailProductOfCondExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a Lambda : ℝ) (g : ℝ → ℝ)
    (beta : ℕ → ℝ) (Values : ∀ j ω, X j ω ∈ S)
    (NonnegativeLambda : 0 ≤ Lambda) (OneLeBeta : ∀ j, 1 ≤ beta j)
    (PotentialBelow : ∀ s ∈ S, s ≤ a → g s ≤ g a)
    (Moment : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * (g (X j u) - g (X (j + 1) u))) | F j]) ω ≤ beta j)
    (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, beta j) *
        (∫ ω, if X 0 ω ≤ a then 1 else Real.exp (-Lambda * (g (X 0 ω) - g a)) ∂μ)) := by
  classical
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  let C := fun s => if s ≤ a then 1 else Real.exp (-Lambda * (g s - g a))
  let K := KilledExponentialPotential a (-Lambda) g
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have IntegrableC (j : ℕ) : Integrable (fun ω => C (Y j ω)) μ :=
    FiniteStateCompositionIntegrable μ (Y j) S C AdaptedY.measurable (YValues j)
  have IntegrableK (j : ℕ) : Integrable (fun ω => K (Y j ω)) μ :=
    FiniteStateCompositionIntegrable μ (Y j) S K AdaptedY.measurable (YValues j)
  have Step (j : ℕ) : (∫ ω, C (Y (j + 1) ω) ∂μ) ≤
      beta j * (∫ ω, C (Y j ω) ∂μ) := by
    let A := {ω | a < Y j ω}
    let H := A.indicator (fun ω => Real.exp (-Lambda * (g (X (j + 1) ω) - g a)))
    let I := Aᶜ.indicator (fun _ : Ω => (1 : ℝ))
    have Event : MeasurableSet A := F.le j _ (measurableSet_lt measurable_const (AdaptedY j))
    have HIntegrable : Integrable H μ := (FiniteStateCompositionIntegrable μ (X (j + 1)) S
      (fun s => Real.exp (-Lambda * (g s - g a))) AdaptedX.measurable (Values (j + 1))).indicator Event
    have IIntegrable : Integrable I μ := (integrable_const (1 : ℝ)).indicator Event.compl
    have INonnegative (ω : Ω) : 0 ≤ I ω := Set.indicator_nonneg (by intros; norm_num) ω
    have Comparison (ω : Ω) : C (Y (j + 1) ω) ≤ I ω + H ω := by
      by_cases Active : ω ∈ A
      · have Above : a < Y j ω := Active
        have Same := (StopAtFirstHitStepBefore (fun s : ℝ => s ≤ a) X j ω
          (not_le_of_gt Above)).2
        change Y (j + 1) ω = X (j + 1) ω at Same
        change C (Y (j + 1) ω) ≤ Aᶜ.indicator _ ω + A.indicator _ ω
        rw [Set.indicator_of_notMem (by simpa using Active), Set.indicator_of_mem Active, zero_add, Same]
        dsimp [C]
        split
        · rename_i Next
          apply Real.one_le_exp_iff.mpr
          exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr NonnegativeLambda)
            (sub_nonpos.mpr (PotentialBelow _ (Values (j + 1) ω) Next))
        · exact le_rfl
      · have AtTarget : Y j ω ≤ a := le_of_not_gt Active
        have Next := StopAtFirstHitAbsorbing (fun s : ℝ => s ≤ a) X j ω AtTarget
        change C (Y (j + 1) ω) ≤ Aᶜ.indicator _ ω + A.indicator _ ω
        rw [Set.indicator_of_mem Active, Set.indicator_of_notMem Active, add_zero]
        exact le_of_eq (if_pos Next)
    have Decomposition : (∫ ω, I ω ∂μ) + (∫ ω, K (Y j ω) ∂μ) =
        ∫ ω, C (Y j ω) ∂μ := by
      rw [← integral_add IIntegrable (IntegrableK j)]
      apply integral_congr_ae
      apply ae_of_all
      intro ω
      by_cases Active : ω ∈ A
      · have Above : a < Y j ω := Active
        change Aᶜ.indicator _ ω + K (Y j ω) = C (Y j ω)
        rw [Set.indicator_of_notMem (by simpa using Active), zero_add]
        simp only [K, C, KilledExponentialPotential, if_neg (not_le_of_gt Above)]
      · have AtTarget : Y j ω ≤ a := le_of_not_gt Active
        change Aᶜ.indicator _ ω + K (Y j ω) = C (Y j ω)
        rw [Set.indicator_of_mem Active]
        simp only [K, C, KilledExponentialPotential, if_pos AtTarget, add_zero]
    have Active := ActiveExponentialLowerExpectedStepOfCondExp μ X F AdaptedX S a Lambda
      (beta j) g Values j (Moment j)
    have ScaledI : (∫ ω, I ω ∂μ) ≤ beta j * (∫ ω, I ω ∂μ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (OneLeBeta j) (integral_nonneg INonnegative)
    calc
      _ ≤ ∫ ω, I ω + H ω ∂μ := integral_mono (IntegrableC (j + 1)) (IIntegrable.add HIntegrable) Comparison
      _ = (∫ ω, I ω ∂μ) + (∫ ω, H ω ∂μ) := integral_add IIntegrable HIntegrable
      _ ≤ beta j * (∫ ω, I ω ∂μ) + beta j * (∫ ω, K (Y j ω) ∂μ) := add_le_add ScaledI Active
      _ = _ := by rw [← mul_add, Decomposition]
  have Decay (j : ℕ) : (∫ ω, C (Y j ω) ∂μ) ≤
      (∏ r ∈ Finset.range j, beta r) * (∫ ω, C (X 0 ω) ∂μ) := by
    induction j with
    | zero => simp only [Y, Finset.range_zero, Finset.prod_empty, one_mul, StopAtFirstHitInitial, le_refl]
    | succ j Before =>
      calc
        _ ≤ beta j * (∫ ω, C (Y j ω) ∂μ) := Step j
        _ ≤ beta j * ((∏ r ∈ Finset.range j, beta r) * (∫ ω, C (X 0 ω) ∂μ)) :=
          mul_le_mul_of_nonneg_left Before (zero_le_one.trans (OneLeBeta j))
        _ = _ := by rw [Finset.prod_range_succ]; ring
  have NonnegativeC (ω : Ω) : 0 ≤ C (Y t ω) := by
    dsimp [C]
    split
    · norm_num
    · exact (Real.exp_pos _).le
  have Markov := (IntegrableC t).measure_le_integral (ae_of_all μ NonnegativeC)
    (s := {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)}) (by
      intro ω Hit
      have AtTarget := (StopAtFirstHitGoalIff (fun s : ℝ => s ≤ a) X t ω).mpr Hit
      exact le_of_eq (if_pos AtTarget).symm)
  exact Markov.trans (ENNReal.ofReal_le_ofReal (Decay t))

/-- Fixed-start form of the general-target sum bound. -/
theorem ExponentialDriftLowerTailSumOfFixedInitial
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a s₀ Lambda : ℝ) (g : ℝ → ℝ)
    (beta : ℕ → ℝ) (Values : ∀ j ω, X j ω ∈ S)
    (NonnegativeLambda : 0 ≤ Lambda) (NonnegativeBeta : ∀ j, 0 ≤ beta j)
    (PotentialBelow : ∀ s ∈ S, s ≤ a → g s ≤ g a)
    (InitialAbove : a < s₀) (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω = s₀)
    (Moment : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * (g (X j u) - g (X (j + 1) u))) | F j]) ω ≤ beta j)
    (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((∑ j ∈ Finset.range t, ∏ r ∈ Finset.range (j + 1), beta r) *
        Real.exp (-Lambda * (g s₀ - g a))) := by
  have Above : ∀ᵐ ω ∂μ, a < X 0 ω := by
    filter_upwards [FixedInitial] with ω Equal
    rwa [Equal]
  have Bound := ExponentialDriftLowerTailSumOfCondExp μ X F AdaptedX S a Lambda g beta Values
    NonnegativeLambda NonnegativeBeta PotentialBelow Above Moment t
  have InitialIntegral : (∫ ω, Real.exp (-Lambda * (g (X 0 ω) - g a)) ∂μ) =
      Real.exp (-Lambda * (g s₀ - g a)) := by
    calc
      _ = ∫ _ω : Ω, Real.exp (-Lambda * (g s₀ - g a)) ∂μ := integral_congr_ae (by
        filter_upwards [FixedInitial] with ω Equal
        rw [Equal])
      _ = _ := by rw [integral_const, probReal_univ, one_smul]
  rw [InitialIntegral, ← Finset.sum_mul] at Bound
  exact Bound

/-- Fixed-start form of the general-target single-product bound. -/
theorem ExponentialDriftLowerTailProductOfFixedInitial
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a s₀ Lambda : ℝ) (g : ℝ → ℝ)
    (beta : ℕ → ℝ) (Values : ∀ j ω, X j ω ∈ S)
    (NonnegativeLambda : 0 ≤ Lambda) (OneLeBeta : ∀ j, 1 ≤ beta j)
    (PotentialBelow : ∀ s ∈ S, s ≤ a → g s ≤ g a)
    (InitialAbove : a < s₀) (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω = s₀)
    (Moment : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * (g (X j u) - g (X (j + 1) u))) | F j]) ω ≤ beta j)
    (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, beta j) * Real.exp (-Lambda * (g s₀ - g a))) := by
  have Bound := ExponentialDriftLowerTailProductOfCondExp μ X F AdaptedX S a Lambda g beta Values
    NonnegativeLambda OneLeBeta PotentialBelow Moment t
  have InitialIntegral : (∫ ω, if X 0 ω ≤ a then 1 else Real.exp (-Lambda * (g (X 0 ω) - g a)) ∂μ) =
      Real.exp (-Lambda * (g s₀ - g a)) := by
    calc
      _ = ∫ _ω : Ω, Real.exp (-Lambda * (g s₀ - g a)) ∂μ := integral_congr_ae (by
        filter_upwards [FixedInitial] with ω Equal
        rw [Equal, if_neg (not_le_of_gt InitialAbove)])
      _ = _ := by rw [integral_const, probReal_univ, one_smul]
  rwa [InitialIntegral] at Bound

end
end ECTheoryLib.Tools.Drift
