import ECTheoryLib.Analysis.Linear.OnePlusOneEA.CountDecrease
import ECTheoryLib.Tools.Runtime.Multiplicative.PositivePartLower
import ECTheoryLib.Analysis.Linear.UniformInitialization
import ECTheoryLib.Analysis.Linear.RLS.PositiveWeights
import ECTheoryLib.Tools.Drift.Potential.LogarithmicBounds
import ECTheoryLib.Operators.Mutation.BitPattern

/-! The original standard weak-elitist EA minimizing a positive weighted
linear objective. One-count may increase even under strict improvement. -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open ECTheoryLib.Tools.Drift
open scoped unitInterval
noncomputable section

/-- The original minimization kernel; the separate EALinear.Step maximizes. -/
def Step {n : ℕ} (PositiveLength : 0 < n) (Weights : Fin n → ℝ) : Transition (Bits n) :=
  OnePlusOneEAStep PositiveLength (Problems.MinNotWorse (Score Weights))

def ExpectedRuntime {n : ℕ} (PositiveLength : 0 < n) (Weights : Fin n → ℝ)
    (Initial : PMF (Bits n)) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength Weights) (fun x => Score Weights x = 0) Initial

private def UnitRate {n : ℕ} (PositiveLength : 0 < n) : I :=
  ⟨1/(n : ℝ), by
    constructor
    · positivity
    · exact (div_le_one (Nat.cast_pos.mpr PositiveLength)).mpr
        (Nat.one_le_cast.mpr PositiveLength)⟩

private theorem UnitRateValue {n : ℕ} (PositiveLength : 0 < n) :
    ENNReal.ofReal (UnitRate PositiveLength : ℝ) = (n : ENNReal)⁻¹ := by
  change ENNReal.ofReal (1/(n : ℝ)) = (n : ENNReal)⁻¹
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr PositiveLength), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast, one_div]

/-- Selection preserves the actual mutation domination of positive decrease. -/
theorem StepPositivePartDrift {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Parent : Bits n) :
    (∫ Next, max ((OneMax Parent : ℝ)-(OneMax Next : ℝ)) 0
      ∂(Step PositiveLength Weights Parent).toMeasure) ≤ (OneMax Parent : ℝ)/(n : ℝ) := by
  have Mean := FlippedOnesExpectation (UnitRate PositiveLength) Parent
  simp only [UnitRateValue] at Mean
  change (∫ Candidate, (FlippedOnes Parent Candidate : ℝ)
    ∂(StandardBitMutation PositiveLength Parent).toMeasure) =
      (1/(n : ℝ))*(OneMax Parent : ℝ) at Mean
  unfold Step OnePlusOneEAStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    integral_map_of_stronglyMeasurable (measurable_of_finite _) (measurable_of_finite _).stronglyMeasurable]
  calc
    _ ≤ ∫ Candidate, (FlippedOnes Parent Candidate : ℝ)
        ∂(StandardBitMutation PositiveLength Parent).toMeasure :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (SelectedCountPositiveDecreaseLeFlippedOnes (Problems.MinNotWorse (Score Weights)) Parent)
    _ = (1/(n : ℝ))*(OneMax Parent : ℝ) := Mean
    _ = _ := by ring

/-- The actual half-count drop has the source-compatible closed tail bound.
Counts one and two use the first moment; larger counts use the factorial moment. -/
theorem StepHalfJumpProbability {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Parent : Bits n) (PositiveCount : 0 < OneMax Parent) :
    (Step PositiveLength Weights Parent).toMeasure.real
      {Next | (1/2 : ℝ)*(OneMax Parent : ℝ) ≤ (OneMax Parent : ℝ)-(OneMax Next : ℝ)} ≤
        8/((n : ℝ)*(1+Real.log (OneMax Parent : ℝ))) := by
  let μ := (StandardBitMutation PositiveLength Parent).toMeasure
  let s : ℝ := OneMax Parent
  let A : Set (Bits n) := {Candidate | s/2 ≤ (FlippedOnes Parent Candidate : ℝ)}
  have PositiveS : 0 < s := Nat.cast_pos.mpr PositiveCount
  have OneS : (1 : ℝ) ≤ s := by
    dsimp [s]
    exact_mod_cast PositiveCount
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have LogNonnegative : 0 ≤ Real.log s := Real.log_nonneg OneS
  have PositiveLog : 0 < 1+Real.log s := by linarith
  have LogLeS : 1+Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos PositiveS]
  have SLeN : s ≤ (n : ℝ) := by dsimp [s]; exact_mod_cast Problems.OneMax.OneMaxLeN Parent
  have LogLeN : 1+Real.log s ≤ (n : ℝ) := LogLeS.trans SLeN
  have Dominated : (Step PositiveLength Weights Parent).toMeasure.real
      {Next | (1/2 : ℝ)*(OneMax Parent : ℝ) ≤ (OneMax Parent : ℝ)-(OneMax Next : ℝ)} ≤ μ.real A := by
    unfold Step OnePlusOneEAStep
    rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
      map_measureReal_apply (measurable_of_finite _) (Set.to_countable _).measurableSet]
    apply measureReal_mono _ (measure_ne_top _ _)
    intro Candidate Member
    change s/2 ≤ (FlippedOnes Parent Candidate : ℝ)
    have Bound := SelectedCountPositiveDecreaseLeFlippedOnes
      (Problems.MinNotWorse (Score Weights)) Parent Candidate
    change (1/2 : ℝ)*s ≤ s-
      (OneMax (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent Candidate) : ℝ) at Member
    have Half : s/2 ≤ max (s-
        (OneMax (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent Candidate) : ℝ)) 0 :=
      (by linarith : s/2 ≤ s-
        (OneMax (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent Candidate) : ℝ)).trans
          (le_max_left _ _)
    exact Half.trans Bound
  apply Dominated.trans
  by_cases LargeCount : 3 ≤ OneMax Parent
  · have Bound := FlippedOnesHalfProbability (UnitRate PositiveLength) Parent LargeCount
    simp only [UnitRateValue] at Bound
    change μ.real A ≤ 8*(1/(n : ℝ))^2 at Bound
    apply Bound.trans
    calc
      8*(1/(n : ℝ))^2 = 8/((n : ℝ)*(n : ℝ)) := by ring
      _ ≤ 8/((n : ℝ)*(1+Real.log s)) :=
        div_le_div_of_nonneg_left (by norm_num) (mul_pos PositiveN PositiveLog)
          (mul_le_mul_of_nonneg_left LogLeN PositiveN.le)
  · have Small : s ≤ 2 := by
      dsimp [s]
      exact_mod_cast (show OneMax Parent ≤ 2 by omega)
    have Containment : A ⊆ {Candidate | 1 ≤ (FlippedOnes Parent Candidate : ℝ)} := by
      intro Candidate Member
      have Nonzero : FlippedOnes Parent Candidate ≠ 0 := by
        intro Zero
        change s/2 ≤ (FlippedOnes Parent Candidate : ℝ) at Member
        rw [Zero, Nat.cast_zero] at Member
        linarith
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Nonzero
    have Bound := FlippedOnesAtLeastOneProbability (UnitRate PositiveLength) Parent
    simp only [UnitRateValue] at Bound
    change μ.real {Candidate | 1 ≤ (FlippedOnes Parent Candidate : ℝ)} ≤ (1/(n : ℝ))*s at Bound
    have RateScale : (1/(n : ℝ))*s = s/(n : ℝ) := by ring
    rw [RateScale] at Bound
    have Probability := (measureReal_mono Containment (measure_ne_top μ _)).trans Bound
    apply Probability.trans
    apply (le_div_iff₀ (mul_pos PositiveN PositiveLog)).mpr
    have Cancel : (s/(n : ℝ))*((n : ℝ)*(1+Real.log s)) = s*(1+Real.log s) := by field_simp
    rw [Cancel]
    have Product := mul_le_mul_of_nonneg_right Small PositiveLog.le
    nlinarith [Product]

/-- Strictly positive weights identify score zero with the actual optimum.
The existing RLS proof of this objective-only fact is reused unchanged. -/
theorem CountZeroIffScoreZero {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ i, 0 < Weights i) (x : Bits n) :
    (OneMax x : ℝ) = 0 ↔ Score Weights x = 0 := by
  rw [← ScoreUnitWeights x,
    RLSLinear.ScoreZeroIff (fun _ => 1) (fun _ => by norm_num),
    RLSLinear.ScoreZeroIff Weights Positive]

/-- The same minimizing-EA trajectories satisfy the nonmonotone lower
bound. Delta16/n is positive for every n>0, and <=1 when n>=16. -/
theorem InitialRuntimeLower {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Initial : PMF (Bits n)) :
    ENNReal.ofReal (((n : ℝ)/48)*(∫ x, MultiplicativeDriftPotential 1 1 (OneMax x : ℝ)
      ∂Initial.toMeasure)) ≤ ExpectedRuntime PositiveLength Weights Initial := by
  classical
  let S : Finset ℝ := (Finset.range (n+1)).image (fun k : ℕ => (k : ℝ))
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have ZeroInS : (0 : ℝ) ∈ S := Finset.mem_image.mpr ⟨0, by simp, by simp⟩
  have Lower : ∀ s ∈ S, s = 0 ∨ 1 ≤ s := by
    intro s Member
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp Member
    by_cases Zero : k = 0
    · exact Or.inl (by simp [Zero])
    · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero)
  have Values (x : Bits n) : (OneMax x : ℝ) ∈ S :=
    Finset.mem_image.mpr ⟨OneMax x, Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Problems.OneMax.OneMaxLeN x)), rfl⟩
  have Bound := Tools.Runtime.MultiplicativeRuntimeLowerBoundOfPositivePart
    (Step PositiveLength Weights) Initial (fun x => (OneMax x : ℝ))
    (fun x => Score Weights x = 0) (fun _ => True) S 1 (1/2) (16/(n : ℝ)) ZeroInS
    (by norm_num) Lower Values (CountZeroIffScoreZero Weights Positive)
    (ae_of_all _ (fun _ => True.intro)) (fun _ => ae_of_all _ (fun _ _ => True.intro))
    (by norm_num) (by norm_num) (by positivity) (by
      intro x _ _
      apply (StepPositivePartDrift PositiveLength Weights x).trans
      have Nonnegative : 0 ≤ (OneMax x : ℝ)/(n : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) PositiveN.le
      calc
        (OneMax x : ℝ)/(n : ℝ) ≤ 16*((OneMax x : ℝ)/(n : ℝ)) := by linarith
        _ = (16/(n : ℝ))*(OneMax x : ℝ) := by ring) (by
      intro x _ Nonzero
      have PositiveCount : 0 < OneMax x := Nat.pos_of_ne_zero (by
        intro Zero
        exact Nonzero (by simp [Zero]))
      have Jump := StepHalfJumpProbability PositiveLength Weights x PositiveCount
      have PositiveLog : 0 < 1+Real.log (OneMax x : ℝ) := by
        have LogNonnegative := Real.log_nonneg (Nat.one_le_cast.mpr PositiveCount :
          (1 : ℝ) ≤ (OneMax x : ℝ))
        linarith
      convert Jump using 1
      simp only [div_one]
      field_simp
      ring)
  have Coefficient (m : ℝ) : (((1 : ℝ)-1/2)/(1+1/2))*(m/(16/(n : ℝ))) =
      ((n : ℝ)/48)*m := by
    field_simp
    ring
  simpa only [Coefficient, ExpectedRuntime] using Bound

theorem FixedRuntimeLower {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) (Parent : Bits n)
    (PositiveCount : 0 < OneMax Parent) :
    ENNReal.ofReal (((n : ℝ)/48)*(1+Real.log (OneMax Parent : ℝ))) ≤
      ExpectedRuntime PositiveLength Weights (PMF.pure Parent) := by
  have Bound := InitialRuntimeLower PositiveLength Weights Positive (PMF.pure Parent)
  simpa only [PMF.toMeasure_pure, integral_dirac, MultiplicativeDriftPotential,
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt PositiveCount), if_false, div_one] using Bound

/-- Uniform initialization keeps its all-zero atom. The lower bound follows
from the existing finite logarithmic chord and actual uniform one-count mean. -/
theorem UniformRuntimeLower {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ i, 0 < Weights i) :
    ENNReal.ofReal ((n : ℝ)*(1+Real.log (n : ℝ))/96) ≤
      ExpectedRuntime PositiveLength Weights (OnePlusOneEAInit n) := by
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have InitMean : (∫ x, (OneMax x : ℝ) ∂(OnePlusOneEAInit n).toMeasure) = (n : ℝ)/2 := by
    have Mean := LinearInitialization.UniformLinearScoreExpectation (n := n) (fun _ => 1)
    simpa [OnePlusOneEAInit, RLSInit, ScoreUnitWeights] using Mean
  have Chord (x : Bits n) :
      ((OneMax x : ℝ)/(n : ℝ))*(1+Real.log (n : ℝ)) ≤
        MultiplicativeDriftPotential 1 1 (OneMax x : ℝ) := by
    have Gap : (OneMax x : ℝ) = 0 ∨ 1 ≤ (OneMax x : ℝ) := by
      by_cases Zero : OneMax x = 0
      · exact Or.inl (by simp [Zero])
      · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero)
    simpa only [div_one] using MultiplicativePotentialLowerChord 1 (n : ℝ) (OneMax x : ℝ)
      (by norm_num) (Nat.one_le_cast.mpr PositiveLength) Gap
      (by exact_mod_cast Problems.OneMax.OneMaxLeN x)
  have Compared := integral_mono (μ := (OnePlusOneEAInit n).toMeasure)
    Integrable.of_finite Integrable.of_finite Chord
  rw [integral_mul_const, integral_div, InitMean] at Compared
  have Identity : ((n : ℝ)/2/(n : ℝ))*(1+Real.log (n : ℝ)) =
      (1+Real.log (n : ℝ))/2 := by field_simp
  have LowerIntegral : (1+Real.log (n : ℝ))/2 ≤
      ∫ x, MultiplicativeDriftPotential 1 1 (OneMax x : ℝ) ∂(OnePlusOneEAInit n).toMeasure := by
    simpa only [Identity] using Compared
  calc
    ENNReal.ofReal ((n : ℝ)*(1+Real.log (n : ℝ))/96) =
        ENNReal.ofReal (((n : ℝ)/48)*((1+Real.log (n : ℝ))/2)) := by congr 1; ring
    _ ≤ ENNReal.ofReal (((n : ℝ)/48)*
        (∫ x, MultiplicativeDriftPotential 1 1 (OneMax x : ℝ) ∂(OnePlusOneEAInit n).toMeasure)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left LowerIntegral (by positivity))
    _ ≤ _ := InitialRuntimeLower PositiveLength Weights Positive (OnePlusOneEAInit n)

theorem AtGoalRuntime {n : ℕ} (PositiveLength : 0 < n) (Weights : Fin n → ℝ) :
    ExpectedRuntime PositiveLength Weights (PMF.pure (fun _ => false)) = 0 :=
  ExpectedHittingTimeOfPureTarget (Step PositiveLength Weights) (fun x => Score Weights x = 0)
    (fun _ => false) (ScoreAllZeros Weights)

/-- A distinct accepted child has exactly its original mutation mass.
Rejected proposals can only contribute additional mass to the parent. -/
theorem StepAcceptedProbability {n : ℕ} (PositiveLength : 0 < n) (Weights : Fin n → ℝ)
    (Parent Child : Bits n) (Different : Child ≠ Parent)
    (Accepted : Score Weights Child ≤ Score Weights Parent) :
    Step PositiveLength Weights Parent Child = StandardBitMutation PositiveLength Parent Child := by
  classical
  have Preimage : (fun Candidate => ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent Candidate) ⁻¹'
      {Child} = {Child} := by
    ext Candidate
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    unfold ElitistSelect
    split_ifs with AcceptCandidate
    · rfl
    · have DifferentCandidate : Candidate ≠ Child := by
        intro Equal
        subst Candidate
        exact AcceptCandidate Accepted
      exact iff_of_false (Ne.symm Different) DifferentCandidate
  have EqualMeasure : (Step PositiveLength Weights Parent).toMeasure {Child} =
      (StandardBitMutation PositiveLength Parent).toMeasure {Child} := by
    unfold Step OnePlusOneEAStep
    rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
      Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _), Preimage]
  simpa only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] using EqualMeasure

theorem StepAcceptedProbabilityPositive {n : ℕ} (PositiveLength : 0 < n) (AtLeastTwo : 2 ≤ n)
    (Weights : Fin n → ℝ) (Parent Child : Bits n) (Different : Child ≠ Parent)
    (Accepted : Score Weights Child ≤ Score Weights Parent) :
    0 < Step PositiveLength Weights Parent Child := by
  rw [StepAcceptedProbability PositiveLength Weights Parent Child Different Accepted,
    StandardBitMutationProbability]
  have GreaterOne : (1 : ENNReal) < n := by exact_mod_cast (show 1 < n by omega)
  have RateLessOne : (n : ENNReal)⁻¹ < 1 := ENNReal.inv_lt_one.mpr GreaterOne
  have RatePositive : 0 < (n : ENNReal)⁻¹ := ENNReal.inv_pos.mpr (by simp)
  apply bot_lt_iff_ne_bot.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs
  · exact (tsub_pos_iff_lt.mpr RateLessOne).ne'
  · exact RatePositive.ne'

/-- For every length at least three, an actual improving accepted mutation
can increase one-count. In particular this persists in the source n>=16 range. -/
theorem PositiveRebound {n : ℕ} (PositiveLength : 0 < n) (AtLeastThree : 3 ≤ n) :
    ∃ Weights : Fin n → ℝ, (∀ i, 0 < Weights i) ∧ ∃ Parent Child : Bits n,
      Score Weights Child < Score Weights Parent ∧ OneMax Parent < OneMax Child ∧
        0 < Step PositiveLength Weights Parent Child := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have D01 : i0 ≠ i1 := by
    intro Equal
    have Values : (0 : ℕ) = 1 := congrArg Fin.val Equal
    omega
  have D02 : i0 ≠ i2 := by
    intro Equal
    have Values : (0 : ℕ) = 2 := congrArg Fin.val Equal
    omega
  have D12 : i1 ≠ i2 := by
    intro Equal
    have Values : (1 : ℕ) = 2 := congrArg Fin.val Equal
    omega
  let Weights : Fin n → ℝ := fun i => if i = i0 then 5 else 1
  let Parent : Bits n := fun i => decide (i = i0)
  let Child : Bits n := fun i => decide (i = i1 ∨ i = i2)
  have Positive : ∀ i, 0 < Weights i := by
    intro i
    dsimp [Weights]
    split_ifs <;> norm_num
  have ParentCount : OneMax Parent = 1 := by simp [OneMax, Parent]
  have ChildCoordinate (i : Fin n) : (if Child i then (1 : ℕ) else 0) =
      (if i = i1 then 1 else 0)+(if i = i2 then 1 else 0) := by
    by_cases First : i = i1
    · subst i
      simp [Child, D12]
    · by_cases Second : i = i2
      · subst i
        simp [Child, Ne.symm D12]
      · simp [Child, First, Second]
  have ChildCount : OneMax Child = 2 := by
    unfold OneMax
    simp_rw [ChildCoordinate]
    rw [Finset.sum_add_distrib]
    simp
  have ParentScore : Score Weights Parent = 5 := by simp [Score, Weights, Parent, mul_ite]
  have ChildScore : Score Weights Child = (OneMax Child : ℝ) := by
    rw [← ScoreUnitWeights Child]
    unfold Score
    apply Finset.sum_congr rfl
    intro i _
    by_cases Heavy : i = i0
    · subst i
      simp [Weights, Child, D01, D02]
    · simp [Weights, Heavy]
  have Different : Child ≠ Parent := by
    intro Equal
    have SameCount := congrArg (OneMax (n := n)) Equal
    rw [ChildCount, ParentCount] at SameCount
    omega
  have Accepted : Score Weights Child ≤ Score Weights Parent := by
    rw [ChildScore, ChildCount, ParentScore]
    norm_num
  refine ⟨Weights, Positive, Parent, Child, ?_, ?_, ?_⟩
  · rw [ChildScore, ChildCount, ParentScore]
    norm_num
  · rw [ParentCount, ChildCount]
    norm_num
  · exact StepAcceptedProbabilityPositive PositiveLength (by omega) Weights Parent Child Different Accepted

end
end ECTheoryLib.Analysis.EALinearMinimization

