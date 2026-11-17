import ECTheoryLib.Algorithms.RLS.Initialization
import ECTheoryLib.Probability.Concentration.BoundedDifferences
import ECTheoryLib.Analysis.LeadingOnes.RLS.UniformInitialization
import Mathlib.Tactic

/-!
# LeadingOnes initialization via bounded conditional expectations

Under the original RLSInit law, every future-average influence is at most 2.
The actual mean is 1 - 2^(-n), the centered MGF parameter is n, and both closed
tails have exponent -d^2/(2*n). Conditional in the theorem names refers to the
proof method; the exported MGF and tail conclusions are unconditional.
The same width 2 fails pointwise when n>=3. Known exact initialization tails
are stronger; these results validate the weaker interface, not a runtime gain.
-/



namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.LeadingOnes
noncomputable section

private theorem leadingOnesFutureCons {n : ℕ} (a : Bool) (k : ℕ) (x : Bits n) :
    FutureCoordinateMean (fun _ : Fin (n + 1) => (PMF.uniformOfFintype Bool).toMeasure)
      (fun y => (LeadingOnes y : ℝ)) (k + 1) (Fin.cons a x) =
    if a then 1 + FutureCoordinateMean
      (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
      (fun y => (LeadingOnes y : ℝ)) k x else 0 := by
  rw [FutureCoordinateMeanCons (A := fun _ : Fin (n + 1) => Bool)
    (fun _ => (PMF.uniformOfFintype Bool).toMeasure)
    (fun y => (LeadingOnes y : ℝ)) (measurable_of_countable _) a k x]
  cases a with
  | false => simp [FutureCoordinateMean, LeadingOnesConsFalse]
  | true =>
    simp only [↓reduceIte]
    dsimp only [FutureCoordinateMean]
    simp_rw [LeadingOnesConsTrue, Nat.cast_add, Nat.cast_one]
    rw [integral_add (integrable_const 1) (Integrable.of_finite),
      integral_const, probReal_univ, one_smul]

private theorem leadingOnesFutureHead {n : ℕ} (k : ℕ) (x : Bits (n + 1)) :
    FutureCoordinateMean (fun _ : Fin (n + 1) => (PMF.uniformOfFintype Bool).toMeasure)
      (fun y => (LeadingOnes y : ℝ)) (k + 1) x =
    if x 0 then 1 + FutureCoordinateMean
      (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
      (fun y => (LeadingOnes y : ℝ)) k (Fin.tail x) else 0 := by
  simpa only [Fin.cons_self_tail] using leadingOnesFutureCons (x 0) k (Fin.tail x)

/-- Uniform initialization satisfies the all-prefix future-average width2 condition. -/
theorem UniformLeadingOnesFutureDifference (n : ℕ) :
    ∀ (i : Fin n) (x y : Bits n), (∀ j, j.val < i.val → x j = y j) →
      |FutureCoordinateMean (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
          (fun z => (LeadingOnes z : ℝ)) (i.val + 1) x -
        FutureCoordinateMean (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
          (fun z => (LeadingOnes z : ℝ)) (i.val + 1) y| ≤ 2 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n Induction =>
    intro i x y Same
    cases i using Fin.cases with
    | zero =>
      have SuffixMean (z : Bits n) :
          FutureCoordinateMean (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
            (fun w => (LeadingOnes w : ℝ)) 0 z = 1 - (2 : ℝ)⁻¹ ^ n := by
        rw [FutureCoordinateMeanZero, ← RLSInitProduct n, UniformLeadingOnesExpectation]
      have PowerNonnegative : 0 ≤ (2 : ℝ)⁻¹ ^ n := pow_nonneg (by norm_num) _
      have PowerLeOne : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have Range (z : Bits (n + 1)) :
          0 ≤ FutureCoordinateMean (fun _ : Fin (n + 1) => (PMF.uniformOfFintype Bool).toMeasure)
              (fun w => (LeadingOnes w : ℝ)) 1 z ∧
          FutureCoordinateMean (fun _ : Fin (n + 1) => (PMF.uniformOfFintype Bool).toMeasure)
              (fun w => (LeadingOnes w : ℝ)) 1 z ≤ 2 := by
        rw [leadingOnesFutureHead 0 z, SuffixMean]
        split_ifs <;> constructor <;> linarith
      have X := Range x
      have Y := Range y
      simp only [Fin.val_zero, zero_add]
      exact abs_le.mpr ⟨by linarith [X.1, Y.2], by linarith [X.2, Y.1]⟩
    | succ i =>
      have SameHead : x 0 = y 0 := Same 0 (by simp)
      simp only [Fin.val_succ]
      rw [leadingOnesFutureHead (i.val + 1) x, leadingOnesFutureHead (i.val + 1) y,
        SameHead]
      split_ifs
      · simp only [add_sub_add_left_eq_sub]
        apply Induction i (Fin.tail x) (Fin.tail y)
        intro j Before
        exact Same j.succ (by simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using Before)
      · norm_num

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes




namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.LeadingOnes
open scoped NNReal
noncomputable section

theorem UniformLeadingOnesConditionalSubGaussian (n : ℕ) :
    HasSubgaussianMGF
      (fun x => (LeadingOnes x : ℝ) - (1 - (2 : ℝ)⁻¹ ^ n))
      (n : ℝ≥0) (RLSInit n).toMeasure := by
  have Marginal (i : Fin n) :
      (RLSInit n).toMeasure.map (fun x : Bits n => x i) =
        (PMF.uniformOfFintype Bool).toMeasure := by
    rw [RLSInitProduct]
    exact (measurePreserving_eval _ i).map_eq
  have Independent : iIndepFun (fun i (x : Bits n) => x i) (RLSInit n).toMeasure := by
    rw [RLSInitProduct]
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have Coordinate : ∀ (i : Fin n) (x y : Bits n),
      (∀ j, j.val < i.val → x j = y j) →
      |FutureCoordinateMean (fun j => (RLSInit n).toMeasure.map (fun z : Bits n => z j))
          (fun z => (LeadingOnes z : ℝ)) (i.val + 1) x -
        FutureCoordinateMean (fun j => (RLSInit n).toMeasure.map (fun z : Bits n => z j))
          (fun z => (LeadingOnes z : ℝ)) (i.val + 1) y| ≤ ((2 : ℝ≥0) : ℝ) := by
    simp_rw [Marginal]
    exact UniformLeadingOnesFutureDifference n
  have Bound := IndependentBoundedConditionalExpectationsSubGaussian
    (RLSInit n).toMeasure (fun i (x : Bits n) => x i)
    (fun _ => (measurable_of_finite _).aemeasurable) Independent
    (fun x => (LeadingOnes x : ℝ)) (fun _ => (2 : ℝ≥0))
    (measurable_of_finite _) Coordinate
  have Parameter : ((∑ _ : Fin n, (2 : ℝ≥0) ^ 2) / 4) = (n : ℝ≥0) := by
    norm_num [Finset.sum_const, nsmul_eq_mul]
  simpa only [UniformLeadingOnesExpectation, Parameter] using Bound

theorem UniformLeadingOnesConditionalUpperTail (n : ℕ)
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    (RLSInit n).toMeasure.real
      {x | (1 - (2 : ℝ)⁻¹ ^ n) + threshold ≤ (LeadingOnes x : ℝ)} ≤
      Real.exp (-threshold ^ 2 / (2 * (n : ℝ))) := by
  have Bound := (UniformLeadingOnesConditionalSubGaussian n).measure_ge_le Nonnegative
  have Event : {x : Bits n | threshold ≤ (LeadingOnes x : ℝ) - (1 - (2 : ℝ)⁻¹ ^ n)} =
      {x | (1 - (2 : ℝ)⁻¹ ^ n) + threshold ≤ (LeadingOnes x : ℝ)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  rw [Event] at Bound
  simpa only [NNReal.coe_natCast] using Bound

theorem UniformLeadingOnesConditionalLowerTail (n : ℕ)
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    (RLSInit n).toMeasure.real
      {x | (LeadingOnes x : ℝ) ≤ (1 - (2 : ℝ)⁻¹ ^ n) - threshold} ≤
      Real.exp (-threshold ^ 2 / (2 * (n : ℝ))) := by
  have Bound := (UniformLeadingOnesConditionalSubGaussian n).neg.measure_ge_le Nonnegative
  have Event : {x : Bits n | threshold ≤ -((LeadingOnes x : ℝ) - (1 - (2 : ℝ)⁻¹ ^ n))} =
      {x | (LeadingOnes x : ℝ) ≤ (1 - (2 : ℝ)⁻¹ ^ n) - threshold} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  change (RLSInit n).toMeasure.real
    {x | threshold ≤ -((LeadingOnes x : ℝ) - (1 - (2 : ℝ)⁻¹ ^ n))} ≤ _ at Bound
  rw [Event] at Bound
  simpa only [NNReal.coe_natCast] using Bound

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes


