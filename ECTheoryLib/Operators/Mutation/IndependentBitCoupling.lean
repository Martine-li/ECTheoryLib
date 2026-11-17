import ECTheoryLib.Probability.Distributions.BinomialDomination
import ECTheoryLib.Operators.Mutation.IndependentBit

/-!
# Coupling independent bit mutation

Threshold the existing product of uniform samples to obtain the actual operator
law. The pointwise comparison is coordinatewise and needs mutation rate at most
one half; objective-specific permutation arguments belong in Analysis.
-/

namespace ECTheoryLib
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- A Boolean Bernoulli sample obtained by thresholding a uniform coordinate. -/
def ThresholdBit (p : I) (u : OpenUnitInterval) : Bool := decide ((u : ℝ) ≤ (p : ℝ))

/-- Thresholding is measurable, including probability endpoints. -/
theorem ThresholdBitMeasurable (p : I) : Measurable (ThresholdBit p) := by
  classical
  exact (measurable_of_finite (fun b : Prop => decide b)).comp (UniformThresholdMeasurable p)

/-- The full Boolean law agrees with the upstream Bernoulli measure. -/
theorem ThresholdBitLaw (p : I) :
    OpenUnitUniform.map (ThresholdBit p) = bernoulliMeasure true false p := by
  classical
  change Measure.map ((fun b : Prop => decide b) ∘ (fun u : OpenUnitInterval => (u : ℝ) ≤ (p : ℝ))) _ = _
  rw [← Measure.map_map (measurable_of_finite (fun b : Prop => decide b)) (UniformThresholdMeasurable p)]
  have PropositionLaw : OpenUnitUniform.map (fun u : OpenUnitInterval => (u : ℝ) ≤ (p : ℝ)) =
      bernoulliMeasure True False p := UniformThresholdLaw p
  rw [PropositionLaw, map_bernoulliMeasure]
  simp only [decide_true, decide_false]

/-- Probability that the mutated bit is one, conditional on the parent bit. -/
def MutationOneProbability (p : I) (Parent : Bool) : I :=
  if Parent then unitInterval.symm p else p

/-- A real unit-interval parameter supplies the existing mutation PMF bound. -/
theorem MutationProbabilityBound (p : I) : ENNReal.ofReal (p : ℝ) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal p.2.2

/-- Each coordinate mass equals the actual bit-flip operator mass. -/
theorem BernoulliMutationMass (p : I) (Parent Candidate : Bool) :
    bernoulliMeasure true false (MutationOneProbability p Parent) {Candidate} =
      BitMutationProbability (ENNReal.ofReal (p : ℝ)) Parent Candidate := by
  have Coefficient (q : I) : (unitInterval.toNNReal q : ENNReal) = ENNReal.ofReal (q : ℝ) := by
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  have Complement : ENNReal.ofReal (1 - (p : ℝ)) = 1 - ENNReal.ofReal (p : ℝ) := by
    rw [ENNReal.ofReal_sub 1 p.2.1, ENNReal.ofReal_one]
  cases Parent with
  | false =>
      cases Candidate with
      | false =>
          simp only [MutationOneProbability, Bool.false_eq_true, if_false,
            bernoulliMeasure_apply (p := p) (measurableSet_singleton false), mem_singleton_iff,
            Bool.true_eq_false, Bool.false_eq_true, if_false, if_true,
            BitMutationProbability, Coefficient, unitInterval.coe_symm_eq]
          exact Complement
      | true =>
          simp only [MutationOneProbability, Bool.false_eq_true, if_false,
            bernoulliMeasure_apply (p := p) (measurableSet_singleton true), mem_singleton_iff,
            Bool.true_eq_false, Bool.false_eq_true, if_false, if_true,
            BitMutationProbability, Coefficient]
  | true =>
      cases Candidate with
      | false =>
          simp only [MutationOneProbability, if_true,
            bernoulliMeasure_apply (p := unitInterval.symm p) (measurableSet_singleton false), mem_singleton_iff,
            Bool.true_eq_false, Bool.false_eq_true, if_false, if_true,
            BitMutationProbability, unitInterval.symm_symm, Coefficient]
      | true =>
          simp only [MutationOneProbability, if_true,
            bernoulliMeasure_apply (p := unitInterval.symm p) (measurableSet_singleton true), mem_singleton_iff,
            Bool.false_eq_true, if_false, if_true,
            BitMutationProbability, Coefficient, unitInterval.coe_symm_eq]
          exact Complement

/-- The independent product law is the existing mutation operator law. -/
theorem IndependentBitMutationProductLaw {n : ℕ} (p : I) (Parent : Bits n) :
    Measure.pi (fun i => bernoulliMeasure true false (MutationOneProbability p (Parent i))) =
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure := by
  apply Measure.ext_of_singleton
  intro Candidate
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    IndependentBitMutationProbability]
  apply Finset.prod_congr rfl
  intro i _Member
  exact BernoulliMutationMass p (Parent i) (Candidate i)

/-- Use the same uniform coordinate samples for all parents. -/
def CoupledBitMutation {n : ℕ} (p : I) (Parent : Bits n) (u : Fin n → OpenUnitInterval) : Bits n :=
  fun i => ThresholdBit (MutationOneProbability p (Parent i)) (u i)

/-- The coupled offspring is a measurable vector of threshold bits. -/
theorem CoupledBitMutationMeasurable {n : ℕ} (p : I) (Parent : Bits n) :
    Measurable (CoupledBitMutation p Parent) :=
  measurable_pi_lambda _ (fun i => (ThresholdBitMeasurable _).comp (measurable_pi_apply i))

/-- The coupling preserves the full offspring law for each parent. -/
theorem CoupledBitMutationLaw {n : ℕ} (p : I) (Parent : Bits n) :
    HasLaw (CoupledBitMutation p Parent)
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
      (UniformTrials (Fin n)) := by
  refine ⟨(CoupledBitMutationMeasurable p Parent).aemeasurable, ?_⟩
  change (Measure.pi (fun _ : Fin n => OpenUnitUniform)).map
    (fun u i => ThresholdBit (MutationOneProbability p (Parent i)) (u i)) = _
  rw [Measure.pi_map_pi (fun i => (ThresholdBitMeasurable (MutationOneProbability p (Parent i))).aemeasurable)]
  simp only [ThresholdBitLaw]
  exact IndependentBitMutationProductLaw p Parent

/-- Rates at most one half preserve the order of parent-bit success probabilities. -/
theorem MutationOneProbabilityMonotone (p : I) (RateHalf : (p : ℝ) ≤ 1 / 2)
    (Parent Other : Bool) (Ordered : Parent = true → Other = true) :
    (MutationOneProbability p Parent : ℝ) ≤ (MutationOneProbability p Other : ℝ) := by
  cases Parent with
  | false =>
      cases Other with
      | false => exact le_rfl
      | true =>
          change (p : ℝ) ≤ 1 - (p : ℝ)
          linarith
  | true =>
      have OtherTrue := Ordered rfl
      rw [OtherTrue]

/-- Coordinatewise parent inclusion yields pointwise coupled offspring inclusion. -/
theorem CoupledBitMutationMonotone {n : ℕ} (p : I) (RateHalf : (p : ℝ) ≤ 1 / 2)
    (Parent Other : Bits n) (Ordered : ∀ i, Parent i = true → Other i = true)
    (u : Fin n → OpenUnitInterval) :
    ∀ i, CoupledBitMutation p Parent u i = true → CoupledBitMutation p Other u i = true := by
  intro i First
  change decide ((u i : ℝ) ≤ (MutationOneProbability p (Parent i) : ℝ)) = true at First
  change decide ((u i : ℝ) ≤ (MutationOneProbability p (Other i) : ℝ)) = true
  apply decide_eq_true
  exact le_trans (of_decide_eq_true First) (MutationOneProbabilityMonotone p RateHalf _ _ (Ordered i))

/-- Permute coordinates without changing the bit-string length. -/
def ReindexBits {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Bits n) : Bits n := fun i => x (e i)

/-- Independent mutation commutes in law with every coordinate permutation. -/
theorem IndependentBitMutationReindex {n : ℕ} (Rate : ENNReal) (RateBound : Rate ≤ 1)
    (Parent : Bits n) (e : Equiv.Perm (Fin n)) :
    (IndependentBitMutation Rate RateBound Parent).toMeasure.map (ReindexBits e) =
      (IndependentBitMutation Rate RateBound (ReindexBits e Parent)).toMeasure := by
  apply Measure.ext_of_singleton
  intro Candidate
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have Preimage : ReindexBits e ⁻¹' {Candidate} = {ReindexBits e.symm Candidate} := by
    ext x
    change ReindexBits e x = Candidate ↔ x = ReindexBits e.symm Candidate
    constructor
    · intro Equal
      funext i
      have Coordinate := congrFun Equal (e.symm i)
      change x (e (e.symm i)) = Candidate (e.symm i) at Coordinate
      rw [e.apply_symm_apply] at Coordinate
      exact Coordinate
    · intro Equal
      subst x
      funext i
      change Candidate (e.symm (e i)) = Candidate i
      rw [e.symm_apply_apply]
  rw [Preimage, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    IndependentBitMutationProbability, IndependentBitMutationProbability]
  change (∏ i, BitMutationProbability Rate (Parent i) (Candidate (e.symm i))) =
    ∏ i, BitMutationProbability Rate (Parent (e i)) (Candidate i)
  calc
    (∏ i, BitMutationProbability Rate (Parent i) (Candidate (e.symm i))) =
      ∏ i, BitMutationProbability Rate (Parent (e i)) (Candidate (e.symm (e i))) :=
        (Equiv.prod_comp e _).symm
    _ = _ := by simp only [e.symm_apply_apply]

end
end ECTheoryLib

