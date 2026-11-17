import ECTheoryLib.Operators.Mutation.IndependentBitCoupling
import ECTheoryLib.Problems.OneMax
import Mathlib.Logic.Equiv.Fintype

/-!
# OneMax distribution order under independent mutation

Doerr, Lemma 1.8.12 (p. 33). Only the parent one-counts must be ordered;
the original parents need not be ordered coordinatewise. A permutation aligns
their true bits, and invariance of the actual mutation law removes that alignment.
The general theorem includes n = 0, p = 0 and p = 1/2.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- Coordinatewise true-bit inclusion implies a one-count comparison. -/
theorem OneMaxPointwiseMonotone {n : ℕ} (Parent Other : Bits n)
    (Ordered : ∀ i, Parent i = true → Other i = true) : OneMax Parent ≤ OneMax Other := by
  unfold OneMax
  apply Finset.sum_le_sum
  intro i _Member
  cases ParentBit : Parent i with
  | false => simp only [Bool.false_eq_true, if_false, Nat.zero_le]
  | true =>
      have OtherBit := Ordered i ParentBit
      simp only [OtherBit, if_true, le_refl]

/-- OneMax is invariant under coordinate permutations. -/
theorem OneMaxReindex {n : ℕ} (e : Equiv.Perm (Fin n)) (Parent : Bits n) :
    OneMax (ReindexBits e Parent) = OneMax Parent := by
  unfold OneMax ReindexBits
  exact Equiv.sum_comp e (fun i => if Parent i then (1 : ℕ) else 0)

/-- The common-uniform coupling compares coordinatewise ordered parents. -/
theorem MutationOneMaxPointwiseDomination {n : ℕ} (p : I) (RateHalf : (p : ℝ) ≤ 1 / 2)
    (Parent Other : Bits n) (Ordered : ∀ i, Parent i = true → Other i = true) :
    StochasticDominated
      ((IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.map OneMax)
      ((IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Other).toMeasure.map OneMax) := by
  have OneMaxLaw (x : Bits n) : HasLaw OneMax
      ((IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) x).toMeasure.map OneMax)
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) x).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable, rfl⟩
  apply StochasticDominatedOfCoupling (UniformTrials (Fin n)) _ _
    (fun u => OneMax (CoupledBitMutation p Parent u))
    (fun u => OneMax (CoupledBitMutation p Other u))
    ((OneMaxLaw Parent).fun_comp (CoupledBitMutationLaw p Parent))
    ((OneMaxLaw Other).fun_comp (CoupledBitMutationLaw p Other))
  exact ae_of_all _ (fun u => OneMaxPointwiseMonotone _ _ (CoupledBitMutationMonotone p RateHalf Parent Other Ordered u))

/-- Permuting a parent preserves its offspring one-count distribution. -/
theorem MutationOneMaxReindexLaw {n : ℕ} (Rate : ENNReal) (RateBound : Rate ≤ 1)
    (Parent : Bits n) (e : Equiv.Perm (Fin n)) :
    (IndependentBitMutation Rate RateBound (ReindexBits e Parent)).toMeasure.map OneMax =
      (IndependentBitMutation Rate RateBound Parent).toMeasure.map OneMax := by
  rw [← IndependentBitMutationReindex Rate RateBound Parent e,
    Measure.map_map (measurable_of_finite OneMax) (measurable_of_finite (ReindexBits e))]
  have FunctionEq : OneMax ∘ ReindexBits e = (OneMax : Bits n → ℕ) := by
    funext x
    exact OneMaxReindex e x
  rw [FunctionEq]

/-- Align the true coordinates of two parents using only their one-count order. -/
theorem OneMaxOrderedReindex {n : ℕ} (Parent Other : Bits n) (Counts : OneMax Parent ≤ OneMax Other) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, Parent i = true → ReindexBits e Other i = true := by
  classical
  let A := Finset.univ.filter (fun i => Parent i = true)
  let B := Finset.univ.filter (fun i => Other i = true)
  have CardA : A.card = OneMax Parent := by
    unfold A OneMax
    rw [Finset.card_filter]
  have CardB : B.card = OneMax Other := by
    unfold B OneMax
    rw [Finset.card_filter]
  have CardOrder : A.card ≤ B.card := by rw [CardA, CardB]; exact Counts
  obtain ⟨C, Subset, CardC⟩ := Finset.exists_subset_card_eq CardOrder
  obtain ⟨e, Image⟩ := Equiv.Perm.exists_map_finset_eq A C CardC.symm
  refine ⟨e, ?_⟩
  intro i ParentBit
  have InA : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ParentBit⟩
  have InC : e i ∈ C := by
    rw [← Image]
    exact Finset.mem_map.mpr ⟨i, InA, rfl⟩
  exact (Finset.mem_filter.mp (Subset InC)).2

/-- Book Lemma 1.8.12: mutation preserves stochastic one-count order for p <= 1/2. -/
theorem MutationOneMaxStochasticMonotone {n : ℕ} (p : I) (RateHalf : (p : ℝ) ≤ 1 / 2)
    (Parent Other : Bits n) (Counts : OneMax Parent ≤ OneMax Other) :
    StochasticDominated
      ((IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.map OneMax)
      ((IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Other).toMeasure.map OneMax) := by
  obtain ⟨e, Ordered⟩ := OneMaxOrderedReindex Parent Other Counts
  have Dominated := MutationOneMaxPointwiseDomination p RateHalf Parent (ReindexBits e Other) Ordered
  rw [MutationOneMaxReindexLaw] at Dominated
  exact Dominated

/-- The actual standard mutation rate 1/n satisfies the book bound when n >= 2. -/
theorem StandardMutationOneMaxStochasticMonotone {n : ℕ} (PositiveLength : 0 < n)
    (AtLeastTwo : 2 ≤ n) (Parent Other : Bits n) (Counts : OneMax Parent ≤ OneMax Other) :
    StochasticDominated ((StandardBitMutation PositiveLength Parent).toMeasure.map OneMax)
      ((StandardBitMutation PositiveLength Other).toMeasure.map OneMax) := by
  have PositiveReal : (0 : ℝ) < n := by exact_mod_cast PositiveLength
  have TwoReal : (2 : ℝ) ≤ n := by exact_mod_cast AtLeastTwo
  let p : I := ⟨1 / (n : ℝ), ⟨by positivity, (div_le_one PositiveReal).mpr (by linarith)⟩⟩
  have Half : (p : ℝ) ≤ 1 / 2 := by
    change 1 / (n : ℝ) ≤ 1 / 2
    exact one_div_le_one_div_of_le (by norm_num) TwoReal
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1 / (n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveReal, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  have Dominated := MutationOneMaxStochasticMonotone p Half Parent Other Counts
  unfold StandardBitMutation
  simp only [Rate] at Dominated
  exact Dominated

end
end ECTheoryLib.Analysis.OneMaxMutation
