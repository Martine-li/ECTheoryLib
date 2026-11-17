import ECTheoryLib.Analysis.Linear.RLS.CoordinateSymmetry
import ECTheoryLib.Analysis.Linear.RLS.BinVal
import ECTheoryLib.Probability.StochasticOrder.StochasticConditioning

/-!
The full conditional current-state law at one remaining one, and source-order
position probabilities. Conditioning is at a deterministic time, not a first visit.
-/
namespace ECTheoryLib.Analysis.RLSBinVal
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability RLSLinear
open ECTheoryLib.Problems.Linear.BinVal
open scoped BigOperators
noncomputable section

def SingleOne {n : ℕ} (i : Fin n) : Bits n := fun j => decide (j = i)

theorem SingleOneInjective {n : ℕ} : Function.Injective (SingleOne (n := n)) := by
  intro i j Equal
  by_contra Different
  have At := congrArg (fun x : Bits n => x i) Equal
  simp [SingleOne, Different] at At

theorem OneCountEqOneIff {n : ℕ} (x : Bits n) :
    OneMax x = 1 ↔ ∃ i, x = SingleOne i := by
  classical
  constructor
  · intro Count
    have Card : (Finset.univ.filter (fun i : Fin n => x i = true)).card = 1 := by
      simpa only [Finset.card_filter, OneMax] using Count
    obtain ⟨i, Equal⟩ := Finset.card_eq_one.mp Card
    refine ⟨i, ?_⟩
    funext j
    have Member : (x j = true) ↔ j = i := by
      have := congrArg (fun S : Finset (Fin n) => j ∈ S) Equal
      exact Iff.of_eq (by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using this)
    cases Bit : x j <;> simp_all [SingleOne]
  · rintro ⟨i, rfl⟩
    exact OneCountSingleOne i

theorem CoordinateSwapSingleOne {n : ℕ} (i j : Fin n) :
    CoordinateSwap i j (SingleOne i) = SingleOne j := by
  funext k
  have Position : Equiv.swap i j k = i ↔ k = j := by
    constructor
    · intro Same
      have Back := congrArg (Equiv.swap i j) Same
      simpa using Back
    · rintro rfl
      simp
  simp only [CoordinateSwap, SingleOne, Position]

theorem SymmetricSingleOneMass {n : ℕ} (p : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw p) (i j : Fin n) :
    p (SingleOne i) = p (SingleOne j) := by
  have Equal := Symmetric i j (SingleOne i)
  rw [CoordinateSwapSingleOne] at Equal
  exact Equal.symm

theorem SymmetricSingleOneSubsetMass {n : ℕ} (p : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw p) (I : Finset (Fin n)) (i : Fin n) :
    p.toMeasure.real (I.image SingleOne : Set (Bits n)) =
      (I.card : ℝ) * (p (SingleOne i)).toReal := by
  classical
  rw [measureReal_def, PMF.toMeasure_apply_finset,
    ENNReal.toReal_sum (fun y _ => p.apply_ne_top y),
    Finset.sum_image (fun _ _ _ _ Eq => SingleOneInjective Eq)]
  have Terms : (∑ j ∈ I, (p (SingleOne j)).toReal) = ∑ _j ∈ I, (p (SingleOne i)).toReal := by
    apply Finset.sum_congr rfl
    intro j _
    rw [SymmetricSingleOneMass p Symmetric j i]
  rw [Terms, Finset.sum_const, nsmul_eq_mul]

theorem OneCountLevelEqSingleOneImage (n : ℕ) :
    {x : Bits n | OneMax x = 1} =
      (Finset.univ.image (SingleOne (n := n)) : Set (Bits n)) := by
  classical
  ext x
  simp only [Set.mem_ofPred_eq, OneCountEqOneIff, Finset.mem_coe, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, Eq⟩ => ⟨i, Eq.symm⟩, fun ⟨i, Eq⟩ => ⟨i, Eq.symm⟩⟩

theorem SymmetricOneCountLevelMass {n : ℕ} (p : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw p) (i : Fin n) :
    p.toMeasure.real {x | OneMax x = 1} = (n : ℝ) * (p (SingleOne i)).toReal := by
  rw [OneCountLevelEqSingleOneImage, SymmetricSingleOneSubsetMass p Symmetric _ i]
  simp

/-- Non-null conditioning is essential; the resulting atom is exactly 1/n. -/
theorem ConditionalSingleOneAtom {n : ℕ} (PositiveLength : 0 < n) (p : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw p) (Positive : p.toMeasure {x | OneMax x = 1} ≠ 0)
    (i : Fin n) :
    (cond p.toMeasure {x | OneMax x = 1}).real {SingleOne i} = 1 / (n : ℝ) := by
  classical
  have Mass := SymmetricOneCountLevelMass p Symmetric i
  have MassPositive : 0 < p.toMeasure.real {x | OneMax x = 1} :=
    ENNReal.toReal_pos Positive (measure_ne_top _ _)
  have AtomNonzero : (p (SingleOne i)).toReal ≠ 0 := by
    intro Zero
    rw [Mass, Zero, mul_zero] at MassPositive
    exact lt_irrefl 0 MassPositive
  rw [ConditionalSingletonReal, if_pos (show SingleOne i ∈ {x | OneMax x = 1} from
      OneCountSingleOne i), Mass]
  simp only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have Nnonzero : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr PositiveLength).ne'
  field_simp

/-- Every subset of coordinates has its cardinal fraction under the conditional law. -/
theorem ConditionalSingleOneSubset {n : ℕ} (PositiveLength : 0 < n) (p : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw p) (Positive : p.toMeasure {x | OneMax x = 1} ≠ 0)
    (I : Finset (Fin n)) :
    (cond p.toMeasure {x | OneMax x = 1}).real (I.image SingleOne : Set (Bits n)) =
      (I.card : ℝ) / (n : ℝ) := by
  classical
  rw [← sum_measureReal_singleton,
    Finset.sum_image (fun _ _ _ _ Eq => SingleOneInjective Eq)]
  simp_rw [ConditionalSingleOneAtom PositiveLength p Symmetric Positive]
  simp [nsmul_eq_mul, div_eq_mul_inv]

theorem UniformOneCountLevelPositive {n : ℕ} (PositiveLength : 0 < n) :
    (RLSInit n).toMeasure {x | OneMax x = 1} ≠ 0 := by
  let i : Fin n := ⟨0, PositiveLength⟩
  have AtomPositive : 0 < (RLSInit n).toMeasure {SingleOne i} := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), RLSInitProbability]
    exact ENNReal.inv_pos.mpr (by finiteness)
  exact (AtomPositive.trans_le (measure_mono (Set.singleton_subset_iff.mpr
    (OneCountSingleOne i)))).ne'

/-- Complete conditional state law, valid for any coordinate-symmetric initial marginal. -/
theorem ConditionalOneCountLawOfSymmetry {n : ℕ} (PositiveLength : 0 < n)
    (p : PMF (Bits n)) (Symmetric : CoordinateSymmetricLaw p)
    (Positive : p.toMeasure {x | OneMax x = 1} ≠ 0) :
    cond p.toMeasure {x | OneMax x = 1} =
      cond (RLSInit n).toMeasure {x | OneMax x = 1} := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro x
  by_cases AtLevel : OneMax x = 1
  · obtain ⟨i, rfl⟩ := (OneCountEqOneIff x).mp AtLevel
    rw [ConditionalSingleOneAtom PositiveLength p Symmetric Positive,
      ConditionalSingleOneAtom PositiveLength (RLSInit n) (UniformCoordinateSymmetric n)
        (UniformOneCountLevelPositive PositiveLength)]
  · rw [ConditionalSingletonReal, ConditionalSingletonReal]
    simp only [Set.mem_ofPred_eq, AtLevel, if_false, zero_div]

theorem PathConditionalOneCountLaw {n : ℕ} (PositiveLength : 0 < n)
    (w : Fin n → ℝ) (PositiveWeights : ∀ i, 0 < w i) (Initial : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw Initial) (t : ℕ)
    (Positive : (PathMeasure (RLSLinear.Step PositiveLength w) Initial)
      {Path | OneMax (Path t) = 1} ≠ 0) :
    (cond (PathMeasure (RLSLinear.Step PositiveLength w) Initial)
      {Path | OneMax (Path t) = 1}).map (fun Path => Path t) =
        cond (RLSInit n).toMeasure {x | OneMax x = 1} := by
  have Commutes := ConditionalMap (PathMeasure (RLSLinear.Step PositiveLength w) Initial)
    (fun Path => Path t) (measurable_pi_apply t) {x | OneMax x = 1}
    (Set.to_countable _).measurableSet
  rw [PathMeasureMarginal] at Commutes
  change (cond (PathMeasure (RLSLinear.Step PositiveLength w) Initial)
    {Path | OneMax (Path t) = 1}).map (fun Path => Path t) = _ at Commutes
  rw [Commutes]
  apply ConditionalOneCountLawOfSymmetry PositiveLength _
    (RunCoordinateSymmetric PositiveLength w PositiveWeights Initial Symmetric t)
  have Event := PathMeasureCoordinateEvent (RLSLinear.Step PositiveLength w) Initial t
    {x | OneMax x = 1}
  rw [← Event]
  exact Positive

theorem PathConditionalSingleOneSubset {n : ℕ} (PositiveLength : 0 < n)
    (w : Fin n → ℝ) (PositiveWeights : ∀ i, 0 < w i) (Initial : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw Initial) (t : ℕ)
    (Positive : (PathMeasure (RLSLinear.Step PositiveLength w) Initial)
      {Path | OneMax (Path t) = 1} ≠ 0) (I : Finset (Fin n)) :
    (cond (PathMeasure (RLSLinear.Step PositiveLength w) Initial)
      {Path | OneMax (Path t) = 1}).real {Path | Path t ∈ (I.image SingleOne : Set (Bits n))} =
        (I.card : ℝ) / (n : ℝ) := by
  have Law := PathConditionalOneCountLaw PositiveLength w PositiveWeights Initial Symmetric t Positive
  have Event := congrArg (fun μ : Measure (Bits n) => μ.real (I.image SingleOne : Set (Bits n))) Law
  rw [map_measureReal_apply (measurable_pi_apply t) (Set.toFinite _).measurableSet] at Event
  exact Event.trans (ConditionalSingleOneSubset PositiveLength _ (UniformCoordinateSymmetric n)
    (UniformOneCountLevelPositive PositiveLength) I)

def PrefixIndices {n : ℕ} (m : ℕ) (Within : m ≤ n) : Finset (Fin n) :=
  Finset.univ.image (Fin.castLE Within)

theorem PrefixIndicesCard {n : ℕ} (m : ℕ) (Within : m ≤ n) :
    (PrefixIndices m Within).card = m := by
  classical
  rw [PrefixIndices, Finset.card_image_of_injective _ (Fin.castLE_injective Within)]
  simp

theorem UniformPathConditionalPrefix {n : ℕ} (PositiveLength : 0 < n) (t m : ℕ)
    (Within : m ≤ n)
    (Positive : (PathMeasure (Step PositiveLength) (RLSInit n))
      {Path | OneMax (Path t) = 1} ≠ 0) :
    (cond (PathMeasure (Step PositiveLength) (RLSInit n))
      {Path | OneMax (Path t) = 1}).real
        {Path | Path t ∈ ((PrefixIndices m Within).image SingleOne : Set (Bits n))} =
          (m : ℝ) / (n : ℝ) := by
  have Probability := PathConditionalSingleOneSubset PositiveLength Weights WeightPositive
    (RLSInit n) (UniformCoordinateSymmetric n) t Positive (PrefixIndices m Within)
  rw [PrefixIndicesCard] at Probability
  exact Probability

theorem PrefixSingleOneScoreLower {n : ℕ} (m : ℕ) (Within : m ≤ n)
    (x : Bits n) (InPrefix : x ∈ ((PrefixIndices m Within).image SingleOne : Set (Bits n))) :
    (2 : ℝ) ^ (n - m) ≤ Score x := by
  classical
  obtain ⟨i, Member, rfl⟩ := Finset.mem_image.mp InPrefix
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp Member
  change (2 : ℝ) ^ (n - m) ≤ Score (fun k => decide (k = Fin.castLE Within j))
  rw [ScoreSingleOne, Weights]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  have Before : (j : ℕ) < m := j.isLt
  simp only [Fin.val_castLE]
  omega

/-- A true prefix event supplies a lower bound on the conditional fitness tail. -/
theorem UniformPathConditionalScoreThreshold {n : ℕ} (PositiveLength : 0 < n) (t m : ℕ)
    (Within : m ≤ n)
    (Positive : (PathMeasure (Step PositiveLength) (RLSInit n))
      {Path | OneMax (Path t) = 1} ≠ 0) :
    (m : ℝ) / (n : ℝ) ≤
      (cond (PathMeasure (Step PositiveLength) (RLSInit n))
        {Path | OneMax (Path t) = 1}).real {Path | (2 : ℝ) ^ (n - m) ≤ Score (Path t)} := by
  let _ : IsProbabilityMeasure (cond (PathMeasure (Step PositiveLength) (RLSInit n))
    {Path | OneMax (Path t) = 1}) := cond_isProbabilityMeasure Positive
  rw [← UniformPathConditionalPrefix PositiveLength t m Within Positive]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro Path Member
  exact PrefixSingleOneScoreLower m Within (Path t) Member

theorem UniformPathConditionalEvenHalf (k : ℕ) (PositiveLength : 0 < 2 * k) (t : ℕ)
    (Positive : (PathMeasure (Step PositiveLength) (RLSInit (2 * k)))
      {Path | OneMax (Path t) = 1} ≠ 0) :
    (1 / 2 : ℝ) ≤
      (cond (PathMeasure (Step PositiveLength) (RLSInit (2 * k)))
        {Path | OneMax (Path t) = 1}).real {Path | (2 : ℝ) ^ k ≤ Score (Path t)} := by
  have Bound := UniformPathConditionalScoreThreshold PositiveLength t k (by omega) Positive
  have Kpositive : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have Ratio : (k : ℝ) / ((2 * k : ℕ) : ℝ) = 1 / 2 := by
    push_cast
    field_simp
  rw [Ratio, show 2 * k - k = k by omega] at Bound
  exact Bound

/-- Odd lengths use ceil-half positions and the integer floor-half exponent. -/
theorem UniformPathConditionalRoundedHalf {n : ℕ} (PositiveLength : 0 < n) (t : ℕ)
    (Positive : (PathMeasure (Step PositiveLength) (RLSInit n))
      {Path | OneMax (Path t) = 1} ≠ 0) :
    (1 / 2 : ℝ) ≤
      (cond (PathMeasure (Step PositiveLength) (RLSInit n))
        {Path | OneMax (Path t) = 1}).real {Path | (2 : ℝ) ^ (n / 2) ≤ Score (Path t)} := by
  have Bound := UniformPathConditionalScoreThreshold PositiveLength t ((n + 1) / 2)
    (by omega) Positive
  rw [show n - (n + 1) / 2 = n / 2 by omega] at Bound
  apply le_trans _ Bound
  apply (le_div_iff₀ (Nat.cast_pos.mpr PositiveLength)).mpr
  have Cover : n ≤ 2 * ((n + 1) / 2) := by omega
  have CastCover : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast Cover
  linarith

end
end ECTheoryLib.Analysis.RLSBinVal

