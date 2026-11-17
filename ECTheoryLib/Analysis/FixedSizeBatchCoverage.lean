import ECTheoryLib.Probability.Sampling.UniformSubsetUnion
import ECTheoryLib.Operators.Mutation.FixedSize
import ECTheoryLib.Operators.Sampling.Batch
import ECTheoryLib.SearchSpaces.BitPopulation

/-!
# Coordinate coverage in an actual mutation offspring batch

Reuse the existing independent sampling operator with fixed-size mutation
from a fixed parent. The complete union of changed coordinates has the
subset-union PMF; exact means and both finite-size tails follow. Offspring
order and duplicates are retained in the underlying batch. The statistic
counts distinct touched coordinates, not total flips or selected survivors.
-/

namespace ECTheoryLib.Analysis.FixedSizeBatchCoverage
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Operators.Selection
noncomputable section

/-- Distinct changed coordinates of an actual proposed child. -/
def ChangedPositions {n : ℕ} (Parent Child : Bits n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Child i≠Parent i)

/-- Coordinates touched by at least one offspring. Repeated offspring and
repeated changes are counted only once. -/
def CoveredPositions {n : ℕ} (Parent : Bits n) : List (Bits n) → Finset (Fin n)
  | [] => ∅
  | Child::Rest => ChangedPositions Parent Child∪CoveredPositions Parent Rest

theorem ChangedPositionsFlip {n : ℕ} (Parent : Bits n) (U : Finset (Fin n)) :
    ChangedPositions Parent (FlipBitSubset Parent U)=U := by
  ext i
  simp [ChangedPositions,FlipBitSubsetChanged]

theorem MutationPositionsLaw {n k : ℕ} (Admissible : k≤n) (Parent : Bits n) :
    (FixedSizeBitMutation Admissible Parent).map (ChangedPositions Parent)=UniformSubset.Law n k Admissible := by
  rw [FixedSizeBitMutation,PMF.map_comp]
  have FunctionIdentity : (ChangedPositions Parent) ∘ (FlipBitSubset Parent)=id := by
    funext U
    exact ChangedPositionsFlip Parent U
  rw [FunctionIdentity,PMF.map_id]

/-- Reuse the existing independent offspring batch. Its complete coverage
distribution equals the uniform-subset union law, not merely its mean. -/
theorem BatchCoverageLaw {n k : ℕ} (Admissible : k≤n) (Parent : Bits n) (BatchSize : ℕ) :
    (IndependentSamples (FixedSizeBitMutation Admissible Parent) BatchSize).map (CoveredPositions Parent)=
      UniformSubsetUnion.Law (fun _j : Fin BatchSize => k) (fun _ => Admissible) := by
  induction BatchSize with
  | zero => simp [IndependentSamples,CoveredPositions,UniformSubsetUnion.Law,RandomSubset.FamilyLaw,PMF.pure_map]
  | succ b IH =>
    let P := FixedSizeBitMutation Admissible Parent
    let Q := UniformSubset.Law n k Admissible
    let R := UniformSubsetUnion.Law (fun _j : Fin b => k) (fun _ => Admissible)
    calc
      _ = P.bind (fun Child =>
          ((IndependentSamples P b).map (CoveredPositions Parent)).map
            (fun U => ChangedPositions Parent Child∪U)) := by
        rw [IndependentSamples,PMF.map_bind]
        apply congrArg (PMF.bind P)
        funext Child
        rw [PMF.map_comp,PMF.map_comp]
        rfl
      _ = P.bind (fun Child => R.map (fun U => ChangedPositions Parent Child∪U)) := by rw [IH]
      _ = (P.map (ChangedPositions Parent)).bind (fun V => R.map (fun U => V∪U)) := by rw [PMF.bind_map]; rfl
      _ = RandomSubset.UnionLaw Q R := by rw [MutationPositionsLaw]; rfl
      _ = _ := by rw [RandomSubset.UnionLawComm]; rfl

theorem ExpectedCoveredPositions {n k : ℕ} (Admissible : k≤n) (Parent : Bits n) (BatchSize : ℕ) :
    (∫ Children, ((CoveredPositions Parent Children).card : ℝ)
      ∂(IndependentSamples (FixedSizeBitMutation Admissible Parent) BatchSize).toMeasure)=
        (n : ℝ)*(1-(1-(k : ℝ)/(n : ℝ))^BatchSize) := by
  have Law : HasLaw (CoveredPositions Parent)
      (UniformSubsetUnion.Law (fun _j : Fin BatchSize => k) (fun _ => Admissible)).toMeasure
      (IndependentSamples (FixedSizeBitMutation Admissible Parent) BatchSize).toMeasure := by
    refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
    rw [PMF.toMeasure_map _ _ (measurable_of_countable _),BatchCoverageLaw]
  have Integral := Law.integral_comp (f := fun U => (U.card : ℝ))
    (measurable_of_finite _).aestronglyMeasurable
  rw [UniformSubsetUnion.ExpectedCard] at Integral
  simpa only [Function.comp_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using Integral

theorem CoveredPositionsFiniteUpperTail {n k : ℕ} (Admissible : k≤n) (Parent : Bits n)
    (BatchSize : ℕ) (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentSamples (FixedSizeBitMutation Admissible Parent) BatchSize).toMeasure.real
      {Children | (1+d)*((n : ℝ)*(1-(1-(k : ℝ)/(n : ℝ))^BatchSize))≤
        ((CoveredPositions Parent Children).card : ℝ)}≤
      FiniteChernoffUpperBound n ((n : ℝ)*(1-(1-(k : ℝ)/(n : ℝ))^BatchSize)) d := by
  have Bound := UniformSubsetUnion.CardFiniteUpperTail (fun _j : Fin BatchSize => k)
    (fun _ => Admissible) d Nonnegative
  rw [← BatchCoverageLaw Admissible Parent BatchSize,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    map_measureReal_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)] at Bound
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Set.preimage_ofPred_eq] using Bound

theorem CoveredPositionsFiniteLowerTail {n k : ℕ} (Admissible : k≤n) (Parent : Bits n)
    (BatchSize : ℕ) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (IndependentSamples (FixedSizeBitMutation Admissible Parent) BatchSize).toMeasure.real
      {Children | ((CoveredPositions Parent Children).card : ℝ)≤
        (1-d)*((n : ℝ)*(1-(1-(k : ℝ)/(n : ℝ))^BatchSize))}≤
      FiniteChernoffLowerBound n ((n : ℝ)*(1-(1-(k : ℝ)/(n : ℝ))^BatchSize)) d := by
  have Bound := UniformSubsetUnion.CardFiniteLowerTail (fun _j : Fin BatchSize => k)
    (fun _ => Admissible) d InUnit
  rw [← BatchCoverageLaw Admissible Parent BatchSize,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    map_measureReal_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)] at Bound
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Set.preimage_ofPred_eq] using Bound

end
end ECTheoryLib.Analysis.FixedSizeBatchCoverage
