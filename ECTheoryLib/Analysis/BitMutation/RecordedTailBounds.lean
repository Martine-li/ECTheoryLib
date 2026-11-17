import ECTheoryLib.Operators.Mutation.Recorded
import ECTheoryLib.Probability.Concentration.MultiroundFailureThreshold
import ECTheoryLib.Probability.Processes.EventUnionBound
import ECTheoryLib.Analysis.BitMutation.HammingTailBounds
import ECTheoryLib.Probability.PMF.BoundedPMF
import ECTheoryLib.Problems.TargetOneMax
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Raw-mutation tail bounds for a recorded process

The exact one-step Hamming law is the mixture of actual mutation tails under
the parent policy. Its uniform bound follows from MutationHammingFailureThreshold.
On the same countable-memory recorded trajectory, the first T raw-call events
then have union probability at most q. This retains positive n, 0<alpha<=n,
positive T including 1, the original q<=exp(-alpha*exp(1/e))/T, and the repaired
threshold at q/T. Memory may encode history; the update is deterministic.
No independence of calls or named selected-state joint-law equality is assumed.
-/

namespace ECTheoryLib.Analysis.BitMutation

open MeasureTheory Set ECTheoryLib ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax
open ECTheoryLib.Probability.PowerTailThreshold
open scoped unitInterval

noncomputable section

/-- Exact probability mixture for the actual recorded Hamming event. The memory
may be countably infinite; only the parent/candidate spaces are finite. -/
theorem RecordedMutationStepTailProbability {S : Type*} {n : ℕ}
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (p : I) (Parents : S → PMF (Bits n)) (Update : S → Bits n → Bits n → S)
    (z : RecordedMutationState S n) (k : ℝ) :
    (RecordedMutationStep p Parents Update z).toMeasure.real
      {w | k ≤ (Hamming w.2.1 w.2.2 : ℝ)} =
      ∫ Parent, (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) Parent).toMeasure.real
          {Candidate | k ≤ (Hamming Parent Candidate : ℝ)} ∂(Parents z.1).toMeasure := by
  classical
  let C : Set (RecordedMutationState S n) := {w | k ≤ (Hamming w.2.1 w.2.2 : ℝ)}
  have MeasurableC : MeasurableSet C := (Set.to_countable C).measurableSet
  have IndicatorBound : ∀ w : RecordedMutationState S n,
      ‖C.indicator (fun _ => (1 : ℝ)) w‖ ≤ 1 := by
    intro w
    by_cases InC : w ∈ C <;> simp [Set.indicator, InC]
  change (RecordedMutationStep p Parents Update z).toMeasure.real C = _
  rw [← integral_indicator_one MeasurableC]
  unfold RecordedMutationStep
  refine (PMFIntegralBindOfBounded (Parents z.1) _ _ 1 IndicatorBound).trans ?_
  apply integral_congr_ae
  exact ae_of_all _ (fun Parent => by
    refine (PMFIntegralMapCountable _ _ _).trans ?_
    change (∫ Candidate,
      ({y : Bits n | k ≤ (Hamming Parent y : ℝ)}.indicator (fun _ => (1 : ℝ))) Candidate
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) Parent).toMeasure) = _
    exact integral_indicator_one (Set.to_countable _).measurableSet)

/-- Uniform one-step bound derived from the existing actual mutation theorem,
not supplied as a hypothesis. Every parent policy and memory update is allowed.
For (c), substitute q/T after proving its original single-call range. -/
theorem RecordedMutationStepFailureThreshold {S : Type*} {n : ℕ}
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (PositiveLength : 0 < n) (Parents : S → PMF (Bits n))
    (Update : S → Bits n → Bits n → S) (z : RecordedMutationState S n)
    (α q k : ℝ) (PositiveAlpha : 0 < α) (AlphaAtMostLength : α ≤ (n : ℝ))
    (PositiveQ : 0 < q)
    (SourceRange : q ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)))
    (LargeThreshold : failureThreshold α q ≤ k) :
    let p : I := ⟨α / (n : ℝ),
      ⟨div_nonneg PositiveAlpha.le (Nat.cast_nonneg n),
        (div_le_one (Nat.cast_pos.mpr PositiveLength)).mpr AlphaAtMostLength⟩⟩
    (RecordedMutationStep p Parents Update z).toMeasure.real
      {w | k ≤ (Hamming w.2.1 w.2.2 : ℝ)} ≤ q := by
  let p : I := ⟨α / (n : ℝ),
    ⟨div_nonneg PositiveAlpha.le (Nat.cast_nonneg n),
      (div_le_one (Nat.cast_pos.mpr PositiveLength)).mpr AlphaAtMostLength⟩⟩
  change (RecordedMutationStep p Parents Update z).toMeasure.real
    {w | k ≤ (Hamming w.2.1 w.2.2 : ℝ)} ≤ q
  rw [RecordedMutationStepTailProbability]
  have ParentBound (Parent : Bits n) :
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) Parent).toMeasure.real
          {Candidate | k ≤ (Hamming Parent Candidate : ℝ)} ≤ q :=
    MutationHammingFailureThreshold PositiveLength Parent α q k PositiveAlpha
      AlphaAtMostLength PositiveQ SourceRange LargeThreshold
  have AverageBound := integral_mono (μ := (Parents z.1).toMeasure)
    Integrable.of_finite (integrable_const q) ParentBound
  simpa only [integral_const, probReal_univ, one_smul] using AverageBound

/-- The first T actual mutation calls in the recorded process have a raw
Hamming jump at least k with probability at most q. Coordinate zero contains
only a dummy record and is excluded. The positive-natural horizon includes 1. -/
theorem RecordedMutationMultiroundFailureThreshold {S : Type*} {n : ℕ}
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (PositiveLength : 0 < n) (Parents : S → PMF (Bits n))
    (Update : S → Bits n → Bits n → S) (Initial : PMF S)
    (Dummy : Bits n × Bits n) (α q k : ℝ) (T : ℕ)
    (PositiveAlpha : 0 < α) (AlphaAtMostLength : α ≤ (n : ℝ))
    (PositiveT : 0 < T) (PositiveQ : 0 < q)
    (SourceRange : q ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)) / (T : ℝ))
    (LargeThreshold : failureThreshold α (q / (T : ℝ)) ≤ k) :
    let p : I := ⟨α / (n : ℝ),
      ⟨div_nonneg PositiveAlpha.le (Nat.cast_nonneg n),
        (div_le_one (Nat.cast_pos.mpr PositiveLength)).mpr AlphaAtMostLength⟩⟩
    (PathMeasure (RecordedMutationStep p Parents Update)
      (RecordedMutationInitial Initial Dummy)).real
        (⋃ t ∈ Finset.range T,
          {path | k ≤ (Hamming (path (t + 1)).2.1 (path (t + 1)).2.2 : ℝ)}) ≤ q := by
  let p : I := ⟨α / (n : ℝ),
    ⟨div_nonneg PositiveAlpha.le (Nat.cast_nonneg n),
      (div_le_one (Nat.cast_pos.mpr PositiveLength)).mpr AlphaAtMostLength⟩⟩
  let C : Set (RecordedMutationState S n) := {w | k ≤ (Hamming w.2.1 w.2.2 : ℝ)}
  have Budget := perCallBudget_originalRange α q T PositiveT PositiveQ SourceRange
  have LocalBound (z : RecordedMutationState S n) :
      (RecordedMutationStep p Parents Update z).toMeasure.real C ≤ q / (T : ℝ) :=
    RecordedMutationStepFailureThreshold PositiveLength Parents Update z
      α (q / (T : ℝ)) k PositiveAlpha AlphaAtMostLength Budget.1 Budget.2 LargeThreshold
  have PositiveRealT : 0 < (T : ℝ) := Nat.cast_pos.mpr PositiveT
  change (PathMeasure (RecordedMutationStep p Parents Update)
    (RecordedMutationInitial Initial Dummy)).real
      (⋃ t ∈ Finset.range T, {path | path (t + 1) ∈ C}) ≤ q
  calc
    _ ≤ (T : ℝ) * (q / (T : ℝ)) :=
      PathNextEventUnionBound (RecordedMutationStep p Parents Update)
        (RecordedMutationInitial Initial Dummy) C T (q / (T : ℝ)) Budget.1.le LocalBound
    _ = q := mul_div_cancel₀ q PositiveRealT.ne'

end
end ECTheoryLib.Analysis.BitMutation
