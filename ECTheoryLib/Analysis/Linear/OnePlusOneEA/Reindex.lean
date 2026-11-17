import ECTheoryLib.Analysis.Linear.OnePlusOneEA.RankPotential
import ECTheoryLib.Operators.Mutation.IndependentBitCoupling
import Mathlib.Data.Fin.Tuple.Sort

/-! Exact coordinate transport for the original weak-minimizing EA.
No sortedness or sign premise is needed to commute selection with reindexing.
This transports local drift, without changing original paths. -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open MeasureTheory ECTheoryLib.Problems.Linear
noncomputable section

theorem ScoreReindex {n : ℕ} (Weights : Fin n → ℝ) (x : Bits n)
    (e : Equiv.Perm (Fin n)) :
    Score (fun i => Weights (e i)) (ReindexBits e x) = Score Weights x := by
  unfold Score ReindexBits
  exact Equiv.sum_comp e (fun i : Fin n => Weights i*(if x i then (1 : ℝ) else 0))

theorem MinimizingSelectionReindex {n : ℕ} (Weights : Fin n → ℝ)
    (Parent Candidate : Bits n) (e : Equiv.Perm (Fin n)) :
    ReindexBits e (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent Candidate) =
      ElitistSelect (Problems.MinNotWorse (Score (fun i => Weights (e i))))
        (ReindexBits e Parent) (ReindexBits e Candidate) := by
  by_cases Accepted : Score Weights Candidate ≤ Score Weights Parent
  · have Reindexed : Score (fun i => Weights (e i)) (ReindexBits e Candidate) ≤
        Score (fun i => Weights (e i)) (ReindexBits e Parent) := by
      simpa only [ScoreReindex] using Accepted
    rw [ElitistSelectAccept (Problems.MinNotWorse (Score Weights)) Parent Candidate Accepted,
      ElitistSelectAccept (Problems.MinNotWorse (Score (fun i => Weights (e i))))
        (ReindexBits e Parent) (ReindexBits e Candidate) Reindexed]
  · have Reindexed : ¬ Score (fun i => Weights (e i)) (ReindexBits e Candidate) ≤
        Score (fun i => Weights (e i)) (ReindexBits e Parent) := by
      simpa only [ScoreReindex] using Accepted
    rw [ElitistSelectReject (Problems.MinNotWorse (Score Weights)) Parent Candidate Accepted,
      ElitistSelectReject (Problems.MinNotWorse (Score (fun i => Weights (e i))))
        (ReindexBits e Parent) (ReindexBits e Candidate) Reindexed]

theorem StandardMutationReindex {n : ℕ} (PositiveLength : 0 < n)
    (Parent : Bits n) (e : Equiv.Perm (Fin n)) :
    (StandardBitMutation PositiveLength Parent).toMeasure.map (ReindexBits e) =
      (StandardBitMutation PositiveLength (ReindexBits e Parent)).toMeasure :=
  IndependentBitMutationReindex _ _ Parent e

theorem StepReindex {n : ℕ} (PositiveLength : 0 < n) (Weights : Fin n → ℝ)
    (Parent : Bits n) (e : Equiv.Perm (Fin n)) :
    (Step PositiveLength Weights Parent).toMeasure.map (ReindexBits e) =
      (Step PositiveLength (fun i => Weights (e i)) (ReindexBits e Parent)).toMeasure := by
  let f := ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent
  let g := ElitistSelect (Problems.MinNotWorse (Score (fun i => Weights (e i)))) (ReindexBits e Parent)
  have KernelLaw (w : Fin n → ℝ) (x : Bits n) :
      (Step PositiveLength w x).toMeasure =
        (StandardBitMutation PositiveLength x).toMeasure.map
          (ElitistSelect (Problems.MinNotWorse (Score w)) x) := by
    exact (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm
  have Commutes : ReindexBits e ∘ f = g ∘ ReindexBits e := by
    funext Candidate
    exact MinimizingSelectionReindex Weights Parent Candidate e
  calc
    (Step PositiveLength Weights Parent).toMeasure.map (ReindexBits e) =
        ((StandardBitMutation PositiveLength Parent).toMeasure.map f).map (ReindexBits e) := by
      rw [KernelLaw]
    _ = (StandardBitMutation PositiveLength Parent).toMeasure.map (ReindexBits e ∘ f) :=
      Measure.map_map (measurable_of_finite _) (measurable_of_finite _)
    _ = (StandardBitMutation PositiveLength Parent).toMeasure.map (g ∘ ReindexBits e) := by
      rw [Commutes]
    _ = ((StandardBitMutation PositiveLength Parent).toMeasure.map (ReindexBits e)).map g :=
      (Measure.map_map (measurable_of_finite _) (measurable_of_finite _)).symm
    _ = (StandardBitMutation PositiveLength (ReindexBits e Parent)).toMeasure.map g := by
      rw [StandardMutationReindex]
    _ = (Step PositiveLength (fun i => Weights (e i)) (ReindexBits e Parent)).toMeasure :=
      (KernelLaw _ _).symm

theorem StepReindexIntegral {n : ℕ} (PositiveLength : 0 < n) (Weights : Fin n → ℝ)
    (Parent : Bits n) (e : Equiv.Perm (Fin n)) (F : Bits n → ℝ) :
    (∫ Next, F (ReindexBits e Next) ∂(Step PositiveLength Weights Parent).toMeasure) =
      ∫ Next, F Next
        ∂(Step PositiveLength (fun i => Weights (e i)) (ReindexBits e Parent)).toMeasure := by
  rw [← StepReindex PositiveLength Weights Parent e,
    integral_map_of_stronglyMeasurable (measurable_of_finite _)
      (measurable_of_finite _).stronglyMeasurable]

theorem ReindexedRankZeroIffScore {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ i, 0 < Weights i) (x : Bits n) (e : Equiv.Perm (Fin n)) :
    RankPotential (ReindexBits e x) = 0 ↔ Score Weights x = 0 := by
  rw [← ScoreReindex Weights x e]
  exact RankPotentialZeroIffScore (fun i => Weights (e i)) (fun i => Positive (e i)) _

/-- Canonical rank potential on original coordinates. Mathlib sorts indexed
weights by a permutation, retaining every coordinate even when weights tie. -/
def SortedRankPotential {n : ℕ} (Weights : Fin n → ℝ) (x : Bits n) : ℝ :=
  RankPotential (ReindexBits (Tuple.sort Weights) x)

theorem SortedRankPotentialZeroIffScore {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ i, 0 < Weights i) (x : Bits n) :
    SortedRankPotential Weights x = 0 ↔ Score Weights x = 0 :=
  ReindexedRankZeroIffScore Weights Positive x (Tuple.sort Weights)

theorem SortedRankPotentialInRange {n : ℕ} (Weights : Fin n → ℝ) (x : Bits n) :
    SortedRankPotential Weights x ∈ RankRange n :=
  RankPotentialInRange (ReindexBits (Tuple.sort Weights) x)

theorem SortedRankPotentialGap {n : ℕ} (Weights : Fin n → ℝ) (x : Bits n) :
    SortedRankPotential Weights x = 0 ∨ 1 ≤ SortedRankPotential Weights x :=
  RankPotentialGap (ReindexBits (Tuple.sort Weights) x)

theorem SortedRankPotentialNonnegative {n : ℕ} (Weights : Fin n → ℝ) (x : Bits n) :
    0 ≤ SortedRankPotential Weights x :=
  RankPotentialNonnegative (ReindexBits (Tuple.sort Weights) x)

theorem SortedRankPotentialLeTwoN {n : ℕ} (Weights : Fin n → ℝ) (x : Bits n) :
    SortedRankPotential Weights x ≤ 2*(n : ℝ) :=
  RankPotentialLeTwoN (ReindexBits (Tuple.sort Weights) x)

end
end ECTheoryLib.Analysis.EALinearMinimization

