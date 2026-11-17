import ECTheoryLib.Analysis.Linear.RLS.PositiveWeights
import ECTheoryLib.Probability.Processes.PathMarginal

/-!
Coordinate symmetry of the actual positive-weight, one-bit minimization kernel.
Weights need not be equal; this does not assert invariance of the objective.
-/
namespace ECTheoryLib.Analysis.RLSLinear
open MeasureTheory ECTheoryLib.Probability
noncomputable section

def CoordinateSwap {n : ℕ} (i j : Fin n) (x : Bits n) : Bits n :=
  fun k => x (Equiv.swap i j k)

theorem CoordinateSwapInvolutive {n : ℕ} (i j : Fin n) :
    Function.Involutive (CoordinateSwap i j) := by
  intro x
  funext k
  simp [CoordinateSwap]

def CoordinateSymmetricLaw {n : ℕ} (p : PMF (Bits n)) : Prop :=
  ∀ (i j : Fin n) (x : Bits n), p (CoordinateSwap i j x) = p x

/-- Strict positivity turns the actual selected update into setting the chosen bit to zero. -/
theorem UpdateEqSetZero {n : ℕ} (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i)
    (x : Bits n) (k : Fin n) :
    RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score w)) x k = Function.update x k false := by
  cases Bit : x k with
  | false =>
    rw [UpdateAtZero w Positive x k Bit]
    simp only [← Bit, Function.update_eq_self]
  | true =>
    rw [UpdateAtOne w Positive x k Bit]
    funext l
    by_cases Equal : l = k
    · subst l
      simp [OnebitMutationAt, Bit]
    · rw [OnebitMutationAway x k l Equal, Function.update_of_ne Equal]

theorem CoordinateSwapSetZero {n : ℕ} (i j k : Fin n) (x : Bits n) :
    CoordinateSwap i j (Function.update x k false) =
      Function.update (CoordinateSwap i j x) (Equiv.swap i j k) false := by
  funext l
  by_cases Equal : l = Equiv.swap i j k
  · subst l
    simp [CoordinateSwap]
  · have Different : Equiv.swap i j l ≠ k := by
      intro Same
      apply Equal
      have Back := congrArg (Equiv.swap i j) Same
      simpa using Back
    simp only [CoordinateSwap, Function.update_of_ne Equal, Function.update_of_ne Different]

theorem UpdateCoordinateSwap {n : ℕ} (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i)
    (i j k : Fin n) (x : Bits n) :
    RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score w)) (CoordinateSwap i j x)
        (Equiv.swap i j k) =
      CoordinateSwap i j (RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score w)) x k) := by
  rw [UpdateEqSetZero w Positive, UpdateEqSetZero w Positive, CoordinateSwapSetZero]

theorem StepCoordinateSwap {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (i j : Fin n) (x y : Bits n) :
    Step PositiveLength w (CoordinateSwap i j x) (CoordinateSwap i j y) =
      Step PositiveLength w x y := by
  classical
  unfold Step
  rw [RLSStepProbability, RLSStepProbability]
  have Reindex := (Equiv.swap i j).bijective.sum_comp
    (fun k => if RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score w))
      (CoordinateSwap i j x) k = CoordinateSwap i j y then (n : ENNReal)⁻¹ else 0)
  rw [← Reindex]
  apply Finset.sum_congr rfl
  intro k _
  rw [UpdateCoordinateSwap w Positive]
  simp only [(CoordinateSwapInvolutive i j).injective.eq_iff]

theorem StepPreservesCoordinateSymmetry {n : ℕ} (PositiveLength : 0 < n)
    (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i) (p : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw p) :
    CoordinateSymmetricLaw (p.bind (Step PositiveLength w)) := by
  intro i j y
  rw [PMF.bind_apply, PMF.bind_apply, tsum_fintype, tsum_fintype]
  have Reindex := (CoordinateSwapInvolutive i j).bijective.sum_comp
    (fun x => p x * Step PositiveLength w x (CoordinateSwap i j y))
  rw [← Reindex]
  apply Finset.sum_congr rfl
  intro x _
  rw [Symmetric i j x, StepCoordinateSwap PositiveLength w Positive]

theorem UniformCoordinateSymmetric (n : ℕ) : CoordinateSymmetricLaw (RLSInit n) := by
  intro i j x
  rw [RLSInitProbability, RLSInitProbability]

theorem RunCoordinateSymmetric {n : ℕ} (PositiveLength : 0 < n)
    (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw Initial) (t : ℕ) :
    CoordinateSymmetricLaw (Evolve (Step PositiveLength w) Initial t) := by
  induction t with
  | zero => exact Symmetric
  | succ t Before => exact StepPreservesCoordinateSymmetry PositiveLength w Positive _ Before

theorem UniformRunCoordinateSymmetric {n : ℕ} (PositiveLength : 0 < n)
    (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i) (t : ℕ) :
    CoordinateSymmetricLaw (Evolve (Step PositiveLength w) (RLSInit n) t) :=
  RunCoordinateSymmetric PositiveLength w Positive _ (UniformCoordinateSymmetric n) t

theorem PathCoordinateSwapMass {n : ℕ} (PositiveLength : 0 < n)
    (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n))
    (Symmetric : CoordinateSymmetricLaw Initial) (t : ℕ) (i j : Fin n) (x : Bits n) :
    (PathMeasure (Step PositiveLength w) Initial) {Path | Path t = CoordinateSwap i j x} =
      (PathMeasure (Step PositiveLength w) Initial) {Path | Path t = x} := by
  have Left := PathMeasureCoordinateEvent (Step PositiveLength w) Initial t
    ({CoordinateSwap i j x} : Set (Bits n))
  have Right := PathMeasureCoordinateEvent (Step PositiveLength w) Initial t
    ({x} : Set (Bits n))
  simp only [Set.mem_singleton_iff] at Left Right
  rw [Left, Right, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact RunCoordinateSymmetric PositiveLength w Positive Initial Symmetric t i j x

end
end ECTheoryLib.Analysis.RLSLinear

