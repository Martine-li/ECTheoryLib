import ECTheoryLib.Tools.Drift.GeometricAdditiveTail
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.MutationTailBounds
import ECTheoryLib.Probability.Processes.HistoryConditional

/-!
# A geometric-jump half-progress tail for the actual standard OneMax EA

The length is 2*m with m>0, and initialization is the pure all-false string.
The target is zero count at most m. Time counts transitions after initialization.
The actual mutation MGF and selected-kernel drift are lifted to the complete
coordinate history; no independence of selected increments is assumed.
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- A strict half-progress tail for the actual standard (1+1) EA, started from
the all-false string of length `2*m`. Equality in the time condition is retained.
Here the geometric radius is `log(3/2)` and its absolute-moment bound is `6*e`;
they are written using the shared definitions to expose the exact core call. -/
theorem HalfProgressGeometricUpperTail (m : ℕ) (PositiveM : 0 < m)
    (t : ℕ) (PositiveTime : 0 < t)
    (LateEnough : (m : ℝ) ≤ (t : ℝ) / (2 * Real.exp 1)) :
    (PathMeasure (Step (Nat.mul_pos (by decide : 0 < 2) PositiveM))
      (PMF.pure (fun _ : Fin (2*m) => false)))
      {Path | (t : WithTop ℕ) <
        FirstHittingTime (fun x : Bits (2*m) => Potential x ≤ (m : ℝ)) Path} ≤
      ENNReal.ofReal (Real.exp (-min
        (GeometricJumpMomentRadius 1 * ((t : ℝ) / (2 * Real.exp 1) - (m : ℝ)) / 4)
        ((GeometricJumpMomentRadius 1) ^ 2 *
          ((t : ℝ) / (2 * Real.exp 1) - (m : ℝ)) ^ 2 /
          (32 * GeometricJumpMomentBound 1 (Real.exp 1) * (t : ℝ))))) := by
  classical
  let PositiveLength : 0 < 2*m := Nat.mul_pos (by decide) PositiveM
  let InitialState : Bits (2*m) := fun _ => false
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits (2*m)) → ℝ := fun j Path => Potential (Path j)
  let F := Filtration.piLE (X := fun _ : ℕ => Bits (2*m))
  let S : Finset ℝ := Finset.univ.image (Potential (n := 2*m))
  have AdaptedX : Adapted F X := PathPotentialAdapted Potential
  have Values (j : ℕ) (Path : ℕ → Bits (2*m)) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have PositiveMReal : (0 : ℝ) < m := Nat.cast_pos.mpr PositiveM
  have InitialAbove : (m : ℝ) < (2*m : ℕ) := by
    push_cast
    linarith
  have FixedInitial : ∀ᵐ Path ∂μ, X 0 Path = (2*m : ℕ) := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState]
      with Path Initial
    change Potential (Path 0) = (2*m : ℕ)
    rw [Initial]
    simp [InitialState, Potential, OneMax.ZeroPotential,
      Problems.OneMax.ZeroCount, ECTheoryLib.OneMax]
  have JumpTail (j k : ℕ) : ∀ᵐ Path ∂μ, (m : ℝ) < X j Path →
      (μ[({u | (k : ℝ) ≤ |X (j+1) u - X j u|}).indicator
        (fun _ => (1 : ℝ)) | F j]) Path ≤ Real.exp 1 / (1 + (1 : ℝ)) ^ k := by
    have Conditional := PathMeasureStateConditionalExpectation
      (Step PositiveLength) (PMF.pure InitialState) j
      (fun Parent Next => ({y | (k : ℝ) ≤ |Potential y - Potential Parent|}).indicator
        (fun _ => (1 : ℝ)) Next)
    filter_upwards [Conditional] with Path Equal
    intro _Above
    change (μ[({u | (k : ℝ) ≤ |X (j+1) u - X j u|}).indicator
        (fun _ => (1 : ℝ)) | F j]) Path =
      ∫ Next, ({y | (k : ℝ) ≤ |Potential y - Potential (Path j)|}).indicator
        (fun _ => (1 : ℝ)) Next ∂(Step PositiveLength (Path j)).toMeasure at Equal
    rw [Equal, integral_indicator_const _ ((Set.to_countable _).measurableSet),
      smul_eq_mul, mul_one]
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
      StepPotentialGeometricTail PositiveLength (Path j) k
  have Drift (j : ℕ) : ∀ᵐ Path ∂μ, (m : ℝ) < X j Path →
      1 / (2 * Real.exp 1) ≤ (μ[fun u => X j u - X (j+1) u | F j]) Path := by
    have Conditional := PathMeasureStateConditionalExpectation
      (Step PositiveLength) (PMF.pure InitialState) j
      (fun Parent Next => Potential Parent - Potential Next)
    filter_upwards [Conditional] with Path Equal
    intro Above
    change (μ[fun u => X j u - X (j+1) u | F j]) Path =
      ∫ Next, Potential (Path j) - Potential Next
        ∂(Step PositiveLength (Path j)).toMeasure at Equal
    rw [Equal]
    exact HalfProgressAdditiveDrift m PositiveM (Path j) Above
  have Distance : ((2*m : ℕ) : ℝ) - (m : ℝ) = (m : ℝ) := by
    push_cast
    ring
  have DriftTime : (1 / (2 * Real.exp 1)) * (t : ℝ) =
      (t : ℝ) / (2 * Real.exp 1) := by ring
  have Late : ((2*m : ℕ) : ℝ) - (m : ℝ) ≤
      (1 / (2 * Real.exp 1)) * (t : ℝ) := by
    rw [Distance, DriftTime]
    exact LateEnough
  have Bound := GeometricAdditiveDriftUpperTailOfCondExp μ X F AdaptedX S
    (m : ℝ) (2*m : ℕ) 1 (1 / (2 * Real.exp 1)) (Real.exp 1)
    (by norm_num) (by positivity) (Real.one_le_exp (by norm_num))
    Values InitialAbove FixedInitial JumpTail Drift t PositiveTime Late
  rw [Distance, DriftTime] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.EAOneMax
