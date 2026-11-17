import ECTheoryLib.Tools.Drift.GeometricAdditiveLowerTail
import ECTheoryLib.Analysis.OneMax.RLS.StochasticProgress
import ECTheoryLib.Analysis.OneMax.RLS.UniformRuntimeBound
import ECTheoryLib.Probability.Processes.HistoryConditional
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative
import Mathlib.Tactic.IntervalCases

/-!
# Actual RLS calls to the geometric-jump lower tail

All conditional premises follow from the original transition and trajectory
law. The sharp prefactor one uses binary progress and its actual conditional
success probability; bounded unit jumps alone would give prefactor two.
Time counts mutation iterations after initialization.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- Exact expected progress conditioned on the full actual RLS history. -/
theorem PathConditionalDecreaseMean {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (j : ℕ) :
    (PathMeasure (Step PositiveLength) Initial)[
      fun Path => Potential (Path j) - Potential (Path (j + 1)) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) j] =ᵐ[
        PathMeasure (Step PositiveLength) Initial]
      (fun Path => Potential (Path j) / (n : ℝ)) := by
  simpa only [OneStepDrift PositiveLength] using
    (PathMeasureStateConditionalExpectation (Step PositiveLength) Initial j
      (fun x y => Potential x - Potential y))

/-- With at most half the bits initially zero, each actual conditional
expected decrease remains at most one half. -/
theorem PathHalfInitialConditionalDecrease {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (HalfInitial : 2 * ZeroCount InitialState ≤ n) (j : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))[
      fun Path => Potential (Path j) - Potential (Path (j + 1)) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) j] ≤ᵐ[
        PathMeasure (Step PositiveLength) (PMF.pure InitialState)]
      (fun _ => (1 / 2 : ℝ)) := by
  have PositiveN : 0 < (n : ℝ) := Nat.cast_pos.mpr PositiveLength
  have Half : 2 * Potential InitialState ≤ (n : ℝ) := by
    change 2 * (ZeroCount InitialState : ℝ) ≤ (n : ℝ)
    exact_mod_cast HalfInitial
  filter_upwards [PathConditionalDecreaseMean PositiveLength (PMF.pure InitialState) j,
    PathPotentialLeInitial PositiveLength InitialState j] with Path Mean Reachable
  rw [Mean]
  apply (div_le_iff₀ PositiveN).mpr
  linarith

/-- Closed geometric jump tails with eta=1 and r=1, proved from the binary
increment of the actual RLS path and its conditional mean bound. -/
theorem PathHalfInitialConditionalJumpTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (HalfInitial : 2 * ZeroCount InitialState ≤ n)
    (j k : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))[
      ({Path | (k : ℝ) ≤ |Potential (Path (j + 1)) - Potential (Path j)|}).indicator
        (fun _ => (1 : ℝ)) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) j] ≤ᵐ[
        PathMeasure (Step PositiveLength) (PMF.pure InitialState)]
      (fun _ => 1 / (1 + (1 : ℝ)) ^ k) := by
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let F := Filtration.piLE (X := fun _ : ℕ => Bits n)
  have Binary := PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
    (fun x y => Potential x - Potential y = 0 ∨ Potential x - Potential y = 1)
    (StepPotentialDecreaseBinary PositiveLength) j
  cases k with
  | zero =>
    have Constant : ({Path : ℕ → Bits n |
        ((0 : ℕ) : ℝ) ≤ |Potential (Path (j + 1)) - Potential (Path j)|}).indicator
        (fun _ => (1 : ℝ)) = (fun _ => 1) := by
      funext Path
      have Member : Path ∈ {u : ℕ → Bits n |
          ((0 : ℕ) : ℝ) ≤ |Potential (u (j + 1)) - Potential (u j)|} := by
        simpa only [Set.mem_ofPred_eq, Nat.cast_zero] using
          (abs_nonneg (Potential (Path (j + 1)) - Potential (Path j)))
      exact Set.indicator_of_mem Member _
    rw [Constant, condExp_const (F.le j)]
    exact ae_of_all _ (fun _ => by norm_num)
  | succ k =>
    by_cases Zero : k = 0
    · subst k
      have Same : ({Path : ℕ → Bits n |
          ((0 + 1 : ℕ) : ℝ) ≤ |Potential (Path (j + 1)) - Potential (Path j)|}).indicator
          (fun _ => (1 : ℝ)) =ᵐ[μ]
          (fun Path => Potential (Path j) - Potential (Path (j + 1))) := by
        filter_upwards [Binary] with Path Drop
        have Forward : Potential (Path (j + 1)) - Potential (Path j) =
            -(Potential (Path j) - Potential (Path (j + 1))) := by ring
        rcases Drop with Drop | Drop <;>
          norm_num [Set.indicator_apply, Forward, abs_neg, Drop]
      have Conditional := condExp_congr_ae (m := F j) Same
      filter_upwards [Conditional,
        PathHalfInitialConditionalDecrease PositiveLength InitialState HalfInitial j]
        with Path Equal Bound
      rw [Equal]
      simpa only [Nat.cast_zero, zero_add, pow_one, one_add_one_eq_two] using Bound
    · have Large : (1 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 < k + 1 by omega)
      have Vanishes : ({Path : ℕ → Bits n |
          ((k + 1 : ℕ) : ℝ) ≤ |Potential (Path (j + 1)) - Potential (Path j)|}).indicator
          (fun _ => (1 : ℝ)) =ᵐ[μ] (fun _ => 0) := by
        filter_upwards [Binary] with Path Drop
        apply Set.indicator_of_notMem
        change ¬((k + 1 : ℕ) : ℝ) ≤ |Potential (Path (j + 1)) - Potential (Path j)|
        rw [show Potential (Path (j + 1)) - Potential (Path j) =
          -(Potential (Path j) - Potential (Path (j + 1))) by ring, abs_neg]
        rcases Drop with Drop | Drop
        · rw [Drop, abs_zero]
          exact not_le_of_gt ((zero_lt_one : (0 : ℝ) < 1).trans Large)
        · rw [Drop, abs_one]
          exact not_le_of_gt Large
      have Conditional := condExp_congr_ae (m := F j) Vanishes
      rw [condExp_const (F.le j)] at Conditional
      filter_upwards [Conditional] with Path Equal
      rw [Equal]
      positivity

/-- The generic lower-tail theorem applied to the genuine RLS kernel and its
full-history law, for any fixed initial state with at most half zero bits. -/
theorem HalfInitialGeometricLowerTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (HalfInitial : 2 * ZeroCount InitialState ≤ n)
    (t : ℕ) (PositiveTime : 0 < t)
    (EarlyEnough : (1 / 2 : ℝ) * (t : ℝ) ≤ (ZeroCount InitialState : ℝ)) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal (Real.exp (-min
        (GeometricJumpMomentRadius 1 * ((ZeroCount InitialState : ℝ) - (t : ℝ) / 2) / 4)
        ((GeometricJumpMomentRadius 1) ^ 2 *
          ((ZeroCount InitialState : ℝ) - (t : ℝ) / 2) ^ 2 / (192 * (t : ℝ))))) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits n) → ℝ := fun j Path => Potential (Path j)
  let F := Filtration.piLE (X := fun _ : ℕ => Bits n)
  let S := Finset.univ.image (Potential (n := n))
  have AdaptedX : Adapted F X := PathPotentialAdapted Potential
  have Values (j : ℕ) (Path : ℕ → Bits n) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have Initial : ∀ᵐ Path ∂μ, X 0 Path = (ZeroCount InitialState : ℝ) := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState] with Path Initial
    change Potential (Path 0) = (ZeroCount InitialState : ℝ)
    rw [Initial]
    rfl
  have InitialAbove : (0 : ℝ) < (ZeroCount InitialState : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) (Nat.cast_pos.mpr PositiveTime)).trans_le EarlyEnough
  have JumpTail : ∀ j (k : ℕ), ∀ᵐ Path ∂μ, 0 < X j Path →
      (μ[({u | (k : ℝ) ≤ |X (j + 1) u - X j u|}).indicator
        (fun _ => (1 : ℝ)) | F j]) Path ≤ 1 / (1 + (1 : ℝ)) ^ k := by
    intro j k
    filter_upwards [PathHalfInitialConditionalJumpTail PositiveLength InitialState HalfInitial j k]
      with Path Bound
    exact fun _ => Bound
  have Drift : ∀ j, ∀ᵐ Path ∂μ, 0 < X j Path →
      (μ[fun u => X j u - X (j + 1) u | F j]) Path ≤ (1 / 2 : ℝ) := by
    intro j
    filter_upwards [PathHalfInitialConditionalDecrease PositiveLength InitialState HalfInitial j]
      with Path Bound
    exact fun _ => Bound
  have Bound := GeometricAdditiveDriftLowerTailOfCondExp μ X F AdaptedX S 0
    (ZeroCount InitialState : ℝ) 1 (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
    Values InitialAbove Initial JumpTail Drift t PositiveTime (by simpa only [sub_zero] using EarlyEnough)
  have Hitting (Path : ℕ → Bits n) :
      FirstHittingTime (fun s : ℝ => s ≤ 0) (fun j => X j Path) =
        FirstHittingTime IsTarget Path :=
    (ZeroHittingTimeEqNonpositive X (fun _ Path => PotentialNonnegative (Path _)) Path).symm.trans
      (ZeroHittingTimeEqRuntime Path)
  simp_rw [Hitting] at Bound
  have Constant : (32 : ℝ) * GeometricJumpMomentBound 1 1 = 192 := by
    norm_num [GeometricJumpMomentBound]
  have HalfTime : (1 / 2 : ℝ) * (t : ℝ) = (t : ℝ) / 2 := by ring
  simpa only [sub_zero, Constant, HalfTime] using Bound

/-- From m zero bits in length 2m, finishing within m mutations has an
exponentially small upper bound. The existing exact mean is not replaced. -/
theorem HalfZerosGeometricEarlyHit (m : ℕ) (PositiveM : 0 < m)
    (InitialState : Bits (2 * m)) (HalfZeros : ZeroCount InitialState = m) :
    (PathMeasure (Step (Nat.mul_pos (by decide : 0 < 2) PositiveM)) (PMF.pure InitialState))
      {Path | FirstHittingTime IsTarget Path ≤ (m : WithTop ℕ)} ≤
      ENNReal.ofReal (Real.exp (-min
        (GeometricJumpMomentRadius 1 * (m : ℝ) / 8)
        ((GeometricJumpMomentRadius 1) ^ 2 * (m : ℝ) / 768))) := by
  have PositiveLength : 0 < 2 * m := Nat.mul_pos (by decide) PositiveM
  have HalfInitial : 2 * ZeroCount InitialState ≤ 2 * m := by rw [HalfZeros]
  have Early : (1 / 2 : ℝ) * (m : ℝ) ≤ (ZeroCount InitialState : ℝ) := by
    rw [HalfZeros]
    have NonnegativeM : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have Bound := HalfInitialGeometricLowerTail PositiveLength InitialState HalfInitial m PositiveM Early
  rw [HalfZeros] at Bound
  have PositiveReal : (0 : ℝ) < m := Nat.cast_pos.mpr PositiveM
  have Linear : GeometricJumpMomentRadius 1 * ((m : ℝ) - (m : ℝ) / 2) / 4 =
      GeometricJumpMomentRadius 1 * (m : ℝ) / 8 := by ring
  have Quadratic : (GeometricJumpMomentRadius 1) ^ 2 * ((m : ℝ) - (m : ℝ) / 2) ^ 2 /
      (192 * (m : ℝ)) = (GeometricJumpMomentRadius 1) ^ 2 * (m : ℝ) / 768 := by
    field_simp [PositiveReal.ne']
    ring
  rwa [Linear, Quadratic] at Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
