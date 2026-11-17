import ECTheoryLib.Analysis.Needle.RLS.RuntimeLowerBounds
import ECTheoryLib.Tools.Drift.BoundedNegativeDrift

/-!
# RLS on Needle through ordinary negative drift

The actual kernel has signed decrease 2V/n-1 outside the optimum, and
absolute jumps at most one everywhere. These verify the bounded-jump
negative-drift interface with delta=1/2 on (0,n/4).
The earlier exact-moment bound remains available and is sharper.
-/

namespace ECTheoryLib.Analysis.RLSOnNeedle
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- All accepted increments, including the absorbing optimum, have size at most one. -/
theorem UpdateAbsoluteJumpBound {n : ℕ} (x : Bits n) (i : Fin n) :
    |Potential (Update x i)-Potential x| ≤ 1 := by
  by_cases Target : IsTarget x
  · rw [UpdateAtTarget x i Target, sub_self, abs_zero]
    norm_num
  · rw [UpdateAway x i Target, MutationPotentialIncrement]
    cases x i with
    | false => change |(-1 : ℝ)|≤1; norm_num
    | true => change |(1 : ℝ)|≤1; norm_num

theorem StepAbsoluteJumpBound {n : ℕ} (PositiveLength : 0<n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, |Potential y-Potential x|≤1 := by
  rw [Step, RLSStepEqUniformUpdate]
  apply PMFAEOfSupport
  intro y Supported
  obtain ⟨i, _Possible, Equal⟩ := (PMF.mem_support_map_iff _ _ _).mp Supported
  rw [← Equal]
  exact UpdateAbsoluteJumpBound x i

/-- The plateau drift points away from the target whenever distance is below n/2. -/
theorem OneStepDriftAway {n : ℕ} (PositiveLength : 0<n) (x : Bits n) (Away : ¬ IsTarget x) :
    (∫ y, Potential x-Potential y ∂(Step PositiveLength x).toMeasure) =
      2*Potential x/(n : ℝ)-1 := by
  classical
  have Each (i : Fin n) : Potential x-Potential (Update x i) =
      2*(if x i then (0 : ℝ) else 1)-1 := by
    rw [UpdateAway x i Away]
    have Increment := MutationPotentialIncrement x i
    cases Bit : x i with
    | false =>
      rw [Bit] at Increment
      change Potential (OnebitMutation x i)-Potential x = -1 at Increment
      change Potential x-Potential (OnebitMutation x i)=2*1-1
      linarith
    | true =>
      rw [Bit] at Increment
      change Potential (OnebitMutation x i)-Potential x = 1 at Increment
      change Potential x-Potential (OnebitMutation x i)=2*0-1
      linarith
  rw [Step, RLSStepEqUniformUpdate, PMFIntegralMap, PMF.integral_eq_sum]
  simp only [smul_eq_mul, UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  change (n : ℝ)⁻¹*(∑ i : Fin n, (Potential x-Potential (Update x i)))=_
  simp_rw [Each]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Problems.OneMax.ZeroBitCountAsReal,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have Nonzero : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr PositiveLength).ne'
  change (n : ℝ)⁻¹*(2*Potential x-(n : ℝ))=2*Potential x/(n : ℝ)-1
  field_simp

/-- A second derivation of Needle's exponential lower tail, using only ordinary
negative drift and bounded jumps. It validates the general sufficient-condition
interface; the exact-moment theorem remains sharper. -/
theorem FixedRuntimeBoundedDriftLowerTail {n : ℕ} (PositiveLength : 0<n)
    (InitialState : Bits n) (InitiallyFar : (n : ℝ)/4 ≤ Potential InitialState) (t : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*Real.exp (-(1/2 : ℝ)*((n : ℝ)/4-1))) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits n) → ℝ := fun j Path => Potential (Path j)
  let S : Finset ℝ := Finset.univ.image (Potential (n := n))
  have Coordinates (j : ℕ) : Measurable (X j) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply j)
  have Values (j : ℕ) (Path : ℕ → Bits n) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have Initial : ∀ᵐ Path ∂μ, (n : ℝ)/4≤X 0 Path := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState] with Path AtInitial
    change (n : ℝ)/4≤Potential (Path 0)
    rw [AtInitial]
    exact InitiallyFar
  have Absorbing (j : ℕ) : ∀ᵐ Path ∂μ, X j Path≤0 → X (j+1) Path≤0 :=
    PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
      (fun x y => Potential x≤0 → Potential y≤0) (StepTargetAbsorbing PositiveLength) j
  have Jumps (j : ℕ) : ∀ᵐ Path ∂μ, 0<X j Path → |X (j+1) Path-X j Path|≤1 := by
    filter_upwards [PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
      (fun x y => |Potential y-Potential x|≤1) (StepAbsoluteJumpBound PositiveLength) j] with Path Jump
    exact fun _ => Jump
  have Drift (j : ℕ) (s : ℝ) (_Member : s∈S) (Above : 0<s) (Below : s<(n : ℝ)/4)
      (Positive : 0<μ (StateEvent X j s)) : StateDrift μ X j s ≤ -(1/2 : ℝ) := by
    rw [StateDrift, EventConditionalExpectationEqCondIntegral]
    exact PathMeasureConditionalTransitionIntegralUpperBound (Step PositiveLength)
      (PMF.pure InitialState) j {x | Potential x=s} (fun x y => Potential x-Potential y)
      (-(1/2 : ℝ)) Positive (by
        intro x Equal
        change Potential x=s at Equal
        have Away : ¬ IsTarget x := fun Target => by
          have Zero := (PotentialEqZeroIffTarget x).mpr Target
          linarith
        rw [OneStepDriftAway PositiveLength x Away, Equal]
        have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
        have Ratio : 2*s/(n : ℝ)<1/2 := (div_lt_iff₀ PositiveN).mpr (by linarith)
        linarith)
  have Bound := BoundedJumpNegativeDriftTail μ X S 0 ((n : ℝ)/4) 1 (1/2)
    (div_pos (Nat.cast_pos.mpr PositiveLength) (by norm_num)) (by norm_num) (by norm_num)
    Coordinates Values Initial Absorbing Jumps Drift t
  have Hitting (Path : ℕ → Bits n) :
      FirstHittingTime (fun s : ℝ => s≤0) (fun j => X j Path)=FirstHittingTime IsTarget Path := by
    have SameGoal (j : ℕ) : (X j Path≤0) ↔ IsTarget (Path j) := by
      rw [← PotentialEqZeroIffTarget]
      exact ⟨fun Zero => le_antisymm Zero (PotentialNonnegative _), fun Zero => Zero.le⟩
    unfold FirstHittingTime hittingAfter
    change (if ∃ j, 0≤j ∧ X j Path≤0 then
      ((sInf {j : ℕ | 0≤j ∧ X j Path≤0} : ℕ) : WithTop ℕ) else ⊤) =
        if ∃ j, 0≤j ∧ IsTarget (Path j) then
          ((sInf {j : ℕ | 0≤j ∧ IsTarget (Path j)} : ℕ) : WithTop ℕ) else ⊤
    simp only [SameGoal]
  simp_rw [Hitting] at Bound
  norm_num only [one_pow, div_one, sub_zero] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnNeedle
