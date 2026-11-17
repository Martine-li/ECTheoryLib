import ECTheoryLib.Tools.Drift.BoundedAdditiveTail
import ECTheoryLib.Tools.Drift.ExponentialTail
import ECTheoryLib.Analysis.OneMax.RLS.RuntimeMultiplicativeLowerBounds

/-!
# Exponential upper tails for actual RLS on OneMax

The exact zero-or-one decrease gives the conditional exponential moment
1 + (exp(-lambda)-1)*s/n. At a positive state s >= 1 this is at most
1 - (1-exp(-lambda))/n. Applying the general exponential drift theorem gives
a fixed-start tail at every natural time. This verifies the general API with
actual trajectory events; the sharper existing multiplicative tails remain.
Time counts mutation iterations after initialization.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- Exact conditional exponential moment of the genuine zero-or-one RLS decrease. -/
theorem PathExponentialDecreaseMoment {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n))
    (t : ℕ) (s Lambda : ℝ)
    (PositiveEvent : 0 < PathMeasure (Step PositiveLength) Initial
      (StateEvent (fun t Path => Potential (Path t)) t s)) :
    EventConditionalExpectation (PathMeasure (Step PositiveLength) Initial)
      (fun Path => Real.exp (Lambda*(Potential (Path (t+1))-Potential (Path t))))
      (StateEvent (fun t Path => Potential (Path t)) t s) =
        1+(Real.exp (-Lambda)-1)*(s/(n : ℝ)) := by
  classical
  let μ := PathMeasure (Step PositiveLength) Initial
  let X : ℕ → (ℕ → Bits n) → ℝ := fun t Path => Potential (Path t)
  let ν := cond μ (StateEvent X t s)
  have ConditionalProbability : IsProbabilityMeasure ν := cond_isProbabilityMeasure PositiveEvent.ne'
  have Binary : ∀ᵐ Path ∂ν, X t Path-X (t+1) Path=0 ∨ X t Path-X (t+1) Path=1 :=
    cond_absolutelyContinuous.ae_le (PathMeasureFollowsTransition (Step PositiveLength) Initial
      (fun x y => Potential x-Potential y=0 ∨ Potential x-Potential y=1)
      (StepPotentialDecreaseBinary PositiveLength) t)
  have CoordinateIntegrable (j : ℕ) : Integrable (X j) ν :=
    FiniteStateIntegrable ν (X j) (Finset.univ.image (Potential (n := n)))
      ((measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply j))
      (ae_of_all _ (fun Path => Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩))
  have ExactDrift : (∫ Path, X t Path-X (t+1) Path ∂ν)=s/(n : ℝ) := by
    have Local (x : Bits n) : (∫ y, Potential x-Potential y ∂(Step PositiveLength x).toMeasure)=Potential x/(n : ℝ) :=
      OneStepDrift PositiveLength x
    have Bound := PathMeasureStateDrift (Step PositiveLength) Initial Potential (fun s => s/(n : ℝ))
      Local t s PositiveEvent
    rw [StateDrift, EventConditionalExpectationEqCondIntegral] at Bound
    exact Bound
  have Affine : (fun Path => Real.exp (Lambda*(X (t+1) Path-X t Path))) =ᵐ[ν]
      (fun Path => 1+(Real.exp (-Lambda)-1)*(X t Path-X (t+1) Path)) := by
    filter_upwards [Binary] with Path Drop
    have Reverse : X (t+1) Path-X t Path= -(X t Path-X (t+1) Path) := by ring
    rw [Reverse]
    rcases Drop with Zero | One
    · rw [Zero]
      norm_num
    · rw [One]
      simp only [mul_neg_one, mul_one, add_sub_cancel]
  rw [EventConditionalExpectationEqCondIntegral]
  change (∫ Path, Real.exp (Lambda*(X (t+1) Path-X t Path)) ∂ν)=_
  have ScaledIntegrable : Integrable (fun Path => (Real.exp (-Lambda)-1)*(X t Path-X (t+1) Path)) ν :=
    ((CoordinateIntegrable t).sub (CoordinateIntegrable (t+1))).const_mul _
  rw [integral_congr_ae Affine, integral_add (integrable_const (1 : ℝ)) ScaledIntegrable,
    integral_const, probReal_univ, one_smul, integral_const_mul, ExactDrift]

/-- A direct fixed-start exponential-tail invocation; all local moment conditions come from actual RLS. -/
theorem FixedRuntimeExponentialUpperTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitialPositive : 0 < ZeroCount InitialState)
    (Lambda : ℝ) (NonnegativeLambda : 0 ≤ Lambda) (t : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | (t : WithTop ℕ) < FirstHittingTime IsTarget Path} ≤
      ENNReal.ofReal ((1-(1-Real.exp (-Lambda))/(n : ℝ))^t*
        Real.exp (Lambda*(ZeroCount InitialState : ℝ))) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits n) → ℝ := fun j Path => Potential (Path j)
  let S : Finset ℝ := Finset.univ.image (Potential (n := n))
  let β := 1-(1-Real.exp (-Lambda))/(n : ℝ)
  have Coordinates (j : ℕ) : Measurable (X j) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply j)
  have Values (j : ℕ) (Path : ℕ → Bits n) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have NonnegativeX (j : ℕ) (Path : ℕ → Bits n) : 0 ≤ X j Path := Nat.cast_nonneg _
  have Absorbing (j : ℕ) : ∀ᵐ Path ∂μ, X j Path ≤ 0 → X (j+1) Path ≤ 0 := by
    have Nonincrease := PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
      (fun x y => Potential y ≤ Potential x) (StepPotentialNonincreasing PositiveLength) j
    filter_upwards [Nonincrease] with Path Decreases
    intro AtTarget
    exact Decreases.trans AtTarget
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have OneLeN : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr PositiveLength
  have ExpPositive : 0 < Real.exp (-Lambda) := Real.exp_pos _
  have ExpLeOne : Real.exp (-Lambda) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr NonnegativeLambda)
  have NonnegativeBeta : 0 ≤ β := by
    apply sub_nonneg.mpr
    apply (div_le_one PositiveN).mpr
    linarith
  have Moment (j : ℕ) (s : ℝ) (InS : s ∈ S) (Above : 0 < s)
      (PositiveEvent : 0 < μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun Path => Real.exp (Lambda*(X (j+1) Path-X j Path)))
        (StateEvent X j s) ≤ β := by
    have LowerS : 1 ≤ s := by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp InS
      have PositiveCount : 0 < ZeroCount x := Nat.cast_pos.mp Above
      exact Nat.one_le_cast.mpr PositiveCount
    rw [PathExponentialDecreaseMoment PositiveLength (PMF.pure InitialState) j s Lambda PositiveEvent]
    have Ratio : 1/(n : ℝ) ≤ s/(n : ℝ) := div_le_div_of_nonneg_right LowerS PositiveN.le
    have Comparison := mul_le_mul_of_nonpos_left Ratio (sub_nonpos.mpr ExpLeOne)
    change 1+(Real.exp (-Lambda)-1)*(s/(n : ℝ)) ≤ 1-(1-Real.exp (-Lambda))/(n : ℝ)
    have Rearrange : (Real.exp (-Lambda)-1)*(1/(n : ℝ))= -(1-Real.exp (-Lambda))/(n : ℝ) := by ring
    rw [Rearrange] at Comparison
    rw [neg_div] at Comparison
    linarith
  have Initial : ∀ᵐ Path ∂μ, X 0 Path=(ZeroCount InitialState : ℝ) := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState] with Path AtInitial
    change Potential (Path 0)=(ZeroCount InitialState : ℝ)
    rw [AtInitial]
    rfl
  have Bound := ExponentialDriftUpperTailOfFixedInitial μ X S 0 Lambda (ZeroCount InitialState : ℝ)
    id (fun _ => β) Coordinates Values Absorbing NonnegativeLambda (fun _ => NonnegativeBeta)
    (fun _ _ Above => Above.le) Moment (Nat.cast_pos.mpr InitialPositive) Initial t
  have Hitting (Path : ℕ → Bits n) :
      FirstHittingTime (fun s : ℝ => s ≤ 0) (fun j => X j Path)=FirstHittingTime IsTarget Path := by
    have SameGoal (j : ℕ) : (X j Path ≤ 0) ↔ IsTarget (Path j) := by
      rw [← PotentialEqZeroIffTarget]
      exact ⟨fun AtZero => le_antisymm AtZero (NonnegativeX j Path), fun Equal => Equal.le⟩
    unfold FirstHittingTime hittingAfter
    change (if ∃ j, 0 ≤ j ∧ X j Path ≤ 0 then
      ((sInf {j : ℕ | 0 ≤ j ∧ X j Path ≤ 0} : ℕ) : WithTop ℕ) else ⊤) =
        if ∃ j, 0 ≤ j ∧ IsTarget (Path j) then
          ((sInf {j : ℕ | 0 ≤ j ∧ IsTarget (Path j)} : ℕ) : WithTop ℕ) else ⊤
    simp only [SameGoal]
  simp only [id_eq, sub_zero, Finset.prod_const, Finset.card_range] at Bound
  simp_rw [Hitting] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift

noncomputable section

/-- From the all-false string of length `2*m`, the actual RLS time until at
least half the bits are one exceeds `4*m` with probability at most `exp(-m/8)`.
The time counts transitions after initialization, not the full optimization time. -/
theorem HalfProgressUpperTail (m : ℕ) (PositiveM : 0 < m) :
    (PathMeasure (Step (Nat.mul_pos (by decide : 0 < 2) PositiveM))
      (PMF.pure (fun _ : Fin (2*m) => false)))
      {Path | ((4*m : ℕ) : WithTop ℕ) <
        FirstHittingTime (fun x : Bits (2*m) => Potential x ≤ (m : ℝ)) Path} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ)/8)) := by
  classical
  let PositiveLength : 0 < 2*m := Nat.mul_pos (by decide) PositiveM
  let InitialState : Bits (2*m) := fun _ => false
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits (2*m)) → ℝ := fun j Path => Potential (Path j)
  let S : Finset ℝ := Finset.univ.image (Potential (n := 2*m))
  have PositiveMReal : (0 : ℝ) < m := Nat.cast_pos.mpr PositiveM
  have PositiveN : (0 : ℝ) < (2*m : ℕ) := Nat.cast_pos.mpr PositiveLength
  have Coordinates (j : ℕ) : Measurable (X j) :=
    (measurable_of_finite (Potential (n := 2*m))).comp (measurable_pi_apply j)
  have Values (j : ℕ) (Path : ℕ → Bits (2*m)) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have Absorbing (j : ℕ) : ∀ᵐ Path ∂μ,
      X j Path ≤ (m : ℝ) → X (j+1) Path ≤ (m : ℝ) := by
    have MonotoneStep := PathMeasureFollowsTransition (Step PositiveLength)
      (PMF.pure InitialState) (fun x y => Potential y ≤ Potential x)
      (StepPotentialNonincreasing PositiveLength) j
    filter_upwards [MonotoneStep] with Path Nonincrease
    exact fun Reached => Nonincrease.trans Reached
  have Jumps (j : ℕ) : ∀ᵐ Path ∂μ,
      (m : ℝ) < X j Path → |X (j+1) Path-X j Path| ≤ 1 := by
    have Binary := PathMeasureFollowsTransition (Step PositiveLength)
      (PMF.pure InitialState)
      (fun x y => Potential x-Potential y=0 ∨ Potential x-Potential y=1)
      (StepPotentialDecreaseBinary PositiveLength) j
    filter_upwards [Binary] with Path Drop
    intro _Above
    change X j Path-X (j+1) Path=0 ∨ X j Path-X (j+1) Path=1 at Drop
    apply abs_le.mpr
    rcases Drop with Zero | One
    · constructor <;> linarith
    · constructor <;> linarith
  have StateMean (j : ℕ) (s : ℝ) (_InS : s ∈ S) (Above : (m : ℝ) < s)
      (PositiveEvent : 0 < μ (StateEvent X j s)) :
      (1/2 : ℝ) ≤ StateDrift μ X j s := by
    have Exact := PathMeasureStateDrift (Step PositiveLength) (PMF.pure InitialState)
      Potential (fun s => s/(2*m : ℕ)) (OneStepDrift PositiveLength) j s PositiveEvent
    rw [Exact]
    apply (le_div_iff₀ PositiveN).mpr
    push_cast
    linarith
  have InitialAbove : (m : ℝ) < (2*m : ℕ) := by
    push_cast
    linarith
  have FixedInitial : ∀ᵐ Path ∂μ, X 0 Path=(2*m : ℕ) := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState]
      with Path Initial
    change Potential (Path 0)=(2*m : ℕ)
    rw [Initial]
    simp [InitialState, Potential, ZeroCount, Problems.OneMax.ZeroCount, ECTheoryLib.OneMax]
  have LateEnough : ((2*m : ℕ) : ℝ)-(m : ℝ) ≤ (1/2 : ℝ)*(4*m : ℕ) := by
    push_cast
    linarith
  have Bound := BoundedAdditiveDriftUpperTail μ X S (m : ℝ) (2*m : ℕ) 1 (1/2)
    Coordinates Values Absorbing Jumps StateMean (by norm_num) (by norm_num)
    InitialAbove FixedInitial (4*m) (Nat.mul_pos (by decide) PositiveM) LateEnough
  have Exponent : -(((1/2 : ℝ)*(4*m : ℕ)-((2*m : ℕ)-(m : ℝ)))^2) /
      (2*(4*m : ℕ)*(1 : ℝ)^2)=-(m : ℝ)/8 := by
    push_cast
    field_simp [ne_of_gt PositiveMReal]
    ring
  rw [Exponent] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
