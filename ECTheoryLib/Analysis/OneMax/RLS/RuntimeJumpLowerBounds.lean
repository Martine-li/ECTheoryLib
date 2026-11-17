import ECTheoryLib.Tools.Drift.VariableJumpLower
import ECTheoryLib.Analysis.OneMax.RLS.RuntimeLowerBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Jump-floor variable drift for RLS on OneMax

This implements Lengler Example 2.4.4 using the actual RLS transition.
The floor xi(s)=s-1 is nonnegative on positive attainable states, including
zero at s=1. The drift h(s)=(s+1)/n is positive at zero and h(xi(s))=s/n.
The application verifies these premises before invoking Theorem 2.4.2.
The closed form counts mutation iterations, with no initialization offset.
Existing exact harmonic runtime results are retained.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- Actual RLS verifies the jump-floor theorem with ξ(s)=s-1 and h(s)=(s+1)/n. -/
theorem RuntimeJumpLowerBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ENNReal.ofReal (∫ x, VariableDriftPotential 1 (fun s => (s+1)/(n : ℝ)) (Potential x)
      ∂Initial.toMeasure) ≤ ExpectedHittingTime (Step PositiveLength) IsTarget Initial := by
  classical
  let μ := PathMeasure (Step PositiveLength) Initial
  let X : ℕ → (ℕ → Bits n) → ℝ := fun t Path => Potential (Path t)
  let S : Finset ℝ := insert 0 (Finset.univ.image (Potential (n := n)))
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have StateLower : ∀ s ∈ S, s=0 ∨ (1 : ℝ) ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | InImage
    · exact Or.inl Zero
    · obtain ⟨x, _InUniv, rfl⟩ := Finset.mem_image.mp InImage
      by_cases Zero : ZeroCount x=0
      · exact Or.inl (Nat.cast_eq_zero.mpr Zero)
      · right
        change (1 : ℝ) ≤ (ZeroCount x : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero
  have ValuesInS (t : ℕ) (Path : ℕ → Bits n) : X t Path ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩)
  have CoordinatesMeasurable (t : ℕ) : Measurable (X t) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply t)
  have Nonincreasing (t : ℕ) : ∀ᵐ Path ∂μ, X (t+1) Path ≤ X t Path :=
    PathMeasureFollowsTransition (Step PositiveLength) Initial
      (fun x y => Potential y ≤ Potential x) (StepPotentialNonincreasing PositiveLength) t
  have JumpFloor (t : ℕ) : ∀ᵐ Path ∂μ, X t Path ≠ 0 → X t Path-1 ≤ X (t+1) Path := by
    have Drop := PathMeasureFollowsTransition (Step PositiveLength) Initial
      (fun x y => Potential x-Potential y ≤ 1) (StepPotentialDropAtMostOne PositiveLength) t
    filter_upwards [Drop] with Path SmallDrop
    intro _Nonzero
    change X t Path-X (t+1) Path ≤ 1 at SmallDrop
    linarith
  have LocalDrift (x : Bits n) :
      (∫ y, Potential x-Potential y ∂(Step PositiveLength x).toMeasure) = (Potential x-1+1)/(n : ℝ) := by
    rw [OneStepDrift, sub_add_cancel]
  have Drift (t : ℕ) (s : ℝ) (_InS : s ∈ S) (_Nonzero : s ≠ 0)
      (PositiveEvent : 0 < μ (StateEvent X t s)) : StateDrift μ X t s ≤ (s-1+1)/(n : ℝ) :=
    (PathMeasureStateDrift (Step PositiveLength) Initial Potential (fun s => (s-1+1)/(n : ℝ))
      LocalDrift t s PositiveEvent).le
  have DriftPositive (x : ℝ) (Nonnegative : 0 ≤ x) : 0 < (x+1)/(n : ℝ) :=
    div_pos (by linarith) PositiveN
  have DriftMonotone : MonotoneOn (fun x : ℝ => (x+1)/(n : ℝ)) (Set.Ici 0) := by
    intro x _hx y _hy Before
    exact div_le_div_of_nonneg_right (add_le_add Before le_rfl) PositiveN.le
  have FloorNonnegative (s : ℝ) (InS : s ∈ S) (Nonzero : s ≠ 0) : 0 ≤ s-1 :=
    sub_nonneg.mpr ((StateLower s InS).resolve_left Nonzero)
  have Bound := VariableDriftLowerBoundOfJumpFloor μ X S 1 (fun s => (s+1)/(n : ℝ))
    (fun s => s-1) CoordinatesMeasurable zero_lt_one StateLower ValuesInS Nonincreasing
    DriftPositive DriftMonotone FloorNonnegative JumpFloor Drift
  have InitialMean : ExpectedValue μ (fun Path => VariableDriftPotential 1
      (fun s => (s+1)/(n : ℝ)) (X 0 Path)) =
      ∫ x, VariableDriftPotential 1 (fun s => (s+1)/(n : ℝ)) (Potential x) ∂Initial.toMeasure := by
    exact PathMeasureInitialIntegral (Step PositiveLength) Initial
      (fun x => VariableDriftPotential 1 (fun s => (s+1)/(n : ℝ)) (Potential x))
  rw [InitialMean] at Bound
  rw [ExpectedHittingTimeEqExpectedZero (Step PositiveLength) Initial Potential IsTarget PotentialEqZeroIffTarget]
  exact Bound

/-- The reciprocal integral used in Example 2.4.4, evaluated by translation and Mathlib's logarithm integral. -/
theorem ShiftedReciprocalDriftIntegral (n s : ℝ) (NonnegativeS : 0 ≤ s) :
    (∫ x in (1 : ℝ)..s, 1/((x+1)/n)) = n*(Real.log (s+1)-Real.log 2) := by
  have Integrands : (fun x : ℝ => 1/((x+1)/n)) = (fun x => n*(1/(x+1))) := by
    funext x
    rw [one_div_div]
    ring
  rw [Integrands, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right (fun x : ℝ => 1/x) 1]
  have PositiveEndpoint : 0 < s+1 := by linarith
  rw [integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1+1) PositiveEndpoint,
    Real.log_div PositiveEndpoint.ne' (by norm_num : (1+1 : ℝ) ≠ 0)]
  norm_num

/-- Example 2.4.4 for a fixed positive initial distance, with the leading n log k term. -/
theorem FixedRuntimeJumpLowerBound {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitialPositive : 0 < ZeroCount InitialState) :
    ENNReal.ofReal ((n : ℝ)/2+(n : ℝ)*(Real.log ((ZeroCount InitialState : ℝ)+1)-Real.log 2)) ≤
      ExpectedRuntime PositiveLength InitialState := by
  have Bound := RuntimeJumpLowerBound PositiveLength (PMF.pure InitialState)
  rw [PMF.toMeasure_pure, integral_dirac] at Bound
  have PositivePotential : 0 < Potential InitialState := Nat.cast_pos.mpr InitialPositive
  have Value : VariableDriftPotential 1 (fun s => (s+1)/(n : ℝ)) (Potential InitialState) =
      (n : ℝ)/2+(n : ℝ)*(Real.log ((ZeroCount InitialState : ℝ)+1)-Real.log 2) := by
    rw [VariableDriftPotential, if_neg PositivePotential.ne',
      ShiftedReciprocalDriftIntegral (n : ℝ) (Potential InitialState) PositivePotential.le,
      one_div_div]
    norm_num only [show (1+1 : ℝ)=2 by norm_num]
    rfl
  rw [Value] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
