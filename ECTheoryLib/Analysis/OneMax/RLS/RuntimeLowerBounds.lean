import ECTheoryLib.Tools.Drift.VariableLower
import ECTheoryLib.Analysis.OneMax.RLS.StochasticProgress
import ECTheoryLib.Analysis.OneMax.RLS.RuntimeBounds

/-!
# Variable-drift lower bound for actual RLS on OneMax

The real transition has nonincreasing zero count and decreases it by at most
one. These facts imply the drift-ratio condition with c=2 and h(s)=s/n.
The existing exact local drift is lifted to actual path conditioning.
Thus the theorem is called with verified premises, not an assumed drift
certificate. Arbitrary initial PMFs and initial optimal mass are retained.
For k>0 zero bits, the bound is n*(1+log k)/2 expected mutation iterations.
This is weaker than the existing exact n*H_k result and validates reuse of
the general lower-bound interface. No evaluation offset is hidden.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- The actual RLS transition decreases the zero-count potential by at most one. -/
theorem StepPotentialDropAtMostOne {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, Potential x-Potential y ≤ 1 := by
  have InRange : ∀ᵐ y ∂((UniformBitIndex n PositiveLength).toMeasure.map (Update x)),
      y ∈ Set.range (Update x) := by
    apply ae_map_mem_range
    exact (Set.to_countable _).measurableSet
  rw [PMF.toMeasure_map (Update x) (UniformBitIndex n PositiveLength) (measurable_of_finite _)] at InRange
  rw [Step, RLSStepEqUniformUpdate]
  filter_upwards [InRange] with y PossibleUpdate
  obtain ⟨i, UpdateEq⟩ := PossibleUpdate
  rw [← UpdateEq, PotentialDecrease]
  cases x i
  · norm_num
  · norm_num

/-- Actual RLS satisfies the variable-drift lower bound with c=2 for any initial PMF. -/
theorem RuntimeVariableLowerBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ENNReal.ofReal ((∫ x, MultiplicativeDriftPotential 1 (1/(n : ℝ)) (Potential x)
      ∂Initial.toMeasure)/2) ≤ ExpectedHittingTime (Step PositiveLength) IsTarget Initial := by
  classical
  let μ := PathMeasure (Step PositiveLength) Initial
  let X : Nat → (Nat → Bits n) → ℝ := fun t Path => Potential (Path t)
  let S : Finset ℝ := insert 0 (Finset.univ.image (Potential (n := n)))
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have PositiveDelta : 0 < 1/(n : ℝ) := one_div_pos.mpr PositiveN
  have StateLower : ∀ s ∈ S, s = 0 ∨ (1 : ℝ) ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | InImage
    · exact Or.inl Zero
    · obtain ⟨x, _InUniv, rfl⟩ := Finset.mem_image.mp InImage
      by_cases Zero : ZeroCount x = 0
      · left
        exact Nat.cast_eq_zero.mpr Zero
      · right
        change (1 : ℝ) ≤ (ZeroCount x : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero
  have ValuesInS (t : Nat) (Path : Nat → Bits n) : X t Path ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩)
  have CoordinatesMeasurable (t : Nat) : Measurable (X t) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply t)
  have Nonincreasing (t : Nat) : ∀ᵐ Path ∂μ, X (t+1) Path ≤ X t Path :=
    PathMeasureFollowsTransition (Step PositiveLength) Initial
      (fun x y => Potential y ≤ Potential x) (StepPotentialNonincreasing PositiveLength) t
  have Ratio (t : Nat) : ∀ᵐ Path ∂μ, X t Path ≠ 0 →
      1/(2 : ℝ) ≤ ((1/(n : ℝ))*max (X (t+1) Path) 1)/((1/(n : ℝ))*X t Path) := by
    have Drop := PathMeasureFollowsTransition (Step PositiveLength) Initial
      (fun x y => Potential x-Potential y ≤ 1) (StepPotentialDropAtMostOne PositiveLength) t
    filter_upwards [Drop] with Path SmallDrop
    intro Nonzero
    have LowerCurrent : 1 ≤ X t Path := (StateLower _ (ValuesInS t Path)).resolve_left Nonzero
    have PositiveCurrent : 0 < X t Path := lt_of_lt_of_le zero_lt_one LowerCurrent
    have CurrentUpper : X t Path ≤ 2*max (X (t+1) Path) 1 := by
      change X t Path-X (t+1) Path ≤ 1 at SmallDrop
      have AboveNext := le_max_left (X (t+1) Path) 1
      have AboveOne := le_max_right (X (t+1) Path) 1
      linarith
    apply (le_div_iff₀ (mul_pos PositiveDelta PositiveCurrent)).mpr
    have Scaled := mul_le_mul_of_nonneg_left CurrentUpper PositiveDelta.le
    nlinarith
  have LocalDrift (x : Bits n) :
      (∫ y, Potential x-Potential y ∂(Step PositiveLength x).toMeasure) = (1/(n : ℝ))*Potential x := by
    rw [OneStepDrift]
    ring
  have Drift (t : Nat) (s : ℝ) (_InS : s ∈ S) (_Nonzero : s ≠ 0)
      (PositiveEvent : 0 < μ (StateEvent X t s)) : StateDrift μ X t s ≤ (1/(n : ℝ))*s :=
    (PathMeasureStateDrift (Step PositiveLength) Initial Potential (fun s => (1/(n : ℝ))*s)
      LocalDrift t s PositiveEvent).le
  have DriftPositive (x : ℝ) (LowerX : 1 ≤ x) : 0 < (1/(n : ℝ))*x :=
    mul_pos PositiveDelta (lt_of_lt_of_le zero_lt_one LowerX)
  have DriftMonotone : MonotoneOn (fun x : ℝ => (1/(n : ℝ))*x) (Set.Ici 1) := by
    intro x _hx y _hy Before
    exact mul_le_mul_of_nonneg_left Before PositiveDelta.le
  have Bound := VariableDriftLowerBound μ X S 1 (fun x => (1/(n : ℝ))*x) 2
    CoordinatesMeasurable (Finset.mem_insert_self _ _) zero_lt_one StateLower ValuesInS Nonincreasing
    DriftPositive DriftMonotone (by norm_num) Ratio Drift
  have InitialMean : ExpectedValue μ (fun Path => VariableDriftPotential 1
      (fun x => (1/(n : ℝ))*x) (X 0 Path)) =
      ∫ x, MultiplicativeDriftPotential 1 (1/(n : ℝ)) (Potential x) ∂Initial.toMeasure := by
    unfold ExpectedValue
    change (∫ Path, VariableDriftPotential 1 (fun x => (1/(n : ℝ))*x) (Potential (Path 0))
      ∂PathMeasure (Step PositiveLength) Initial) = _
    rw [PathMeasureInitialIntegral (Step PositiveLength) Initial
      (fun x => VariableDriftPotential 1 (fun s => (1/(n : ℝ))*s) (Potential x))]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    apply LinearVariableDriftPotential 1 (1/(n : ℝ)) (Potential x) zero_lt_one PositiveDelta
    exact StateLower _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
  rw [InitialMean] at Bound
  rw [ExpectedHittingTimeEqExpectedZero (Step PositiveLength) Initial Potential IsTarget PotentialEqZeroIffTarget]
  exact Bound

/-- Actual RLS from k>0 zero bits needs at least n*(1+log k)/2 expected iterations by Theorem 2.4.1. -/
theorem FixedRuntimeVariableLowerBound {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitialPositive : 0 < ZeroCount InitialState) :
    ENNReal.ofReal (((n : ℝ)/2)*(1+Real.log (ZeroCount InitialState : ℝ))) ≤
      ExpectedRuntime PositiveLength InitialState := by
  have Bound := RuntimeVariableLowerBound PositiveLength (PMF.pure InitialState)
  rw [PMF.toMeasure_pure, integral_dirac] at Bound
  have Nonzero : Potential InitialState ≠ 0 := (Nat.cast_pos.mpr InitialPositive).ne'
  have Value : MultiplicativeDriftPotential 1 (1/(n : ℝ)) (Potential InitialState)/2 =
      ((n : ℝ)/2)*(1+Real.log (ZeroCount InitialState : ℝ)) := by
    simp only [MultiplicativeDriftPotential, if_neg Nonzero, div_one]
    rw [one_div, div_inv_eq_mul]
    unfold Potential
    ring
  rw [Value] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
