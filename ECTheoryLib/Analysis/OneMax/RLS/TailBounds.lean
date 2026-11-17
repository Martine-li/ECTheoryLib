import ECTheoryLib.Probability.Moments.ExponentialTailExpectation
import ECTheoryLib.Analysis.OneMax.RLS.RuntimeBounds
import ECTheoryLib.Analysis.OneMax.RLS.UniformRuntimeBound
import ECTheoryLib.Tools.Runtime.MultiplicativeTail

/-!
# Upper tails for the actual RLS-OneMax runtime

Lengler's Theorem 2.4.5 is instantiated with zero count, minimum positive value
one, and drift coefficient `1/n`. For a fixed state with `k > 0` zero bits,
the probability of needing more than `ceil (n * (log k + r))` iterations is at
most `exp (-r)`. Initialization is time zero and no evaluation offset is hidden.
The separate random-initialization result retains initially optimal mass and
gives the uniform-law estimate `(n/2) * exp (-t/n)` at every natural time.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open ECTheoryLib.Tools.Runtime

noncomputable section

private def TailPotentialRange (n : Nat) : Finset ℝ :=
  insert 0 (Finset.univ.image (Potential (n := n)))

private theorem TailPotentialInRange {n : Nat} (x : Bits n) :
    Potential x ∈ TailPotentialRange n := by
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)

private theorem TailPotentialLowerBound (n : Nat) :
    ∀ s ∈ TailPotentialRange n, s = 0 ∨ (1 : ℝ) ≤ s := by
  intro s InS
  rcases Finset.mem_insert.mp InS with IsZero | InImage
  · exact Or.inl IsZero
  · obtain ⟨x, _InUniv, ValueEq⟩ := Finset.mem_image.mp InImage
    by_cases IsZero : ZeroCount x = 0
    · left
      rw [← ValueEq]
      exact Nat.cast_eq_zero.mpr IsZero
    · right
      rw [← ValueEq]
      change (1 : ℝ) ≤ (ZeroCount x : ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr IsZero

/-- Direct invocation of the scalar book theorem on the actual fixed-initial
RLS trajectory measure. All stochastic and model premises are discharged. -/
theorem FixedRuntimeUpperTail {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitialPositive : 0 < ZeroCount InitialState)
    (r : ℝ) (NonnegativeR : 0 ≤ r) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | (⌈(n : ℝ) * (Real.log (ZeroCount InitialState : ℝ) + r)⌉₊ : WithTop Nat) <
        FirstHittingTime IsTarget Path} ≤ ENNReal.ofReal (Real.exp (-r)) := by
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : Nat → (Nat → Bits n) → ℝ := fun t Path => Potential (Path t)
  have MeasurableX : ∀ t, Measurable (X t) :=
    fun t => (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply t)
  have Absorbing : ZeroIsAbsorbing μ X := by
    intro t
    have Follows := PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
      (fun x y => ZeroCount x = 0 → ZeroCount y = 0)
      (StepPreservesZeroCount PositiveLength) t
    filter_upwards [Follows] with Path Preserves
    intro CurrentZero
    exact Nat.cast_eq_zero.mpr (Preserves (Nat.cast_eq_zero.mp CurrentZero))
  have LocalDrift : ∀ x : Bits n,
      (∫ y, Potential x - Potential y ∂(Step PositiveLength x).toMeasure) =
        (1 / (n : ℝ)) * Potential x := by
    intro x
    rw [OneStepDrift PositiveLength x]
    ring
  have Drift : ∀ t s, s ∈ TailPotentialRange n → s ≠ 0 →
      0 < μ (StateEvent X t s) → (1 / (n : ℝ)) * s ≤ StateDrift μ X t s := by
    intro t s _InS _Nonzero EventPositive
    have Exact := PathMeasureStateDrift (Step PositiveLength) (PMF.pure InitialState)
      Potential (fun s => (1 / (n : ℝ)) * s) LocalDrift t s EventPositive
    exact le_of_eq Exact.symm
  have InitialFixed : ∀ᵐ Path ∂μ, X 0 Path = (ZeroCount InitialState : ℝ) := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState]
      with Path AtInitial
    change Potential (Path 0) = (ZeroCount InitialState : ℝ)
    rw [AtInitial]
    rfl
  have Bound := MultiplicativeDriftUpperTail μ X (TailPotentialRange n) 1
    (1 / (n : ℝ)) (ZeroCount InitialState : ℝ) MeasurableX
    (Finset.mem_insert_self _ _) (by norm_num) (TailPotentialLowerBound n)
    (fun _ Path => TailPotentialInRange (Path _)) Absorbing
    (one_div_pos.mpr (Nat.cast_pos.mpr PositiveLength)) Drift InitialFixed
    (Nat.cast_pos.mpr InitialPositive) r NonnegativeR
  have Threshold : (r + Real.log ((ZeroCount InitialState : ℝ) / 1)) / (1 / (n : ℝ)) =
      (n : ℝ) * (Real.log (ZeroCount InitialState : ℝ) + r) := by
    rw [div_one, one_div, div_inv_eq_mul]
    ring
  have HittingEquality : ∀ Path : Nat → Bits n,
      ZeroHittingTime X Path = FirstHittingTime IsTarget Path := by
    intro Path
    exact ZeroHittingTimeEqRuntime Path
  rw [Threshold] at Bound
  simp_rw [HittingEquality] at Bound
  exact Bound

/-- For any initial law, the actual strict runtime tail is bounded by the
initial mean zero count times `exp (-t/n)`. Initial optimal states are included. -/
theorem RuntimeTailAtTime {n : Nat} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : Nat) :
    (PathMeasure (Step PositiveLength) Initial)
      {Path | (t : WithTop Nat) < FirstHittingTime IsTarget Path} ≤
      ENNReal.ofReal (Real.exp (-(t : ℝ) / (n : ℝ)) *
        (∫ x, Potential x ∂Initial.toMeasure)) := by
  have PreservesZero : ∀ x : Bits n, ∀ᵐ y ∂(Step PositiveLength x).toMeasure,
      True → Potential x = 0 → Potential y = 0 := by
    intro x
    filter_upwards [StepPreservesZeroCount PositiveLength x] with y Preserves
    intro _ IsZero
    exact Nat.cast_eq_zero.mpr (Preserves (Nat.cast_eq_zero.mp IsZero))
  have LocalDrift : ∀ x : Bits n, True → Potential x ≠ 0 →
      (1 / (n : ℝ)) * Potential x ≤
        ∫ y, Potential x - Potential y ∂(Step PositiveLength x).toMeasure := by
    intro x _ _
    rw [OneStepDrift PositiveLength x]
    exact le_of_eq (by ring)
  have Bound := MultiplicativeRuntimeTailAtTimeOfFiniteRange (Step PositiveLength) Initial
    Potential IsTarget (fun _ => True) (TailPotentialRange n) 1 (1 / (n : ℝ))
    (by norm_num) (TailPotentialLowerBound n) TailPotentialInRange PotentialEqZeroIffTarget
    (Filter.Eventually.of_forall (fun _ => True.intro))
    (fun _ => Filter.Eventually.of_forall (fun _ _ => True.intro)) PreservesZero LocalDrift t
  have Exponent : -(1 / (n : ℝ)) * (t : ℝ) = -(t : ℝ) / (n : ℝ) := by ring
  rw [Exponent, div_one] at Bound
  exact Bound

/-- Uniform initialization has mean zero count `n/2`; no conditioning on a
nonoptimal initial state changes the algorithm's actual distribution. -/
theorem UniformRuntimeTailAtTime {n : Nat} (PositiveLength : 0 < n) (t : Nat) :
    (RunMeasure PositiveLength) {Path | (t : WithTop Nat) < FirstHittingTime IsTarget Path} ≤
      ENNReal.ofReal (Real.exp (-(t : ℝ) / (n : ℝ)) * ((n : ℝ) / 2)) := by
  have Bound := RuntimeTailAtTime PositiveLength (RLSInit n) t
  rw [UniformInitialPotentialExpectation] at Bound
  exact Bound

/-- The strict runtime tail of an already optimal fixed initialization is
exactly zero at every natural time, independently of the logarithmic formula. -/
theorem OptimalInitialRuntimeTailEqZero {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitialZero : ZeroCount InitialState = 0) (t : Nat) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | (t : WithTop Nat) < FirstHittingTime IsTarget Path} = 0 := by
  have TimeZero := FirstHittingTimeOfPureTarget (Step PositiveLength) IsTarget InitialState
    ((ZeroCountEqZeroIffTarget InitialState).mp InitialZero)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [TimeZero] with Path HitAtZero
  rw [HitAtZero]
  exact not_lt_of_ge (by exact_mod_cast Nat.zero_le t)

end
end ECTheoryLib.Analysis.RLSOnOneMax

/-!
## Expected runtime obtained from the actual exponential tail

The integer shift preserves the closed-tail endpoint, including infinite times.
The following application uses RuntimeTailAtTime and the generic expectation
bridge; no earlier expected-runtime or termination theorem is invoked.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- Integer strict/closed conversion in WithTop Nat, including infinite times. -/
private theorem ClosedRuntimeEndpoint (c j : Nat) (T : WithTop Nat) :
    ((c + 1 + j : Nat) : WithTop Nat) ≤ T ↔
      ((c + j : Nat) : WithTop Nat) < T := by
  have Index : c + 1 + j = (c + j) + 1 := by omega
  rw [Index]
  change (((c + j) + 1 : Nat) : ENat) ≤ T ↔ ((c + j : Nat) : ENat) < T
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ENat.natCast_add_one_le_iff (m := c + j) (n := T))

/-- The actual strict RLS tail, shifted by one to the core's closed integer
endpoint. The pure initial mean zero count is evaluated, not postulated. -/
theorem FixedClosedRuntimeTailOfExponentialTail {n : Nat}
    (PositiveLength : 0 < n) (InitialState : Bits n)
    (InitialPositive : 0 < ZeroCount InitialState) (j : Nat) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | ((⌈(n : ℝ) * Real.log (ZeroCount InitialState : ℝ)⌉₊ + 1 + j : Nat) :
          WithTop Nat) ≤ FirstHittingTime IsTarget Path} ≤
      ENNReal.ofReal (Real.exp (-(j : ℝ) / (n : ℝ))) := by
  let c : Nat := ⌈(n : ℝ) * Real.log (ZeroCount InitialState : ℝ)⌉₊
  have PositiveN : 0 < (n : ℝ) := Nat.cast_pos.mpr PositiveLength
  have PositiveK : 0 < (ZeroCount InitialState : ℝ) := Nat.cast_pos.mpr InitialPositive
  have CeilBound : (n : ℝ) * Real.log (ZeroCount InitialState : ℝ) ≤ (c : ℝ) :=
    Nat.le_ceil _
  have LogBound : Real.log (ZeroCount InitialState : ℝ) ≤ (c : ℝ) / (n : ℝ) :=
    (le_div_iff₀ PositiveN).mpr (by simpa only [mul_comm] using CeilBound)
  have ExponentBound :
      -((c + j : Nat) : ℝ) / (n : ℝ) + Real.log (ZeroCount InitialState : ℝ) ≤
        -(j : ℝ) / (n : ℝ) := by
    rw [Nat.cast_add]
    calc
      _ ≤ -((c : ℝ) + (j : ℝ)) / (n : ℝ) + (c : ℝ) / (n : ℝ) :=
        add_le_add le_rfl LogBound
      _ = _ := by ring
  have InitialMean :
      (∫ x, Potential x ∂(PMF.pure InitialState).toMeasure) =
        (ZeroCount InitialState : ℝ) := by
    rw [PMF.toMeasure_pure, integral_dirac]
    rfl
  have Bound := RuntimeTailAtTime PositiveLength (PMF.pure InitialState) (c + j)
  rw [InitialMean] at Bound
  have ExponentialIdentity :
      Real.exp (-((c + j : Nat) : ℝ) / (n : ℝ)) * (ZeroCount InitialState : ℝ) =
        Real.exp (-((c + j : Nat) : ℝ) / (n : ℝ) +
          Real.log (ZeroCount InitialState : ℝ)) := by
    rw [Real.exp_add, Real.exp_log PositiveK]
  rw [ExponentialIdentity] at Bound
  have Events :
      {Path : Nat → Bits n | ((c + 1 + j : Nat) : WithTop Nat) ≤
        FirstHittingTime IsTarget Path} =
      {Path : Nat → Bits n | ((c + j : Nat) : WithTop Nat) <
        FirstHittingTime IsTarget Path} := by
    ext Path
    exact ClosedRuntimeEndpoint c j (FirstHittingTime IsTarget Path)
  change (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
    {Path | ((c + 1 + j : Nat) : WithTop Nat) ≤ FirstHittingTime IsTarget Path} ≤ _
  rw [Events]
  exact Bound.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ExponentBound))

/-- Apply the new tail-to-expectation theorem to the genuine RLS path law.
No integrability, almost-sure termination, or expected-runtime premise is added.
This is an interface validation, not an improvement over the old RLS bound. -/
theorem FixedRuntimeUpperBoundOfExponentialTail {n : Nat}
    (PositiveLength : 0 < n) (InitialState : Bits n)
    (InitialPositive : 0 < ZeroCount InitialState) :
    ExpectedRuntime PositiveLength InitialState ≤
      ENNReal.ofReal
        ((⌈(n : ℝ) * Real.log (ZeroCount InitialState : ℝ)⌉₊ : ℝ) + 1 + (n : ℝ)) := by
  have Tail : ∀ j : Nat, 0 < j →
      (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
        {Path | ((⌈(n : ℝ) * Real.log (ZeroCount InitialState : ℝ)⌉₊ + 1 + j : Nat) :
            WithTop Nat) ≤ FirstHittingTime IsTarget Path} ≤
        ENNReal.ofReal ((1 : ℝ) * Real.exp (-(j : ℝ) / (n : ℝ))) := by
    intro j _PositiveOffset
    simpa only [one_mul] using
      FixedClosedRuntimeTailOfExponentialTail PositiveLength InitialState InitialPositive j
  have Bound := ExpectedWithTopNatLeOfExponentialTail
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
    (FirstHittingTime (IsTarget (n := n)))
    (⌈(n : ℝ) * Real.log (ZeroCount InitialState : ℝ)⌉₊ + 1) 1 (n : ℝ)
    (FirstHittingTimeMeasurable IsTarget) (by norm_num)
    (Nat.cast_pos.mpr PositiveLength) Tail
  simpa only [ExpectedRuntime, ExpectedHittingTime, FirstHittingTimeValue,
    Nat.cast_add, Nat.cast_one, one_mul] using Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax

