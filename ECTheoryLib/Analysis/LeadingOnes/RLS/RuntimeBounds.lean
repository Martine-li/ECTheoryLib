import ECTheoryLib.Analysis.LeadingOnes.RLS.Drift
import ECTheoryLib.Tools.Runtime.LocalDrift

/-!
# Additive runtime bounds for actual RLS on LeadingOnes

The generic local-drift interface gives E[T] <= n*E[n-LeadingOnes(X_0)] for
any initial PMF, hence E[T] <= n^2. A fixed initial state needs no distributional
premise. Absorption, the goal correspondence, and local drift are all discharged.
These are the coarse upper bounds in Example 2.3.2, pp. 97-99. The uniform-start
exact mean n^2/2 requires a separate unseen-suffix distribution argument and
is not claimed here. Runtime finiteness is a conclusion, not an assumption.
-/

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Arbitrary initialization, including optimal mass; runtime counts mutation iterations. -/
theorem RuntimeUpperBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤
      ENNReal.ofReal ((n : ℝ) * (∫ x, Potential x ∂Initial.toMeasure)) := by
  have Bound := Tools.Runtime.AdditiveRuntimeUpperBound (Step PositiveLength) Initial Potential
    (fun x => x = AllOnes n) (fun _ => True) PotentialNonnegative PotentialZeroIffTarget
    (ae_of_all _ (fun _ => trivial)) (fun _ => ae_of_all _ (fun _ _ => trivial))
    (by
      intro x
      filter_upwards [StepPotentialNonincreasing PositiveLength x] with y Decreases
      intro _Valid Zero
      rw [Zero] at Decreases
      exact le_antisymm Decreases (PotentialNonnegative y))
    (1 / (n : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr PositiveLength))
    (fun x _Valid Nonzero => OneStepDriftLowerBound PositiveLength x Nonzero)
  rw [div_div_eq_mul_div, div_one, mul_comm] at Bound
  exact Bound

theorem FixedRuntimeUpperBound {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ExpectedRuntime PositiveLength (PMF.pure x) ≤
      ENNReal.ofReal ((n : ℝ) * (n - LeadingOnes x : ℕ)) := by
  have Bound := RuntimeUpperBound PositiveLength (PMF.pure x)
  rw [PMF.toMeasure_pure, integral_dirac] at Bound
  exact Bound

theorem RuntimeQuadraticUpperBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal ((n : ℝ)^2) := by
  apply (RuntimeUpperBound PositiveLength Initial).trans
  apply ENNReal.ofReal_le_ofReal
  have MeanBound : (∫ x, Potential x ∂Initial.toMeasure) ≤ (n : ℝ) := by
    have Bound := integral_mono (μ := Initial.toMeasure) (Integrable.of_finite (f := Potential))
      (integrable_const (n : ℝ)) (fun x => Nat.cast_le.mpr (Nat.sub_le n (LeadingOnes x)))
    rw [integral_const, probReal_univ, one_smul] at Bound
    exact Bound
  calc
    _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left MeanBound (Nat.cast_nonneg n)
    _ = _ := (pow_two _).symm

theorem RuntimeFinite {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial < ⊤ :=
  (RuntimeQuadraticUpperBound PositiveLength Initial).trans_lt ENNReal.ofReal_lt_top

theorem OptimalRuntimeZero {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (PMF.pure (AllOnes n)) = 0 :=
  ExpectedHittingTimeOfPureTarget (Step PositiveLength) (fun x => x = AllOnes n) (AllOnes n) rfl

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes
