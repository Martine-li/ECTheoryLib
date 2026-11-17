import ECTheoryLib.Analysis.LeadingOnes.RLS.TranslatedDrift
import ECTheoryLib.Tools.Drift.Additive

/-!
# Exact uniform-start RLS runtime on LeadingOnes

Example 2.3.2 in Lengler's Drift Analysis (pp. 97-99): E[T]=n^2/2 for n>0,
with time zero at the uniform initial state and weak elitist selection.
The existing additive upper and lower theorems coincide after the actual
conditional drift, nonnegative finite range, zero absorption, initial mean n,
and goal/hitting-time correspondence are all verified. Optimal initial mass
is included. No finite-runtime hypothesis or surrogate scalar Markov model
is used.
-/


namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- Example 2.3.2: the actual weak-selection RLS kernel with uniform initial
state has exact mean n^2/2 mutation iterations. Initialization itself is time 0. -/
theorem UniformRuntimeExact {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (RLSInit n) = ENNReal.ofReal ((n : ℝ)^2 / 2) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (RLSInit n)
  let X : ℕ → (ℕ → Bits n) → ℝ := fun t Path => TranslatedPotential (Path t)
  let S : Finset ℝ := insert 0 (Finset.univ.image (@TranslatedPotential n))
  have MeasurableX : ∀ t, Measurable (X t) :=
    fun t => (measurable_of_finite (@TranslatedPotential n)).comp (measurable_pi_apply t)
  have ZeroInS : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have StatesNonnegative : ∀ s ∈ S, 0 ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | InImage
    · rw [Zero]
    · obtain ⟨x, _InUniv, Value⟩ := Finset.mem_image.mp InImage
      rw [← Value]
      exact TranslatedPotentialNonnegative x
  have ValuesInS : ∀ t Path, X t Path ∈ S := by
    intro t Path
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩
  have StepPreservesZero : ∀ x, ∀ᵐ y ∂(Step PositiveLength x).toMeasure,
      TranslatedPotential x = 0 → TranslatedPotential y = 0 := by
    intro x
    filter_upwards [StepPotentialNonincreasing PositiveLength x] with y Decrease
    intro Zero
    have XTarget := (TranslatedPotentialZeroIffTarget x).mp Zero
    have XDeficitZero := (PotentialZeroIffTarget x).mpr XTarget
    rw [XDeficitZero] at Decrease
    have YDeficitZero := le_antisymm Decrease (PotentialNonnegative y)
    exact (TranslatedPotentialZeroIffTarget y).mpr ((PotentialZeroIffTarget y).mp YDeficitZero)
  have Absorbing : ZeroIsAbsorbing μ X := by
    intro t
    exact PathMeasureFollowsTransition (Step PositiveLength) (RLSInit n)
      (fun x y => TranslatedPotential x = 0 → TranslatedPotential y = 0) StepPreservesZero t
  have DeltaPositive : 0 < 2 / (n : ℝ) := div_pos (by norm_num) (Nat.cast_pos.mpr PositiveLength)
  have DriftLower : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      2 / (n : ℝ) ≤ StateDrift μ X t s := by
    intro t s _InS Nonzero Positive
    exact (UniformTranslatedStateDrift PositiveLength t s Nonzero Positive).symm.le
  have DriftUpper : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      StateDrift μ X t s ≤ 2 / (n : ℝ) := by
    intro t s _InS Nonzero Positive
    exact (UniformTranslatedStateDrift PositiveLength t s Nonzero Positive).le
  have InitialMean : ExpectedValue μ (X 0) = (n : ℝ) := by
    change (∫ Path, TranslatedPotential (Path 0) ∂μ) = _
    rw [PathMeasureInitialIntegral]
    exact UniformTranslatedPotentialExpectation n
  have Upper := AdditiveDriftUpperBound μ X S (2 / (n : ℝ)) MeasurableX ZeroInS
    StatesNonnegative ValuesInS Absorbing DeltaPositive DriftLower
  have Lower := AdditiveDriftLowerBound μ X S (2 / (n : ℝ)) MeasurableX ZeroInS
    StatesNonnegative ValuesInS Absorbing DeltaPositive DriftUpper
  rw [InitialMean] at Upper Lower
  have ZeroRuntime : ExpectedZeroHittingTime μ X = ENNReal.ofReal ((n : ℝ) / (2 / n)) :=
    le_antisymm Upper Lower
  rw [ExpectedRuntime, ExpectedHittingTimeEqExpectedZero (Step PositiveLength) (RLSInit n)
    TranslatedPotential (fun x => x = AllOnes n) TranslatedPotentialZeroIffTarget]
  change ExpectedZeroHittingTime μ X = _
  rw [ZeroRuntime]
  congr 1
  rw [div_div_eq_mul_div, pow_two]

/-- The same exact mean in real notation; finiteness follows from the theorem. -/
theorem UniformRuntimeExactReal {n : ℕ} (PositiveLength : 0 < n) :
    (ExpectedRuntime PositiveLength (RLSInit n)).toReal = (n : ℝ)^2 / 2 := by
  rw [UniformRuntimeExact PositiveLength, ENNReal.toReal_ofReal (by positivity)]

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes
