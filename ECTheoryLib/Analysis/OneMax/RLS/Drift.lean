import ECTheoryLib.Analysis.OneMax.RLS.Model
import ECTheoryLib.Analysis.OneMax.ElitistBitFlip
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Ring

/-!
# One-step drift of RLS on OneMax

The proofs use the actual problem, mutation, and selection definitions. Flipping
a zero decreases the zero-count potential by one; flipping a one is rejected.
Consequently the exact expected decrease at state `x` is `Potential x / n`.
Coordinate identities and deterministic selection facts come from shared OneMax modules.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability

noncomputable section
/-- OneMax-maximizing RLS accepts a zero-to-one flip. -/
theorem RLSAcceptsZeroFlip {n : Nat}
    (x : Bits n) (i : Fin n) (BitIsZero : x i = false) :
    Update x i = OnebitMutation x i := by
  exact OneMax.ElitistAcceptsZeroFlip x i BitIsZero

/-- OneMax-maximizing RLS rejects a one-to-zero flip. -/
theorem RLSRejectsOneFlip {n : Nat}
    (x : Bits n) (i : Fin n) (BitIsOne : x i = true) :
    Update x i = x := by
  exact OneMax.ElitistRejectsOneFlip x i BitIsOne

/-- Each deterministic elitist update preserves zero potential. -/
theorem UpdatePreservesZero {n : Nat} (x : Bits n) (i : Fin n)
    (ParentZero : Potential x = 0) :
    Potential (Update x i) = 0 := by
  exact OneMax.ElitistBitFlipPreservesZero x i ParentZero

/-- A complete update decreases potential by one for a zero coordinate
and by zero for a one coordinate. -/
theorem PotentialDecrease {n : Nat} (x : Bits n) (i : Fin n) :
    Potential x - Potential (Update x i) =
      if x i then 0 else 1 := by
  exact OneMax.ElitistBitFlipDecrease x i

/-- Every genuine RLS transition has zero-count decrease zero or one. -/
theorem StepPotentialDecreaseBinary {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, Potential x-Potential y=0 ∨ Potential x-Potential y=1 := by
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
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Exact expected one-step decrease: zero count divided by string length. -/
theorem OneStepDrift {n : Nat} (PositiveLength : 0 < n) (x : Bits n) :
    (∫ y, Potential x - Potential y
      ∂(Step PositiveLength x).toMeasure) =
        Potential x / (n : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, PositiveLength⟩⟩
  rw [Step, RLSStepEqUniformUpdate]
  change
    (∫ y, Potential x - Potential y
      ∂((PMF.uniformOfFintype (Fin n)).map (Update x)).toMeasure) =
        Potential x / (n : ℝ)
  rw [← PMF.toMeasure_map (Update x) (PMF.uniformOfFintype (Fin n))
    (measurable_of_finite (Update x))]
  rw [integral_map_of_stronglyMeasurable (measurable_of_finite (Update x))
    (measurable_of_finite
      (fun y : Bits n => Potential x -
        Potential y)).stronglyMeasurable]
  rw [PMF.integral_eq_sum]
  have UniformWeight : ∀ i : Fin n,
      ((PMF.uniformOfFintype (Fin n)) i).toReal = 1 / (n : ℝ) := by
    intro i
    rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact (one_div (n : ℝ)).symm
  change
    (∑ i : Fin n, ((PMF.uniformOfFintype (Fin n)) i).toReal *
      (Potential x - Potential (Update x i))) =
        Potential x / (n : ℝ)
  have AverageOverPositions :
      (∑ i : Fin n, ((PMF.uniformOfFintype (Fin n)) i).toReal *
        (Potential x - Potential (Update x i))) =
          ∑ i : Fin n, (1 / (n : ℝ)) * (if x i then (0 : ℝ) else 1) := by
    apply Finset.sum_congr rfl
    intro i _Membership
    rw [UniformWeight, PotentialDecrease]
  rw [AverageOverPositions, ← Finset.mul_sum, Problems.OneMax.ZeroBitCountAsReal]
  unfold Potential ZeroCount
  ring

/-- The same local drift identity in the public finite-sum ExpectedDecrease
representation, connected to the integral formula. -/
theorem ExpectedDecreaseEqPotentialDivLength {n : Nat}
    (PositiveLength : 0 < n) (x : Bits n) :
    ExpectedDecrease (Step PositiveLength) Potential x = Potential x / (n : ℝ) := by
  have IntegralDrift := OneStepDrift PositiveLength x
  rw [PMF.integral_eq_sum] at IntegralDrift
  exact IntegralDrift

/-- Every non-target string has at least one zero and satisfies the
coarse additive-drift lower-bound specification. -/
theorem OneStepDriftLowerBoundProof {n : Nat} (PositiveLength : 0 < n) :
    OneStepDriftLowerBound PositiveLength := by
  intro x NotTarget
  have ZeroCountNonzero : ZeroCount x ≠ 0 := by
    intro CountZero
    apply NotTarget
    apply (PotentialEqZeroIffTarget x).mp
    unfold Potential
    rw [CountZero, Nat.cast_zero]
  have PotentialAtLeastOne : (1 : ℝ) ≤ Potential x := by
    unfold Potential
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr ZeroCountNonzero
  rw [ExpectedDecreaseEqPotentialDivLength PositiveLength x]
  exact div_le_div_of_nonneg_right PotentialAtLeastOne
    (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))

end
end ECTheoryLib.Analysis.RLSOnOneMax
