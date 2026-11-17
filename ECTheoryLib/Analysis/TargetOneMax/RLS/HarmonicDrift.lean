import ECTheoryLib.Analysis.TargetOneMax.RLS.Drift
import ECTheoryLib.Tools.Runtime.Harmonic

/-!
# Exact harmonic-potential drift for binary RLS

The potential uses mathlib's rational harmonic number, cast to the reals.
The actual Hamming RLS kernel is reused.  Each incorrect coordinate reduces
the count by one, and its harmonic-potential decrease is n / k.
-/

namespace ECTheoryLib.Analysis.RLSHamming

open MeasureTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax

noncomputable section

/-- The real harmonic-number potential for the exact binary RLS runtime. -/
def HarmonicPotential {n : Nat} (Target State : Bits n) : ℝ :=
  (n : ℝ) * (harmonic (Hamming Target State) : ℝ)

theorem HarmonicPotentialNonnegative {n : Nat} (Target State : Bits n) :
    0 ≤ HarmonicPotential Target State := by
  exact mul_nonneg (Nat.cast_nonneg n) (Tools.Runtime.HarmonicNonnegative _)

theorem HarmonicPotentialEqZeroIff {n : Nat} (PositiveLength : 0 < n)
    (Target State : Bits n) :
    HarmonicPotential Target State = 0 ↔ Hamming Target State = 0 := by
  constructor
  · intro PotentialZero
    by_contra CountNonzero
    have CountPositive : 0 < Hamming Target State := Nat.pos_of_ne_zero CountNonzero
    have PotentialPositive : 0 < HarmonicPotential Target State := by
      exact mul_pos (Nat.cast_pos.mpr PositiveLength) (Tools.Runtime.HarmonicPositive CountPositive)
    exact (ne_of_gt PotentialPositive) PotentialZero
  · intro CountZero
    unfold HarmonicPotential
    rw [CountZero, harmonic_zero, Rat.cast_zero, mul_zero]

/-- The old encoded OneMax drift identifies the actual Hamming count's change. -/
theorem HammingDecrease {n : Nat} (Target State : Bits n) (i : Fin n) :
    (Hamming Target State : ℝ) - (Hamming Target (Update Target State i) : ℝ) =
      if State i = Target i then 0 else 1 := by
  have EncodedDecrease := RLSOnOneMax.PotentialDecrease (Encode Target State) i
  rw [← EncodeUpdate Target State i, ← PotentialEqEncodedPotential,
    ← PotentialEqEncodedPotential] at EncodedDecrease
  by_cases Agreement : State i = Target i
  · have EncodedBit : Encode Target State i = true := by
      unfold Encode
      exact decide_eq_true Agreement
    rw [EncodedBit] at EncodedDecrease
    rw [if_pos Agreement]
    exact EncodedDecrease
  · have EncodedBit : Encode Target State i = false := by
      unfold Encode
      exact decide_eq_false Agreement
    rw [EncodedBit] at EncodedDecrease
    rw [if_neg Agreement]
    exact EncodedDecrease

/-- Harmonic-potential decrease for a specified uniformly chosen coordinate. -/
theorem HarmonicPotentialDecrease {n : Nat} (Target State : Bits n) (i : Fin n) :
    HarmonicPotential Target State - HarmonicPotential Target (Update Target State i) =
      if State i = Target i then 0 else (n : ℝ) / (Hamming Target State : ℝ) := by
  have CountDecrease := HammingDecrease Target State i
  by_cases Agreement : State i = Target i
  · rw [if_pos Agreement] at CountDecrease ⊢
    have CountsEqual : Hamming Target State = Hamming Target (Update Target State i) := by
      exact_mod_cast sub_eq_zero.mp CountDecrease
    unfold HarmonicPotential
    rw [CountsEqual, sub_self]
  · rw [if_neg Agreement] at CountDecrease ⊢
    have CountSuccessor :
        Hamming Target State = Hamming Target (Update Target State i) + 1 := by
      have CastSuccessor : (Hamming Target State : ℝ) =
          (Hamming Target (Update Target State i) : ℝ) + 1 := by
        linarith
      exact_mod_cast CastSuccessor
    unfold HarmonicPotential
    rw [CountSuccessor, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
    rw [div_eq_mul_inv]
    ring

/-- The sum of real mismatch indicators equals the natural Hamming count. -/
theorem MismatchSumAsReal {n : Nat} (Target State : Bits n) :
    (∑ i : Fin n, if State i = Target i then (0 : ℝ) else 1) =
      (Hamming Target State : ℝ) := by
  unfold Hamming
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _Membership
  by_cases Agreement : State i = Target i
  · rw [if_pos Agreement, if_pos Agreement, Nat.cast_zero]
  · rw [if_neg Agreement, if_neg Agreement, Nat.cast_one]

/-- The exact harmonic drift is one before the target and zero at the target. -/
theorem OneStepHarmonicDrift {n : Nat} (PositiveLength : 0 < n)
    (Target State : Bits n) :
    (∫ Next, HarmonicPotential Target State - HarmonicPotential Target Next
      ∂(Step PositiveLength Target State).toMeasure) =
      if Hamming Target State = 0 then 0 else 1 := by
  let : Nonempty (Fin n) := ⟨⟨0, PositiveLength⟩⟩
  rw [Step, RLSStepEqUniformUpdate]
  rw [← PMF.toMeasure_map (Update Target State) (UniformBitIndex n PositiveLength)
    (measurable_of_finite (Update Target State))]
  rw [integral_map_of_stronglyMeasurable
    (measurable_of_finite (Update Target State))
    (measurable_of_finite
      (fun Next : Bits n => HarmonicPotential Target State -
        HarmonicPotential Target Next)).stronglyMeasurable]
  rw [PMF.integral_eq_sum]
  have UniformWeight : ∀ i : Fin n,
      (UniformBitIndex n PositiveLength i).toReal = 1 / (n : ℝ) := by
    intro i
    rw [UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact (one_div (n : ℝ)).symm
  change
    (∑ i : Fin n, (UniformBitIndex n PositiveLength i).toReal *
      (HarmonicPotential Target State -
        HarmonicPotential Target (Update Target State i))) =
      if Hamming Target State = 0 then 0 else 1
  have AverageDecrease :
      (∑ i : Fin n, (UniformBitIndex n PositiveLength i).toReal *
        (HarmonicPotential Target State -
          HarmonicPotential Target (Update Target State i))) =
        (1 / (n : ℝ)) * ((n : ℝ) / (Hamming Target State : ℝ)) *
          (Hamming Target State : ℝ) := by
    have EachTerm : ∀ i : Fin n,
        (UniformBitIndex n PositiveLength i).toReal *
          (HarmonicPotential Target State -
            HarmonicPotential Target (Update Target State i)) =
          (1 / (n : ℝ)) * ((n : ℝ) / (Hamming Target State : ℝ)) *
            (if State i = Target i then 0 else 1) := by
      intro i
      rw [UniformWeight, HarmonicPotentialDecrease]
      by_cases Agreement : State i = Target i
      · rw [if_pos Agreement, if_pos Agreement, mul_zero, mul_zero]
      · rw [if_neg Agreement, if_neg Agreement, mul_one]
    simp_rw [EachTerm]
    rw [← Finset.mul_sum, MismatchSumAsReal]
  rw [AverageDecrease]
  by_cases CountZero : Hamming Target State = 0
  · rw [if_pos CountZero, CountZero, Nat.cast_zero, mul_zero]
  · rw [if_neg CountZero]
    have LengthNonzero : (n : ℝ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt PositiveLength)
    have CountNonzero : (Hamming Target State : ℝ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr CountZero
    field_simp

end
end ECTheoryLib.Analysis.RLSHamming
