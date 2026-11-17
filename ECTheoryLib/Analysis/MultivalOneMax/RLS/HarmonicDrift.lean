import ECTheoryLib.Analysis.MultivalOneMax.RLS.Drift
import ECTheoryLib.Tools.Runtime.Harmonic

/-!
# Exact harmonic drift of interval-distance RLS

Selection minimizes the sum of coordinate interval distances; the analysis
potential is a harmonic function of Hamming distance. Each mismatched coordinate
has exactly one replacement that decreases the Hamming level. Other accepted
replacements may change the search point while leaving its Hamming level fixed.
Harmonic numbers come from mathlib; their real-valued positivity properties are
reused through Tools.Runtime.Harmonic, independently of the binary analysis.
The one-step identity corresponds to equation (1) in the proof of Theorem 6,
Doerr, Doerr, and Koetzing (2018), Algorithmica 80:1732–1768.
-/

namespace ECTheoryLib.Analysis.RLSMultival

open MeasureTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax

noncomputable section

/-- Actual RLS kernel: uniform different-value replacement, accepting
nonincreasing interval-distance objective. -/
def Step {n r : Nat} (PositiveLength : 0 < n) (AlphabetSize : 2 ≤ r)
    (Target : MultiValues n r) : Transition (MultiValues n r) :=
  MultivalRLSStep PositiveLength AlphabetSize (Problems.MinNotWorse (Distance Target))

/-- The `n(r-1)` legal coordinate-and-value choices have equal probability. -/
def RuntimeScale (n r : Nat) : ℝ := ((n * (r - 1) : Nat) : ℝ)

theorem RuntimeScalePositive {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) : 0 < RuntimeScale n r := by
  apply Nat.cast_pos.mpr
  exact Nat.mul_pos PositiveLength (by omega)

/-- Scaled harmonic potential `n(r-1)H_k`, whose initial value will equal
the expected runtime after the unit-drift argument. -/
def HarmonicPotential {n r : Nat} (Target State : MultiValues n r) : ℝ :=
  RuntimeScale n r * (harmonic (Hamming Target State) : ℝ)

theorem HarmonicPotentialNonnegative {n r : Nat} (Target State : MultiValues n r) :
    0 ≤ HarmonicPotential Target State := by
  exact mul_nonneg (Nat.cast_nonneg _) (Tools.Runtime.HarmonicNonnegative _)

theorem HarmonicPotentialEqZeroIff {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target State : MultiValues n r) :
    HarmonicPotential Target State = 0 ↔ Hamming Target State = 0 := by
  constructor
  · intro PotentialZero
    by_contra CountNonzero
    have PotentialPositive : 0 < HarmonicPotential Target State := by
      exact mul_pos (RuntimeScalePositive PositiveLength AlphabetSize)
        (Tools.Runtime.HarmonicPositive (Nat.pos_of_ne_zero CountNonzero))
    exact (ne_of_gt PotentialPositive) PotentialZero
  · intro CountZero
    unfold HarmonicPotential
    rw [CountZero, harmonic_zero, Rat.cast_zero, mul_zero]

/-- A specified replacement decreases the harmonic potential by either
`n(r-1)/k` or zero. -/
theorem HarmonicPotentialDecrease {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) :
    HarmonicPotential Target State - HarmonicPotential Target (Update Target State i v) =
      if State i ≠ Target i ∧ v = Target i then
        RuntimeScale n r / (Hamming Target State : ℝ) else 0 := by
  have CountDecrease := HammingDecrease Target State i v
  by_cases Success : State i ≠ Target i ∧ v = Target i
  · rw [if_pos Success] at CountDecrease ⊢
    have CountSuccessor : Hamming Target State = Hamming Target (Update Target State i v) + 1 := by
      have CastSuccessor : (Hamming Target State : ℝ) =
          (Hamming Target (Update Target State i v) : ℝ) + 1 := by linarith
      exact_mod_cast CastSuccessor
    unfold HarmonicPotential
    rw [CountSuccessor, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
      div_eq_mul_inv]
    ring
  · rw [if_neg Success] at CountDecrease ⊢
    have CountsEqual : Hamming Target State = Hamming Target (Update Target State i v) := by
      exact_mod_cast sub_eq_zero.mp CountDecrease
    unfold HarmonicPotential
    rw [CountsEqual, sub_self]

/-- Each mismatched coordinate has exactly one successful replacement,
so the number of successful choices equals the Hamming distance. -/
theorem SuccessfulChoiceSum {n r : Nat} (Target State : MultiValues n r) :
    (∑ c : CoordinateChoice State,
      if State c.1 ≠ Target c.1 ∧ c.2.val = Target c.1 then (1 : ℝ) else 0) =
      (Hamming Target State : ℝ) := by
  change (∑ c : (i : Fin n) × {v : Fin r // v ≠ State i},
    if State c.1 ≠ Target c.1 ∧ c.2.val = Target c.1 then (1 : ℝ) else 0) = _
  rw [Fintype.sum_sigma]
  unfold Hamming
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _InUniv
  by_cases Correct : State i = Target i
  · simp only [Correct, ne_eq, not_true_eq_false, false_and, ite_false,
      Finset.sum_const_zero, ite_true, Nat.cast_zero]
  · rw [if_neg Correct, Nat.cast_one]
    let TargetChoice : {v : Fin r // v ≠ State i} := ⟨Target i, Ne.symm Correct⟩
    have IsTarget : ∀ v : {v : Fin r // v ≠ State i},
        v.val = Target i ↔ v = TargetChoice := by
      intro v
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    simp only [ne_eq, Correct, not_false_eq_true, true_and, IsTarget]
    simp

/-- Equation (1) in Doerr, Doerr, and Koetzing (2018), Theorem 6's proof:
the actual one-step Hamming drift is `k/[n(r-1)]`. -/
theorem OneStepHammingDrift {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target State : MultiValues n r) :
    (∫ Next, (Hamming Target State : ℝ) - (Hamming Target Next : ℝ)
      ∂(Step PositiveLength AlphabetSize Target State).toMeasure) =
      (Hamming Target State : ℝ) / RuntimeScale n r := by
  rw [Step, MultivalRLSStepIntegral]
  change (1 / RuntimeScale n r) *
    (∑ c : CoordinateChoice State,
      ((Hamming Target State : ℝ) - (Hamming Target (Update Target State c.1 c.2.val) : ℝ))) = _
  simp_rw [HammingDecrease]
  rw [SuccessfulChoiceSum]
  ring

/-- The Hamming level decreases exactly when a mismatched coordinate is
replaced directly by its target value. -/
theorem UpdateHammingDecreaseIff {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) :
    Hamming Target (Update Target State i v) + 1 = Hamming Target State ↔
      State i ≠ Target i ∧ v = Target i := by
  have Balance := HammingUpdateDecrease Target State i v
  constructor
  · intro Decreased
    by_contra NoRepair
    rw [if_neg NoRepair] at Balance
    omega
  · intro Repair
    rw [if_pos Repair] at Balance
    exact Balance

/-- Under the actual one-step measure, a one-level decrease has probability
`k/[n(r-1)]`, including zero when already at the target. -/
theorem OneStepHammingDecreaseProbability {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target State : MultiValues n r) :
    (Step PositiveLength AlphabetSize Target State).toMeasure.real
      {Next | Hamming Target Next + 1 = Hamming Target State} =
      (Hamming Target State : ℝ) / RuntimeScale n r := by
  have EventMeasurable : MeasurableSet
      {Next : MultiValues n r | Hamming Target Next + 1 = Hamming Target State} := by
    exact (Set.to_countable _).measurableSet
  rw [← integral_indicator_one EventMeasurable]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  rw [Step, MultivalRLSStepIntegral]
  change (1 / RuntimeScale n r) *
    (∑ c : CoordinateChoice State,
      if Hamming Target (Update Target State c.1 c.2.val) + 1 = Hamming Target State
        then (1 : ℝ) else 0) = _
  simp only [UpdateHammingDecreaseIff]
  rw [SuccessfulChoiceSum]
  ring

/-- The successor's Hamming level is unchanged or decreases by one.
An unchanged level does not assert an unchanged search point. -/
theorem StepHammingLevels {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target State : MultiValues n r) :
    ∀ᵐ Next ∂(Step PositiveLength AlphabetSize Target State).toMeasure,
      Hamming Target Next = Hamming Target State ∨
        Hamming Target Next + 1 = Hamming Target State := by
  apply MultivalRLSStepProperty PositiveLength AlphabetSize
    (Problems.MinNotWorse (Distance Target)) State
  intro c
  have Balance := HammingUpdateDecrease Target State c.1 c.2.val
  by_cases Success : State c.1 ≠ Target c.1 ∧ c.2.val = Target c.1
  · rw [if_pos Success] at Balance
    exact Or.inr Balance
  · rw [if_neg Success, Nat.add_zero] at Balance
    exact Or.inl Balance

/-- The actual level transition makes zero Hamming distance absorbing almost surely. -/
theorem StepPreservesZeroHamming {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target State : MultiValues n r) :
    ∀ᵐ Next ∂(Step PositiveLength AlphabetSize Target State).toMeasure,
      Hamming Target State = 0 → Hamming Target Next = 0 := by
  filter_upwards [StepHammingLevels PositiveLength AlphabetSize Target State] with Next Levels
  intro ParentZero
  rcases Levels with Same | Lower
  · exact Same.trans ParentZero
  · omega

/-- At every non-target state the harmonic potential has exact expected
one-step decrease one under the actual kernel. -/
theorem OneStepHarmonicDrift {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target State : MultiValues n r) :
    (∫ Next, HarmonicPotential Target State - HarmonicPotential Target Next
      ∂(Step PositiveLength AlphabetSize Target State).toMeasure) =
      if Hamming Target State = 0 then 0 else 1 := by
  rw [Step, MultivalRLSStepIntegral]
  change (1 / RuntimeScale n r) *
    (∑ c : CoordinateChoice State,
      (HarmonicPotential Target State - HarmonicPotential Target (Update Target State c.1 c.2.val))) = _
  have EachTerm : ∀ c : CoordinateChoice State,
      HarmonicPotential Target State - HarmonicPotential Target (Update Target State c.1 c.2.val) =
        (RuntimeScale n r / (Hamming Target State : ℝ)) *
          (if State c.1 ≠ Target c.1 ∧ c.2.val = Target c.1 then 1 else 0) := by
    intro c
    rw [HarmonicPotentialDecrease]
    by_cases Success : State c.1 ≠ Target c.1 ∧ c.2.val = Target c.1
    · rw [if_pos Success, if_pos Success, mul_one]
    · rw [if_neg Success, if_neg Success, mul_zero]
  simp_rw [EachTerm]
  rw [← Finset.mul_sum, SuccessfulChoiceSum]
  by_cases CountZero : Hamming Target State = 0
  · rw [if_pos CountZero, CountZero, Nat.cast_zero, mul_zero, mul_zero]
  · rw [if_neg CountZero]
    have ScaleNonzero := ne_of_gt (RuntimeScalePositive PositiveLength AlphabetSize)
    have CountNonzero : (Hamming Target State : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr CountZero
    field_simp

end
end ECTheoryLib.Analysis.RLSMultival
