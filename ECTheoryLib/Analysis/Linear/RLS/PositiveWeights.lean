import ECTheoryLib.Problems.Linear
import ECTheoryLib.Analysis.TargetOneMax.RLS.ExactRuntime
import ECTheoryLib.Probability.Processes.InitialMixture
import Mathlib.Tactic.Linarith

/-!
# One-bit RLS minimizing a strictly positive linear objective

The actual kernel proposes a uniformly chosen one-bit flip and applies weak
minimization selection. Strictly positive weights imply equality with Hamming minimization toward
the all-zero string, although comparisons on arbitrary pairs need not agree.
The fixed-state harmonic runtime and count drift reuse existing Hamming RLS
theorems. Extended total expectation includes every initial PMF and its
initially optimal mass; iterations exclude the initial evaluation.

This supplies the model-transfer part of Example 2.3.7 in Lengler's chapter.
BinVal's indexed weights, fitness drift, rescaling and uniform asymptotic
comparison remain separate obligations. No multi-bit EA transfer is asserted.
-/

namespace ECTheoryLib.Analysis.RLSLinear

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open ECTheoryLib.Problems.TargetOneMax
open scoped BigOperators

noncomputable section

/-- The existing actual one-bit RLS kernel, with linear-score minimization.
The definition permits signed weights; transfer theorems require positivity. -/
def Step {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ) : Transition (Bits n) :=
  RLSStep PositiveLength (Problems.MinNotWorse (Score w))

/-- Extended first score-zero hitting time, measured in mutation iterations.
For strictly positive weights score-zero is exactly the all-zero optimum. -/
def ExpectedRuntime {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Initial : PMF (Bits n)) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength w) (fun x => Score w x = 0) Initial

theorem ScoreNonnegative {n : ℕ} (w : Fin n → ℝ) (Nonnegative : ∀ i, 0 ≤ w i)
    (x : Bits n) : 0 ≤ Score w x := by
  apply Finset.sum_nonneg
  intro i _
  cases x i <;> simp [Nonnegative i]

/-- Strict positivity is needed for uniqueness of the score-zero target. -/
theorem ScoreZeroIff {n : ℕ} (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i)
    (x : Bits n) : Score w x = 0 ↔ x = fun _ => false := by
  constructor
  · intro Zero
    have Terms : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        w i * (if x i then 1 else 0 : ℝ) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg _).mp Zero
      intro i _
      cases x i <;> simp [le_of_lt (Positive i)]
    funext i
    have Term := Terms i (Finset.mem_univ i)
    cases Bit : x i with
    | false => rfl
    | true =>
      simp only [Bit, if_true, mul_one] at Term
      exact False.elim ((ne_of_gt (Positive i)) Term)
  · intro Eq
    rw [Eq, ScoreAllZeros]

/-- Hamming distance to the minimization target is the number of one bits. -/
theorem HammingZeroEqOneMax {n : ℕ} (x : Bits n) :
    Hamming (fun _ => false) x = OneMax x := by
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> rfl

/-- The signed score change of one proposed flip, before selection.
This identity needs neither positive weights nor positive string length. -/
theorem MutationScoreDifference {n : ℕ} (w : Fin n → ℝ) (x : Bits n) (i : Fin n) :
    Score w x - Score w (OnebitMutation x i) = if x i then w i else -w i := by
  unfold Score
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [OnebitMutationAt]
    cases x i <;> simp
  · intro j _ Different
    rw [OnebitMutationAway x i j Different, sub_self]
  · intro Absent
    exact False.elim (Absent (Finset.mem_univ i))

/-- A one-to-zero proposal is accepted by the actual weak minimization rule. -/
theorem UpdateAtOne {n : ℕ} (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i)
    (x : Bits n) (i : Fin n) (One : x i = true) :
    RLSUpdate (Problems.MinNotWorse (Score w)) x i = OnebitMutation x i := by
  have Difference := MutationScoreDifference w x i
  rw [One, if_pos rfl] at Difference
  apply ElitistSelectAccept
  change Score w (OnebitMutation x i) ≤ Score w x
  linarith [Positive i]

/-- A zero-to-one proposal is rejected; strict positivity excludes a tie. -/
theorem UpdateAtZero {n : ℕ} (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i)
    (x : Bits n) (i : Fin n) (Zero : x i = false) :
    RLSUpdate (Problems.MinNotWorse (Score w)) x i = x := by
  have Difference := MutationScoreDifference w x i
  rw [Zero, if_neg Bool.false_ne_true] at Difference
  apply ElitistSelectReject
  change ¬ Score w (OnebitMutation x i) ≤ Score w x
  linarith [Positive i]

/-- Exact selected weighted decrement, rather than a statement about proposals. -/
theorem UpdateScoreDecrease {n : ℕ} (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i)
    (x : Bits n) (i : Fin n) :
    Score w x - Score w (RLSUpdate (Problems.MinNotWorse (Score w)) x i) =
      if x i then w i else 0 := by
  cases Bit : x i with
  | false => rw [UpdateAtZero w Positive x i Bit, sub_self]; rfl
  | true =>
    rw [UpdateAtOne w Positive x i Bit, MutationScoreDifference, Bit]
    rfl

/-- Equality concerns actual one-bit updates, not comparisons on arbitrary pairs. -/
theorem UpdateEqHamming {n : ℕ} (w : Fin n → ℝ) (Positive : ∀ i, 0 < w i)
    (x : Bits n) (i : Fin n) :
    RLSUpdate (Problems.MinNotWorse (Score w)) x i =
      RLSHamming.Update (fun _ => false) x i := by
  cases Bit : x i with
  | false =>
    rw [UpdateAtZero w Positive x i Bit]
    symm
    apply ElitistSelectReject
    change ¬ Hamming (fun _ => false) (OnebitMutation x i) ≤ Hamming (fun _ => false) x
    rw [HammingZeroEqOneMax, HammingZeroEqOneMax,
      Analysis.OneMax.OneMaxMutationAtZero x i Bit]
    omega
  | true =>
    rw [UpdateAtOne w Positive x i Bit]
    symm
    apply ElitistSelectAccept
    change Hamming (fun _ => false) (OnebitMutation x i) ≤ Hamming (fun _ => false) x
    rw [HammingZeroEqOneMax, HammingZeroEqOneMax]
    have Difference := Analysis.OneMax.OneMaxMutationAtOne x i Bit
    omega

/-- Exact equality of the actual kernels on the same binary search space. -/
theorem StepEqHamming {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) :
    Step PositiveLength w = RLSHamming.Step PositiveLength (fun _ => false) := by
  funext x
  rw [Step, RLSHamming.Step, RLSStepEqUniformUpdate, RLSStepEqUniformUpdate]
  congr 1
  funext i
  exact UpdateEqHamming w Positive x i

/-- The actual RLS path law transfers with the same arbitrary initial PMF. -/
theorem PathLawEqHamming {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n)) :
    RLSProcess PositiveLength (Problems.MinNotWorse (Score w)) Initial =
      PathMeasure (RLSHamming.Step PositiveLength (fun _ => false)) Initial := by
  change PathMeasure (Step PositiveLength w) Initial = _
  rw [StepEqHamming PositiveLength w Positive]

/-- Both the trajectory kernel and the score-zero goal are transferred. -/
theorem RuntimeEqHamming {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength w Initial =
      ExpectedHittingTime (RLSHamming.Step PositiveLength (fun _ => false))
        (fun x => x = fun _ => false) Initial := by
  unfold ExpectedRuntime
  rw [StepEqHamming PositiveLength w Positive]
  congr 1
  funext x
  exact propext (ScoreZeroIff w Positive x)

/-- Reuse the exact Hamming theorem: from k one bits the mean is n H_k. -/
theorem FixedRuntimeExact {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (x : Bits n) :
    ExpectedRuntime PositiveLength w (PMF.pure x) =
      ENNReal.ofReal ((n : ℝ) * (harmonic (OneMax x) : ℝ)) := by
  rw [RuntimeEqHamming PositiveLength w Positive]
  change RLSHamming.ExpectedRuntime PositiveLength (fun _ => false) x = _
  rw [RLSHamming.FixedRuntimeExact, HammingZeroEqOneMax]

theorem FixedRuntimeFinite {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (x : Bits n) :
    ExpectedRuntime PositiveLength w (PMF.pure x) ≠ ⊤ := by
  rw [RuntimeEqHamming PositiveLength w Positive]
  exact RLSHamming.FixedRuntimeFinite PositiveLength (fun _ => false) x

/-- The real-valued corollary follows from the already finite extended mean. -/
theorem FixedRuntimeExactReal {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (x : Bits n) :
    (ExpectedRuntime PositiveLength w (PMF.pure x)).toReal =
      (n : ℝ) * (harmonic (OneMax x) : ℝ) := by
  rw [RuntimeEqHamming PositiveLength w Positive]
  simpa only [RLSHamming.ExpectedRuntime, HammingZeroEqOneMax] using
    RLSHamming.FixedRuntimeExactReal PositiveLength (fun _ => false) x

/-- Total expectation retains the optimum atom and all other initial states. -/
theorem RuntimeMixture {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength w Initial =
      ∫⁻ x, ENNReal.ofReal ((n : ℝ) * (harmonic (OneMax x) : ℝ)) ∂Initial.toMeasure := by
  unfold ExpectedRuntime
  rw [ExpectedHittingTimeInitialMixture]
  exact lintegral_congr (FixedRuntimeExact PositiveLength w Positive)

/-- Finite-state integrability turns the exact mixture into one real integral. -/
theorem RuntimeHarmonic {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength w Initial =
      ENNReal.ofReal ((n : ℝ) *
        ∫ x, (harmonic (OneMax x) : ℝ) ∂Initial.toMeasure) := by
  rw [RuntimeMixture PositiveLength w Positive]
  have Nonnegative : ∀ x : Bits n, 0 ≤ (n : ℝ) * (harmonic (OneMax x) : ℝ) := by
    intro x
    exact mul_nonneg (Nat.cast_nonneg n) (Tools.Runtime.HarmonicNonnegative _)
  rw [← ofReal_integral_eq_lintegral_ofReal Integrable.of_finite (ae_of_all _ Nonnegative),
    integral_const_mul]

theorem RuntimeFinite {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength w Initial ≠ ⊤ := by
  rw [RuntimeHarmonic PositiveLength w Positive]
  exact ENNReal.ofReal_ne_top

theorem RuntimeExactReal {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (Initial : PMF (Bits n)) :
    (ExpectedRuntime PositiveLength w Initial).toReal =
      (n : ℝ) * ∫ x, (harmonic (OneMax x) : ℝ) ∂Initial.toMeasure := by
  rw [RuntimeHarmonic PositiveLength w Positive, ENNReal.toReal_ofReal]
  apply mul_nonneg (Nat.cast_nonneg n)
  exact integral_nonneg (fun _ => Tools.Runtime.HarmonicNonnegative _)

/-- Initialization at the optimum takes zero mutation iterations. -/
theorem InitialSuccessRuntime {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) :
    ExpectedRuntime PositiveLength w (PMF.pure (fun _ => false)) = 0 := by
  rw [FixedRuntimeExact PositiveLength w Positive]
  simp [OneMax, harmonic_zero]

/-- The actual one-count drift reuses the established Hamming drift, also at zero. -/
theorem OneCountDrift {n : ℕ} (PositiveLength : 0 < n) (w : Fin n → ℝ)
    (Positive : ∀ i, 0 < w i) (x : Bits n) :
    (∫ Next, (OneMax x : ℝ) - (OneMax Next : ℝ) ∂(Step PositiveLength w x).toMeasure) =
      (OneMax x : ℝ) / (n : ℝ) := by
  rw [StepEqHamming PositiveLength w Positive]
  simpa only [RLSHamming.Potential, HammingZeroEqOneMax] using
    RLSHamming.OneStepDrift PositiveLength (fun _ => false) x

end
end ECTheoryLib.Analysis.RLSLinear

