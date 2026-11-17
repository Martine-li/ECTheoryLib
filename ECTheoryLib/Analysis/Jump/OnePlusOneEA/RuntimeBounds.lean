import ECTheoryLib.Analysis.Jump.OnePlusOneEA.PhaseGeometry
import ECTheoryLib.Operators.Mutation.BitPattern
import ECTheoryLib.Tools.Runtime.Phases
import ECTheoryLib.Tools.Runtime.Cost

/-!
# Two-phase expected runtime of the (1+1) EA on Jump

For 1 ≤ k ≤ n, arbitrary initialization is allowed, including the fitness valley.
The first phase uses H_(n-Jump(x))/delta, where delta is the exact one-bit event
probability. On the plateau, the waiting certificate is the reciprocal of the
exact event that flips all k zeros and leaves every one unchanged. The shared
two-phase rule bounds the actual path's first arrival at the unique optimum.
Iterations exclude the initial evaluation; a separate result adds its unit cost.
-/
namespace ECTheoryLib.Analysis.EAJump
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Runtime
noncomputable section

/-- Exact probability of the optimum-producing mutation from the plateau. -/
def GapProbability (n k : ℕ) : ℝ :=
  (1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ (n - k)

/-- Positive crossing probability throughout the stated benchmark domain. -/
theorem GapProbabilityPositive {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    0 < GapProbability n k := StandardPatternProbabilityPositive hk hkn

/-- The optimum differs from x exactly at its zero coordinates. -/
theorem DifferenceToOptimum {n : ℕ} (x : Bits n) :
    BitDifferenceCount x (AllOnes n) = n - OneMax x := by
  unfold BitDifferenceCount
  rw [← Problems.OneMax.ZeroBitCount x, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [AllOnes]

/-- At any nonoptimal state in the second phase, the actual mutation's point
probability of the optimum is exactly the gap-crossing probability. -/
theorem PlateauMutationProbability {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n) (x : Bits n) (Inside : Region k x) (NotGoal : x ≠ AllOnes n) :
    (StandardBitMutation hn x (AllOnes n)).toReal = GapProbability n k := by
  have Plateau : OneMax x = n - k := ((RegionIff hk hkn x).mp Inside).resolve_right NotGoal
  rw [StandardBitMutationPatternReal, DifferenceToOptimum, Plateau]
  have Zeros : n - (n - k) = k := by omega
  rw [Zeros]
  rfl

/-- Harmonic progress of the actual Jump kernel is at least delta outside the
region. Distinct single-bit outcomes suffice; all omitted terms are nonnegative. -/
theorem HarmonicDrift {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (x : Bits n) (Outside : ¬ Region k x) :
    StandardOneBitProbability n ≤ ∫ y, (harmonic (Level k x) : ℝ) -
      (harmonic (Level k y) : ℝ) ∂(Step hn k x).toMeasure := by
  change _ ≤ ∫ y, _ ∂((StandardBitMutation hn x).map (Update k x)).toMeasure
  rw [PMFIntegralMap]
  have Bound := PMFIntegralLowerOfInjection (StandardBitMutation hn x)
    (fun y => (harmonic (Level k x) : ℝ) - (harmonic (Level k (Update k x y)) : ℝ))
    (OnebitMutation x) (OnebitMutationInjective x)
    (fun y => sub_nonneg.mpr (HarmonicMonotone (UpdateLevel k x y)))
    (StandardOneBitProbability n) (fun i => (StandardBitMutationOneBitReal hn x i).ge)
  apply le_trans ?_ Bound
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (HarmonicOneBitProgress hk hkn x Outside) (StandardOneBitProbabilityPositive hn).le

/-- First-phase unit-drift certificate; it vanishes upon region entry. -/
def FirstPotential {n : ℕ} (k : ℕ) (x : Bits n) : ℝ :=
  (harmonic (Level k x) : ℝ) / StandardOneBitProbability n

/-- Constant waiting budget away from the optimum, zero at the optimum. Only
its behavior inside the persistent plateau region is used for phase-two drift. -/
def SecondPotential {n : ℕ} (k : ℕ) (x : Bits n) : ℝ :=
  if x = AllOnes n then 0 else 1 / GapProbability n k

/-- A property of every deterministic selected child holds almost surely for
the actual one-step EA kernel. -/
theorem StepAEUpdate {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Bits n)
    (P : Bits n → Prop) (EveryCandidate : ∀ y, P (Update k x y)) :
    ∀ᵐ y ∂(Step hn k x).toMeasure, P y := by
  apply PMFAEOfSupport
  intro y Possible
  rcases (OnePlusOneEAStepSupport hn (Problems.MaxNotWorse (Jump k)) x y).mp Possible with
    ⟨z, _Supported, Selected⟩
  rw [← Selected]
  exact EveryCandidate z

/-- Scaling harmonic progress by its positive event probability gives unit drift. -/
theorem FirstDrift {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (x : Bits n) (Outside : ¬ Region k x) :
    1 ≤ ∫ y, FirstPotential k x - FirstPotential k y ∂(Step hn k x).toMeasure := by
  simp only [FirstPotential, ← sub_div]
  rw [integral_div]
  apply (le_div_iff₀ (StandardOneBitProbabilityPositive hn)).mpr
  simpa only [one_mul] using HarmonicDrift hn hk hkn x Outside

/-- The actual optimum-producing mutation pays for the entire reciprocal
waiting budget. No independent geometric waiting-time model is substituted. -/
theorem SecondDrift {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (x : Bits n) (Inside : Region k x) (NotGoal : x ≠ AllOnes n) :
    1 ≤ ∫ y, SecondPotential k x - SecondPotential k y ∂(Step hn k x).toMeasure := by
  have Positive := GapProbabilityPositive hk hkn
  have AcceptOptimum : Update k x (AllOnes n) = AllOnes n := by
    apply ElitistSelectAccept
    change Jump k x ≤ Jump k (AllOnes n)
    rw [Problems.Jump.JumpAllOnes]
    exact Problems.Jump.JumpLeMax x
  have Nonnegative (y : Bits n) : 0 ≤ SecondPotential k x -
      SecondPotential k (Update k x y) := by
    simp only [SecondPotential, if_neg NotGoal]
    split_ifs
    · simpa only [sub_zero] using (one_div_pos.mpr Positive).le
    · rw [sub_self]
  change _ ≤ ∫ y, _ ∂((StandardBitMutation hn x).map (Update k x)).toMeasure
  rw [PMFIntegralMap]
  have Bound := PMFIntegralLowerOfInjection (ι := Unit) (StandardBitMutation hn x)
    (fun y => SecondPotential k x - SecondPotential k (Update k x y))
    (fun _ => AllOnes n) (fun _ _ _ => Subsingleton.elim _ _) Nonnegative
    (GapProbability n k) (fun _ => (PlateauMutationProbability hn hk hkn x Inside NotGoal).ge)
  simpa [AcceptOptimum, SecondPotential, NotGoal, Positive.ne'] using Bound

/-- Concrete certificates for both Jump phases on the existing EA kernel.
The first phase can be skipped by initialization on the plateau or optimum. -/
def Certificate {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    TwoPhaseCertificate (Step hn k) (fun x => x = AllOnes n) (fun _ => True) (Region k) where
  First := FirstPotential k
  Second := SecondPotential k
  Budget := 1 / GapProbability n k
  BudgetPositive := one_div_pos.mpr (GapProbabilityPositive hk hkn)
  FirstNonnegative := fun x => div_nonneg (HarmonicNonnegative _) (StandardOneBitProbabilityPositive hn).le
  SecondNonnegative := by
    intro x
    unfold SecondPotential
    split_ifs
    · exact le_rfl
    · exact (one_div_pos.mpr (GapProbabilityPositive hk hkn)).le
  SecondZeroIffGoal := by
    intro x
    simp only [SecondPotential]
    split_ifs with Goal
    · exact iff_of_true rfl Goal
    · exact iff_of_false (ne_of_gt (one_div_pos.mpr (GapProbabilityPositive hk hkn))) Goal
  GoalInRegion := by
    intro x Goal
    rw [Goal]
    exact (RegionIff hk hkn _).mpr (Or.inr rfl)
  SecondBound := by
    intro x _
    unfold SecondPotential
    split_ifs
    · exact (one_div_pos.mpr (GapProbabilityPositive hk hkn)).le
    · exact le_rfl
  PreservesValid := fun _ => ae_of_all _ (fun _ _ => trivial)
  PreservesRegion := fun x => StepAEUpdate hn k x _ (fun y _ Inside => UpdateRegion k x y Inside)
  PreservesGoal := fun x => StepAEUpdate hn k x _ (fun y _ Goal => UpdateGoal k x y Goal)
  FirstDrift := fun x _ Outside => FirstDrift hn hk hkn x Outside
  SecondDrift := fun x _ Inside NotGoal => SecondDrift hn hk hkn x Inside NotGoal

/-- Expected iterations to the unique optimum are at most H_n/delta + 1/p_gap
for arbitrary initial PMF, where delta and p_gap are exact mutation probabilities.
The result includes 1 ≤ k ≤ n and n=1, with no assumed finite expectation. -/
theorem RuntimeHarmonicBound {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (Initial : PMF (Bits n)) :
    ExpectedHittingTime (Step hn k) (fun x => x = AllOnes n) Initial ≤
      ENNReal.ofReal ((harmonic n : ℝ) / StandardOneBitProbability n + 1 / GapProbability n k) := by
  apply (Certificate hn hk hkn).RuntimeUniformBound Initial (ae_of_all _ (fun _ => trivial))
  intro x
  exact div_le_div_of_nonneg_right (HarmonicMonotone (Nat.sub_le n _))
    (StandardOneBitProbabilityPositive hn).le

/-- Explicit bound e n (1+log n) + e n^k on the actual expected iteration count.
It separates the time to the plateau from the gap-crossing term and applies to
every initial PMF under 1 ≤ k ≤ n. -/
theorem RuntimeLogBound {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (Initial : PMF (Bits n)) :
    ExpectedHittingTime (Step hn k) (fun x => x = AllOnes n) Initial ≤
      ENNReal.ofReal (Real.exp 1 * (n : ℝ) * (1 + Real.log n) + Real.exp 1 * (n : ℝ) ^ k) := by
  apply (RuntimeHarmonicBound hn hk hkn Initial).trans
  apply ENNReal.ofReal_le_ofReal
  apply add_le_add _ (StandardPatternProbabilityInverseBound hk hkn)
  calc
    (harmonic n : ℝ) / StandardOneBitProbability n =
        (1 / StandardOneBitProbability n) * (harmonic n : ℝ) := by ring
    _ ≤ (Real.exp 1 * (n : ℝ)) * (harmonic n : ℝ) :=
      mul_le_mul_of_nonneg_right (StandardOneBitProbabilityInverseBound hn) (HarmonicNonnegative n)
    _ ≤ (Real.exp 1 * (n : ℝ)) * (1 + Real.log n) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) (by positivity)

/-- Standard uniform initialization discharges all algorithm-specific premises
of the logarithmic plus gap-crossing runtime bound. -/
theorem UniformRuntimeBound {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    ExpectedHittingTime (Step hn k) (fun x => x = AllOnes n) (OnePlusOneEAInit n) ≤
      ENNReal.ofReal (Real.exp 1 * (n : ℝ) * (1 + Real.log n) + Real.exp 1 * (n : ℝ) ^ k) :=
  RuntimeLogBound hn hk hkn (OnePlusOneEAInit n)

/-- One initial fitness evaluation and one evaluation per mutation iteration
give exactly one plus the expected iteration count. -/
theorem EvaluationCostEq {n : ℕ} (hn : 0 < n) (k : ℕ) (Initial : PMF (Bits n)) :
    ExpectedEvaluationCost (Step hn k) (fun x => x = AllOnes n) Initial 1 1 =
      1 + ExpectedHittingTime (Step hn k) (fun x => x = AllOnes n) Initial := by
  rw [ExpectedEvaluationCostEq]
  simp only [Nat.cast_one, one_mul]

/-- The exact probability formula gives a finite expected runtime, even when
the supplied initial distribution includes valley states or the optimum. -/
theorem RuntimeFinite {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (Initial : PMF (Bits n)) :
    ExpectedHittingTime (Step hn k) (fun x => x = AllOnes n) Initial < ⊤ :=
  lt_of_le_of_lt (RuntimeHarmonicBound hn hk hkn Initial) ENNReal.ofReal_lt_top

end
end ECTheoryLib.Analysis.EAJump
