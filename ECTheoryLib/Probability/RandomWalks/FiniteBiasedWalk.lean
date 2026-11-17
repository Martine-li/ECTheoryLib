import ECTheoryLib.Probability.Processes.Transition
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite biased random walk

The state is an integer between zero and N. Zero is absorbing. At an interior
state, the downward probability is (1 + bias)/2. At N, the walk moves downward
with probability bias and otherwise holds, preserving the same expected decrease.
This completes the boundary convention in Lengler, Example 2.4.6 and footnote 22.
The probability law reuses Mathlib's Bernoulli measure and its PMF conversion.
-/

namespace ECTheoryLib.Probability.FiniteBiasedWalk
open MeasureTheory ProbabilityTheory
open scoped unitInterval
noncomputable section

/-- Downward probability giving the prescribed mean decrease in the interior. -/
def InteriorDownProbability (ε : I) : I :=
  ⟨(1+(ε : ℝ))/2, by
    constructor
    · linarith [ε.2.1]
    · linarith [ε.2.2]⟩

def Down {N : ℕ} (x : Fin (N+1)) : Fin (N+1) :=
  ⟨x.val-1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩

def Up {N : ℕ} (x : Fin (N+1)) : Fin (N+1) :=
  ⟨min (x.val+1) N, Nat.lt_succ_iff.mpr (min_le_right _ _)⟩

/-- Absorbing at zero, with an explicit holding law at the upper boundary. -/
def Step (N : ℕ) (ε : I) (x : Fin (N+1)) : PMF (Fin (N+1)) :=
  if x.val=0 then PMF.pure x else
    (bernoulliMeasure (Down x) (Up x) (if x.val=N then ε else InteriorDownProbability ε)).toPMF

/-- Distance to zero, interpreted as a real-valued potential. -/
def Potential {N : ℕ} (x : Fin (N+1)) : ℝ := (x.val : ℝ)

theorem DownPotentialDifference {N : ℕ} (x : Fin (N+1)) (Nonzero : x.val ≠ 0) :
    Potential x-Potential (Down x)=1 := by
  have AtLeastOne : 1 ≤ x.val := Nat.one_le_iff_ne_zero.mpr Nonzero
  simp only [Potential, Down, Nat.cast_sub AtLeastOne, Nat.cast_one]
  ring

theorem UpAtBoundary {N : ℕ} (x : Fin (N+1)) (AtBoundary : x.val=N) : Up x=x := by
  apply Fin.ext
  change min (x.val+1) N=x.val
  rw [AtBoundary, min_eq_right (by omega : N ≤ N+1)]

theorem UpPotentialDifference {N : ℕ} (x : Fin (N+1)) (NotBoundary : x.val ≠ N) :
    Potential x-Potential (Up x)= -1 := by
  have Interior : x.val+1 ≤ N := by have Bound := x.isLt; omega
  simp only [Potential, Up, min_eq_left Interior, Nat.cast_add, Nat.cast_one]
  ring

/-- Both the interior and the explicitly completed upper boundary have drift ε. -/
theorem OneStepDrift (N : ℕ) (ε : I) (x : Fin (N+1)) :
    (∫ y, Potential x-Potential y ∂(Step N ε x).toMeasure) =
      if Potential x=0 then 0 else (ε : ℝ) := by
  by_cases AtZero : x.val=0
  · rw [Step, if_pos AtZero, PMF.toMeasure_pure, integral_dirac]
    have ZeroPotential : Potential x=0 := by simp only [Potential, AtZero, Nat.cast_zero]
    rw [if_pos ZeroPotential, sub_self]
  · have NonzeroPotential : Potential x ≠ 0 := Nat.cast_ne_zero.mpr AtZero
    rw [Step, if_neg AtZero, Measure.toPMF_toMeasure, integral_bernoulliMeasure,
      if_neg NonzeroPotential, DownPotentialDifference x AtZero]
    by_cases AtBoundary : x.val=N
    · rw [if_pos AtBoundary, UpAtBoundary x AtBoundary, sub_self]
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
    · rw [if_neg AtBoundary, UpPotentialDifference x AtBoundary]
      simp only [InteriorDownProbability, smul_eq_mul, mul_one, mul_neg, mul_one]
      ring

theorem StepPreservesZero (N : ℕ) (ε : I) (x : Fin (N+1)) :
    ∀ᵐ y ∂(Step N ε x).toMeasure, Potential x=0 → Potential y=0 := by
  by_cases Zero : Potential x=0
  · have AtZero : x.val=0 := Nat.cast_eq_zero.mp Zero
    rw [Step, if_pos AtZero, PMF.toMeasure_pure]
    have Same : ∀ᵐ y ∂Measure.dirac x, y=x := ae_eq_dirac (fun y : Fin (N+1) => y)
    filter_upwards [Same] with y Equal
    intro _
    rw [Equal]
    exact Zero
  · exact ae_of_all _ (fun _ h => (Zero h).elim)

/-- Every transition has absolute step size at most one, including the upper boundary. -/
theorem StepAbsoluteJumpBound (N : ℕ) (ε : I) (x : Fin (N+1)) :
    ∀ᵐ y ∂(Step N ε x).toMeasure, |Potential x-Potential y| ≤ 1 := by
  by_cases AtZero : x.val=0
  · rw [Step, if_pos AtZero, PMF.toMeasure_pure]
    filter_upwards [ae_eq_dirac (fun y : Fin (N+1) => y)] with y Equal
    change y=x at Equal
    rw [Equal, sub_self, abs_zero]
    exact zero_le_one
  · rw [Step, if_neg AtZero, Measure.toPMF_toMeasure]
    let p := if x.val=N then ε else InteriorDownProbability ε
    have Supported : ∀ᵐ y ∂bernoulliMeasure (Down x) (Up x) p, y=Down x ∨ y=Up x := by
      rw [bernoulliMeasure_def]
      apply ae_add_measure_iff.mpr
      constructor
      · exact Measure.ae_smul_measure ((ae_eq_dirac (fun y : Fin (N+1) => y)).mono (fun y Equal => Or.inl Equal)) _
      · exact Measure.ae_smul_measure ((ae_eq_dirac (fun y : Fin (N+1) => y)).mono (fun y Equal => Or.inr Equal)) _
    filter_upwards [Supported] with y InSupport
    rcases InSupport with Lower | Upper
    · rw [Lower, DownPotentialDifference x AtZero, abs_one]
    · rw [Upper]
      by_cases AtBoundary : x.val=N
      · rw [UpAtBoundary x AtBoundary, sub_self, abs_zero]
        exact zero_le_one
      · rw [UpPotentialDifference x AtBoundary]
        norm_num

end
end ECTheoryLib.Probability.FiniteBiasedWalk

namespace ECTheoryLib.Probability.FiniteBiasedWalk
open MeasureTheory ProbabilityTheory
open scoped unitInterval
noncomputable section

/-- Quadratic inside [0,m], zero outside it. It records exit through either end. -/
def ExitPotential (m : ℕ) {N : ℕ} (x : Fin (N+1)) : ℝ :=
  ((min x.val m : ℕ) : ℝ)*((m : ℝ)-((min x.val m : ℕ) : ℝ))

theorem ExitPotentialNonnegative (m : ℕ) {N : ℕ} (x : Fin (N+1)) :
    0≤ExitPotential m x := by
  unfold ExitPotential
  apply mul_nonneg (Nat.cast_nonneg _)
  exact sub_nonneg.mpr (Nat.cast_le.mpr (min_le_right _ _))

theorem ExitPotentialZeroIff (m : ℕ) (Positive : 0<m) {N : ℕ} (x : Fin (N+1)) :
    ExitPotential m x=0 ↔ x.val=0 ∨ m≤x.val := by
  rw [ExitPotential,mul_eq_zero]
  constructor
  · rintro (Left | Right)
    · have Zero : min x.val m=0 := Nat.cast_eq_zero.mp Left
      left
      omega
    · have Equal : m=min x.val m := Nat.cast_inj.mp (sub_eq_zero.mp Right)
      right
      omega
  · rintro (Zero | Above)
    · left
      simp [Zero]
    · right
      rw [min_eq_right Above,sub_self]

theorem ExitPotentialDownDifference (m : ℕ) {N : ℕ} (x : Fin (N+1))
    (Nonzero : x.val≠0) (Below : x.val<m) :
    ExitPotential m x-ExitPotential m (Down x)=(m : ℝ)-2*x.val+1 := by
  have AtLeastOne : 1≤x.val := Nat.one_le_iff_ne_zero.mpr Nonzero
  have DownBelow : x.val-1≤m := by omega
  simp only [ExitPotential,Down,min_eq_left Below.le,min_eq_left DownBelow,
    Nat.cast_sub AtLeastOne,Nat.cast_one]
  ring

theorem ExitPotentialUpDifference (m : ℕ) {N : ℕ} (Capacity : m≤N) (x : Fin (N+1))
    (Below : x.val<m) :
    ExitPotential m x-ExitPotential m (Up x)=2*x.val-(m : ℝ)+1 := by
  have UpBelow : x.val+1≤m := by omega
  have UpCapacity : x.val+1≤N := UpBelow.trans Capacity
  simp only [ExitPotential,Up,min_eq_left UpCapacity,min_eq_left Below.le,
    min_eq_left UpBelow,Nat.cast_add,Nat.cast_one]
  ring

/-- The quadratic exit potential gains unit drift from the random walk's variance. -/
theorem OneStepExitDrift (N m : ℕ) (Capacity : m≤N) (ε : I) (x : Fin (N+1))
    (Nonzero : x.val≠0) (Below : x.val<m) :
    (∫ y, ExitPotential m x-ExitPotential m y ∂(Step N ε x).toMeasure) =
      1+(ε : ℝ)*((m : ℝ)-2*x.val) := by
  have NotBoundary : x.val≠N := by omega
  rw [Step,if_neg Nonzero,Measure.toPMF_toMeasure,integral_bernoulliMeasure,
    if_neg NotBoundary,ExitPotentialDownDifference m x Nonzero Below,
    ExitPotentialUpDifference m Capacity x Below]
  simp only [InteriorDownProbability,smul_eq_mul]
  ring

theorem OneStepExitDriftLowerBound (N m : ℕ) (Capacity : m≤N) (ε : I) (x : Fin (N+1))
    (Nonzero : x.val≠0) (Below : x.val<m) :
    1-(ε : ℝ)*m≤∫ y, ExitPotential m x-ExitPotential m y ∂(Step N ε x).toMeasure := by
  rw [OneStepExitDrift N m Capacity ε x Nonzero Below]
  have Comparison : (x.val : ℝ)≤m := Nat.cast_le.mpr Below.le
  nlinarith [mul_nonneg ε.2.1 (sub_nonneg.mpr Comparison)]

end
end ECTheoryLib.Probability.FiniteBiasedWalk
