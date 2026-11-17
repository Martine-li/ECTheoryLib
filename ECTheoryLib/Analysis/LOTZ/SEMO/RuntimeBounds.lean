import ECTheoryLib.Analysis.LOTZ.OneBitProgress
import ECTheoryLib.Tools.Runtime.Phases
import ECTheoryLib.Tools.Runtime.Cost

/-!
# Full-front runtime of SEMO on LOTZ

The actual algorithm uses uniform archive-parent selection, one uniformly chosen
bit flip, and strict-dominance rejection with weak-dominance removal. For n>0,
all n+1 Pareto points coexist after expected at most n(n+1)(2n+1) iterations.
Initialization may be any PMF on valid nonempty archives; the standard uniform
singleton is included. Time zero is initialization and evaluations add one.

The same TwoPhaseCertificate already used for Jump combines front approach and
front coverage. The first level is n minus the largest prefix-plus-suffix score;
the second is the number of currently missing true front points. This gives an
explicit cubic bound, without treating historical discoveries as current coverage.
-/
namespace ECTheoryLib.Analysis.SEMOLOTZ
open MeasureTheory ECTheoryLib.Probability Tools.Runtime LOTZCoverage
noncomputable section

/-- Common useful-event floor: select a particular current member and flip a
particular coordinate, using the proved archive-size bound. -/
def Rate (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) * (1 / (n : ℝ))

/-- The useful-event rate is positive for nonempty bit strings. -/
theorem RatePositive {n : ℕ} (hn : 0 < n) : 0 < Rate n := by
  have Positive : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold Rate
  positivity

/-- Scaled remaining distance to the first true Pareto point. -/
def FirstPotential {n : ℕ} (P : ParetoPopulation (Bits n)) : ℝ := (FirstLevel P : ℝ) / Rate n

/-- Scaled missing-front count; zero exactly at current complete coverage. -/
def SecondPotential {n : ℕ} (P : ParetoPopulation (Bits n)) : ℝ := Missing P / Rate n

/-- Infinite-path expectation of the first time the current archive covers the
entire LOTZ front; nonarrival has value infinity and initial success has time zero. -/
def ExpectedRuntime {n : ℕ} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)) := SEMOInit n) : ENNReal :=
  ExpectedHittingTime (SEMOStep hn Dominates) Complete Initial

/-- Properties of every updated archive lift to almost-sure statements about
the actual SEMO kernel, for use by the generic path-level phase rule. -/
theorem StepAEUpdate {n : ℕ} (hn : 0 < n) (P : ParetoPopulation (Bits n))
    (Q : ParetoPopulation (Bits n) → Prop) (EveryCandidate : ∀ y, Q (Update P y)) :
    ∀ᵐ R ∂(SEMOStep hn Dominates P).toMeasure, Q R := by
  apply PMFAEOfSupport
  intro R Possible
  obtain ⟨_x, _InP, y, _PossibleMutation, rfl⟩ := (SEMOStepSupport hn Dominates P R).mp Possible
  exact EveryCandidate y

/-- Before any front point is present, the scaled best-score deficit has unit drift. -/
theorem FirstDrift {n : ℕ} (hn : 0 < n) (P : ParetoPopulation (Bits n))
    (IsValid : Valid P) (Outside : ¬ Region P) :
    1 ≤ ∫ Q, FirstPotential P - FirstPotential Q ∂(SEMOStep hn Dominates P).toMeasure := by
  obtain ⟨x, InP, i, Progress⟩ := UsefulFirstMutation P Outside
  have Nonnegative (y : Bits n) : 0 ≤ (FirstLevel P : ℝ) - FirstLevel (Update P y) := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr (FirstLevelUpdate P y))
  have RealProgress : 1 ≤ (FirstLevel P : ℝ) - FirstLevel (Update P (OnebitMutation x i)) := by
    have Cast : (FirstLevel (Update P (OnebitMutation x i)) : ℝ) + 1 ≤ FirstLevel P := by
      exact_mod_cast Progress
    linarith
  have Bound := ProgressFloor hn (fun Q => (FirstLevel Q : ℝ)) P IsValid Nonnegative x InP i RealProgress
  simp only [FirstPotential, ← sub_div]
  rw [integral_div]
  exact (le_div_iff₀ (RatePositive hn)).mpr (by simpa only [Rate, one_mul] using Bound)

/-- After the first front point, the scaled missing count has unit drift until
every front point is present simultaneously. -/
theorem SecondDrift {n : ℕ} (hn : 0 < n) (P : ParetoPopulation (Bits n))
    (IsValid : Valid P) (Inside : Region P) (Incomplete : ¬ Complete P) :
    1 ≤ ∫ Q, SecondPotential P - SecondPotential Q ∂(SEMOStep hn Dominates P).toMeasure := by
  obtain ⟨x, InP, i, Progress⟩ := UsefulCoverageMutation P Inside Incomplete
  have Bound := ProgressFloor hn Missing P IsValid
    (fun y => sub_nonneg.mpr (MissingUpdate P y)) x InP i Progress
  simp only [SecondPotential, ← sub_div]
  rw [integral_div]
  exact (le_div_iff₀ (RatePositive hn)).mpr (by simpa only [Rate, one_mul] using Bound)

/-- The LOTZ instantiation of the unchanged two-phase composition interface.
All retention and local progress premises are discharged from the actual algorithm. -/
def Certificate {n : ℕ} (hn : 0 < n) :
    TwoPhaseCertificate (SEMOStep hn Dominates) Complete Valid Region where
  First := FirstPotential
  Second := SecondPotential
  Budget := ((n : ℝ) + 1) / Rate n
  BudgetPositive := div_pos (by positivity) (RatePositive hn)
  FirstNonnegative := fun P => div_nonneg (Nat.cast_nonneg _) (RatePositive hn).le
  SecondNonnegative := fun P => div_nonneg (MissingNonnegative P) (RatePositive hn).le
  SecondZeroIffGoal := by
    intro P
    rw [SecondPotential, div_eq_zero_iff]
    simp only [(RatePositive hn).ne', or_false, MissingZeroIff]
  GoalInRegion := CompleteInRegion
  SecondBound := fun P _ => div_le_div_of_nonneg_right (MissingBound P) (RatePositive hn).le
  PreservesValid := fun P => StepAEUpdate hn P _
    (fun y IsValid => ParetoArchiveUpdateValid Dominates P.val y IsValid)
  PreservesRegion := fun P => StepAEUpdate hn P _
    (fun y _ Inside => Inside.mono (ObservedRetained P y))
  PreservesGoal := fun P => StepAEUpdate hn P _
    (fun y _ Covered => Covered.trans (ObservedRetained P y))
  FirstDrift := FirstDrift hn
  SecondDrift := SecondDrift hn

/-- Complete-front expected runtime is at most n(n+1)(2n+1) for any distribution
on valid nonempty archives. The result derives finiteness; it does not assume it. -/
theorem RuntimeBound {n : ℕ} (hn : 0 < n) (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedRuntime hn Initial ≤ ENNReal.ofReal ((n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) := by
  have Bound := (Certificate hn).RuntimeUniformBound Initial
    (PMFAEOfSupport Initial Valid InitiallyValid) ((n : ℝ) / Rate n)
    (fun P => div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le n (BestScore P))) (RatePositive hn).le)
  have Normalize : (n : ℝ) / Rate n + ((n : ℝ) + 1) / Rate n =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) := by
    unfold Rate
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul, inv_inv]
    ring
  change ExpectedRuntime hn Initial ≤ ENNReal.ofReal ((n : ℝ) / Rate n + ((n : ℝ) + 1) / Rate n) at Bound
  rw [Normalize] at Bound
  exact Bound

/-- Standard uniform singleton initialization needs no additional archive premise. -/
theorem UniformRuntimeBound {n : ℕ} (hn : 0 < n) :
    ExpectedRuntime hn ≤ ENNReal.ofReal ((n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) :=
  RuntimeBound hn (SEMOInit n) (fun P Possible => SEMOInitValid Dominates P Possible)

/-- Expected full-front coverage time is finite for standard initialization. -/
theorem RuntimeFinite {n : ℕ} (hn : 0 < n) : ExpectedRuntime hn < ⊤ :=
  lt_of_le_of_lt (UniformRuntimeBound hn) ENNReal.ofReal_lt_top

/-- With one evaluation for initialization and one per offspring, evaluation
count is exactly one plus the iteration count up to full front coverage. -/
theorem EvaluationCostEq {n : ℕ} (hn : 0 < n) :
    ExpectedEvaluationCost (SEMOStep hn Dominates) Complete (SEMOInit n) 1 1 =
      1 + ExpectedRuntime hn := by
  rw [ExpectedEvaluationCostEq]
  simp only [Nat.cast_one, one_mul]
  rfl

end
end ECTheoryLib.Analysis.SEMOLOTZ
