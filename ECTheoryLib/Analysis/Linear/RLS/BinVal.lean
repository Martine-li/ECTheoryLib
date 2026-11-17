import ECTheoryLib.Problems.Linear.BinVal
import ECTheoryLib.Analysis.Linear.RLS.FitnessDrift
import ECTheoryLib.Probability.Processes.PathDriftBounds
import ECTheoryLib.Tools.Drift.Multiplicative

/-!
# BinVal: two potentials on the same actual RLS trajectories

Source: Example 2.3.7, printed pages 105-106. The fitness and one-count
potentials share weak minimization selection, arbitrary initialization and
the all-zero target. Both variable and multiplicative drift bounds count
mutation iterations after initialization. Zero-safe initial potentials
retain any optimum atom; fixed positive starts have the displayed log forms.
The comparison concerns the precision of upper bounds, not a quadratic
actual runtime. Uniform-start asymptotics and rescaled drift are separate.
-/
namespace ECTheoryLib.Analysis.RLSBinVal
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open ECTheoryLib.Problems.Linear.BinVal
noncomputable section

abbrev Step {n : ℕ} (PositiveLength : 0 < n) := RLSLinear.Step PositiveLength (Weights (n := n))

abbrev ExpectedRuntime {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :=
  RLSLinear.ExpectedRuntime PositiveLength (Weights (n := n)) Initial

def FitnessBound {n : ℕ} (x : Bits n) : ℝ :=
  MultiplicativeDriftPotential 1 (1 / (n : ℝ)) (Score x)

def CountBound {n : ℕ} (x : Bits n) : ℝ :=
  MultiplicativeDriftPotential 1 (1 / (n : ℝ)) (OneMax x : ℝ)

theorem ScoreZeroIff {n : ℕ} (x : Bits n) : Score x = 0 ↔ x = fun _ => false :=
  RLSLinear.ScoreZeroIff Weights WeightPositive x

theorem CountZeroIffScoreZero {n : ℕ} (x : Bits n) : (OneMax x : ℝ) = 0 ↔ Score x = 0 := by
  rw [← Problems.Linear.ScoreUnitWeights x,
    RLSLinear.ScoreZeroIff (fun _ => 1) (fun _ => by norm_num), ScoreZeroIff]

theorem CountUnitGap {n : ℕ} (x : Bits n) : (OneMax x : ℝ) = 0 ∨ 1 ≤ (OneMax x : ℝ) := by
  by_cases Zero : OneMax x = 0
  · exact Or.inl (by simp [Zero])
  · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero)

theorem FitnessUnitGap {n : ℕ} (x : Bits n) : Score x = 0 ∨ 1 ≤ Score x := by
  rcases CountUnitGap x with Zero | Lower
  · exact Or.inl ((CountZeroIffScoreZero x).mp Zero)
  · exact Or.inr (Lower.trans (OneCountLeScore x))

theorem FitnessDrift {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    (∫ y, Score x - Score y ∂(Step PositiveLength x).toMeasure) = Score x / (n : ℝ) :=
  RLSLinear.FitnessDrift PositiveLength Weights WeightPositive x

theorem CountDrift {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    (∫ y, (OneMax x : ℝ) - (OneMax y : ℝ) ∂(Step PositiveLength x).toMeasure) =
      (OneMax x : ℝ) / (n : ℝ) :=
  RLSLinear.OneCountDrift PositiveLength Weights WeightPositive x

theorem CountConditionalDrift {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) :
    (PathMeasure (Step PositiveLength) Initial)[
      fun Path => (OneMax (Path t) : ℝ) - (OneMax (Path (t + 1)) : ℝ) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) t] =ᵐ[PathMeasure (Step PositiveLength) Initial]
      (fun Path => (OneMax (Path t) : ℝ) / (n : ℝ)) := by
  classical
  filter_upwards [PathMeasureFinitePotentialConditionalDrift (Step PositiveLength)
    Initial (fun x => (OneMax x : ℝ)) (Finset.univ.image (fun x : Bits n => (OneMax x : ℝ)))
    (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) t] with Path Equal
  rw [Equal, CountDrift PositiveLength]

theorem StepPreservesFitnessZero {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, Score x = 0 → Score y = 0 :=
  RLSLinear.StepPreservesScoreZero PositiveLength Weights WeightPositive x

theorem StepPreservesCountZero {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure,
      (OneMax x : ℝ) = 0 → (OneMax y : ℝ) = 0 := by
  filter_upwards [StepPreservesFitnessZero PositiveLength x] with y Preserved
  exact fun Zero => (CountZeroIffScoreZero y).mpr (Preserved ((CountZeroIffScoreZero x).mp Zero))

/-- Only a private proof-sharing lemma: no new stochastic framework. Both calls
below use existing drift interfaces with premises from the actual selected kernel. -/
private theorem RuntimeBounds {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n))
    (V : Bits n → ℝ) (Gap : ∀ x, V x = 0 ∨ 1 ≤ V x)
    (Goal : ∀ x, V x = 0 ↔ Score x = 0)
    (Local : ∀ x, (∫ y, V x - V y ∂(Step PositiveLength x).toMeasure) = V x / (n : ℝ))
    (Preserves : ∀ x, ∀ᵐ y ∂(Step PositiveLength x).toMeasure, V x = 0 → V y = 0) :
    (ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal
      (∫ x, VariableDriftPotential 1 (fun s => (1 / (n : ℝ)) * s) (V x) ∂Initial.toMeasure)) ∧
    (ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal
      (∫ x, MultiplicativeDriftPotential 1 (1 / (n : ℝ)) (V x) ∂Initial.toMeasure)) := by
  classical
  let μ := PathMeasure (Step PositiveLength) Initial
  let X : ℕ → (ℕ → Bits n) → ℝ := fun t Path => V (Path t)
  let S : Finset ℝ := insert 0 (Finset.univ.image V)
  have DeltaPositive : 0 < 1 / (n : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr PositiveLength)
  have Lower : ∀ s ∈ S, s = 0 ∨ 1 ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | Image
    · exact Or.inl Zero
    · rcases Finset.mem_image.mp Image with ⟨x, _, rfl⟩
      exact Gap x
  have Values : ∀ t Path, X t Path ∈ S := by
    intro t Path
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩)
  have AdaptedX : Adapted (Filtration.piLE (X := fun _ : ℕ => Bits n)) X :=
    CountablePathPotentialAdapted V
  have Absorbing : ZeroIsAbsorbing μ X :=
    PathMeasureZeroIsAbsorbing (Step PositiveLength) Initial V (fun _ => True)
      (fun _ => ae_of_all _ (fun _ => trivial))
      (fun x => (Preserves x).mono (fun _ Holds _ => Holds))
  have Drift : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      (1 / (n : ℝ)) * s ≤ StateDrift μ X t s := by
    intro t s _ _ EventPositive
    have Equal := PathMeasureStateDrift (Step PositiveLength) Initial V
      (fun s => s / (n : ℝ)) Local t s EventPositive
    change _ ≤ StateDrift μ X t s
    rw [Equal]
    exact le_of_eq (by ring)
  have Variable := VariableDriftUpperBound μ X S 1 (fun s => (1 / (n : ℝ)) * s)
    (fun _ => AdaptedX.measurable) (Finset.mem_insert_self _ _) (by norm_num) Lower Values
    Absorbing (fun s H => mul_pos DeltaPositive (lt_of_lt_of_le (by norm_num) H))
    (fun _ _ _ _ H => mul_le_mul_of_nonneg_left H DeltaPositive.le) Drift
  have Multiplicative := MultiplicativeDriftUpperBound μ X S 1 (1 / (n : ℝ))
    (fun _ => AdaptedX.measurable) (Finset.mem_insert_self _ _) (by norm_num) Lower Values
    Absorbing DeltaPositive Drift
  have Hitting := ExpectedHittingTimeEqExpectedZero (Step PositiveLength) Initial V
    (fun x => Score x = 0) Goal
  change ExpectedRuntime PositiveLength Initial = ExpectedZeroHittingTime μ X at Hitting
  have VariableInitial := PathMeasureInitialIntegral (Step PositiveLength) Initial
    (fun x => VariableDriftPotential 1 (fun s => (1 / (n : ℝ)) * s) (V x))
  change ExpectedValue μ (fun Path => VariableDriftPotential 1
    (fun s => (1 / (n : ℝ)) * s) (X 0 Path)) = _ at VariableInitial
  have MultiplicativeInitial := PathMeasureInitialIntegral (Step PositiveLength) Initial
    (fun x => MultiplicativeDriftPotential 1 (1 / (n : ℝ)) (V x))
  change ExpectedValue μ (fun Path => MultiplicativeDriftPotential 1
    (1 / (n : ℝ)) (X 0 Path)) = _ at MultiplicativeInitial
  rw [VariableInitial] at Variable
  rw [MultiplicativeInitial] at Multiplicative
  rw [Hitting]
  exact ⟨Variable, Multiplicative⟩

theorem FitnessVariableUpperBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal
      (∫ x, VariableDriftPotential 1 (fun s => (1 / (n : ℝ)) * s) (Score x) ∂Initial.toMeasure) :=
  (RuntimeBounds PositiveLength Initial Score FitnessUnitGap (fun _ => Iff.rfl)
    (FitnessDrift PositiveLength) (StepPreservesFitnessZero PositiveLength)).1

theorem FitnessMultiplicativeUpperBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal (∫ x, FitnessBound x ∂Initial.toMeasure) :=
  (RuntimeBounds PositiveLength Initial Score FitnessUnitGap (fun _ => Iff.rfl)
    (FitnessDrift PositiveLength) (StepPreservesFitnessZero PositiveLength)).2

theorem CountVariableUpperBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal
      (∫ x, VariableDriftPotential 1 (fun s => (1 / (n : ℝ)) * s)
        (OneMax x : ℝ) ∂Initial.toMeasure) :=
  (RuntimeBounds PositiveLength Initial (fun x => (OneMax x : ℝ)) CountUnitGap CountZeroIffScoreZero
    (CountDrift PositiveLength) (StepPreservesCountZero PositiveLength)).1

theorem CountMultiplicativeUpperBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal (∫ x, CountBound x ∂Initial.toMeasure) :=
  (RuntimeBounds PositiveLength Initial (fun x => (OneMax x : ℝ)) CountUnitGap CountZeroIffScoreZero
    (CountDrift PositiveLength) (StepPreservesCountZero PositiveLength)).2

theorem VariableFitnessPotentialEqBound {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    VariableDriftPotential 1 (fun s => (1 / (n : ℝ)) * s) (Score x) = FitnessBound x :=
  LinearVariableDriftPotential 1 (1 / (n : ℝ)) (Score x) (by norm_num)
    (one_div_pos.mpr (Nat.cast_pos.mpr PositiveLength)) (FitnessUnitGap x)

theorem VariableCountPotentialEqBound {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    VariableDriftPotential 1 (fun s => (1 / (n : ℝ)) * s) (OneMax x : ℝ) = CountBound x :=
  LinearVariableDriftPotential 1 (1 / (n : ℝ)) (OneMax x : ℝ) (by norm_num)
    (one_div_pos.mpr (Nat.cast_pos.mpr PositiveLength)) (CountUnitGap x)

theorem FitnessBoundOfNonzero {n : ℕ} (x : Bits n) (Nonzero : Score x ≠ 0) :
    FitnessBound x = (n : ℝ) * (1 + Real.log (Score x)) := by
  simp [FitnessBound, MultiplicativeDriftPotential, Nonzero, div_eq_mul_inv, mul_comm]

theorem CountBoundOfNonzero {n : ℕ} (x : Bits n) (Nonzero : (OneMax x : ℝ) ≠ 0) :
    CountBound x = (n : ℝ) * (1 + Real.log (OneMax x : ℝ)) := by
  simp [CountBound, MultiplicativeDriftPotential, Nonzero, div_eq_mul_inv, mul_comm]

theorem FixedFitnessUpperBound {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Nonzero : Score x ≠ 0) : ExpectedRuntime PositiveLength (PMF.pure x) ≤
      ENNReal.ofReal ((n : ℝ) * (1 + Real.log (Score x))) := by
  have Bound := FitnessMultiplicativeUpperBound PositiveLength (PMF.pure x)
  simpa only [PMF.toMeasure_pure, integral_dirac, FitnessBoundOfNonzero x Nonzero] using Bound

theorem FixedCountUpperBound {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Nonzero : (OneMax x : ℝ) ≠ 0) : ExpectedRuntime PositiveLength (PMF.pure x) ≤
      ENNReal.ofReal ((n : ℝ) * (1 + Real.log (OneMax x : ℝ))) := by
  have Bound := CountMultiplicativeUpperBound PositiveLength (PMF.pure x)
  simpa only [PMF.toMeasure_pure, integral_dirac, CountBoundOfNonzero x Nonzero] using Bound

theorem InitialSuccessBounds {n : ℕ} :
    FitnessBound (fun _ : Fin n => false) = 0 ∧ CountBound (fun _ : Fin n => false) = 0 := by
  simp [FitnessBound, CountBound, MultiplicativeDriftPotential, Score, Problems.Linear.Score, OneMax]

theorem InitialSuccessRuntime {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (PMF.pure (fun _ => false)) = 0 :=
  RLSLinear.InitialSuccessRuntime PositiveLength Weights WeightPositive

/-- Compare zero-safe potentials before integrating any initial distribution. -/
theorem CountBoundLeFitnessBound {n : ℕ} (x : Bits n) : CountBound x ≤ FitnessBound x := by
  by_cases Zero : (OneMax x : ℝ) = 0
  · have FitnessZero := (CountZeroIffScoreZero x).mp Zero
    simp [CountBound, FitnessBound, MultiplicativeDriftPotential, Zero, FitnessZero]
  · have CountPositive : 0 < (OneMax x : ℝ) :=
      lt_of_lt_of_le (by norm_num) ((CountUnitGap x).resolve_left Zero)
    have FitnessNonzero : Score x ≠ 0 := fun H => Zero ((CountZeroIffScoreZero x).mpr H)
    rw [CountBoundOfNonzero x Zero, FitnessBoundOfNonzero x FitnessNonzero]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    linarith [Real.log_le_log CountPositive (OneCountLeScore x)]

theorem InitialBoundsIntegrable {n : ℕ} (Initial : PMF (Bits n)) :
    Integrable (CountBound (n := n)) Initial.toMeasure ∧
      Integrable (FitnessBound (n := n)) Initial.toMeasure :=
  ⟨Integrable.of_finite, Integrable.of_finite⟩

theorem InitialCountBoundLeFitnessBound {n : ℕ} (Initial : PMF (Bits n)) :
    (∫ x, CountBound x ∂Initial.toMeasure) ≤ ∫ x, FitnessBound x ∂Initial.toMeasure := by
  exact integral_mono (InitialBoundsIntegrable Initial).1 (InitialBoundsIntegrable Initial).2
    CountBoundLeFitnessBound

theorem LastBitBoundsEqual (n : ℕ) :
    CountBound (fun j : Fin (n + 1) => decide (j = Fin.last n)) = (n + 1 : ℝ) ∧
    FitnessBound (fun j : Fin (n + 1) => decide (j = Fin.last n)) = (n + 1 : ℝ) := by
  simp [CountBound, FitnessBound, MultiplicativeDriftPotential, OneCountSingleOne,
    ScoreSingleOne, LastWeight]

theorem HighestBitBoundStrict (n : ℕ) :
    CountBound (fun j : Fin (n + 2) => decide (j = 0)) <
      FitnessBound (fun j : Fin (n + 2) => decide (j = 0)) := by
  let x : Bits (n + 2) := fun j => decide (j = 0)
  have Count : (OneMax x : ℝ) = 1 := by rw [OneCountSingleOne]; norm_num
  have Fitness : Score x = (2 : ℝ) ^ (n + 1) := ScoreSingleOne (0 : Fin (n + 2)) |>.trans (FirstWeight (n + 1))
  have Large : 1 < (2 : ℝ) ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have CountNonzero : (OneMax x : ℝ) ≠ 0 := by rw [Count]; norm_num
  have FitnessNonzero : Score x ≠ 0 := by rw [Fitness]; exact ne_of_gt (zero_lt_one.trans Large)
  change CountBound x < FitnessBound x
  rw [CountBoundOfNonzero x CountNonzero, FitnessBoundOfNonzero x FitnessNonzero, Count, Fitness]
  apply mul_lt_mul_of_pos_left _ (by exact_mod_cast (show 0 < n + 2 by omega))
  simpa using add_lt_add_left (Real.log_pos Large) 1

end
end ECTheoryLib.Analysis.RLSBinVal




/-!
Actual rescaled drift in Example2.3.7 (prose after2.39, printed106).
These results concern full single-one states on the existing BinVal kernel.
The logarithmic and count potentials are the accepted zero-safe bounds;
no known runtime is a drift premise and no scalar event is identified with
a full state. Uniform initialization and random last-position claims are separate.
-/
namespace ECTheoryLib.Analysis.RLSBinVal
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open ECTheoryLib.Problems.Linear.BinVal
noncomputable section

/-- The actual selected update removes the unique one iff it selects that coordinate. -/
theorem UpdateSingleOne {n : ℕ} (i k : Fin n) :
    RLSUpdate (Problems.MinNotWorse Score) (fun j => decide (j = i)) k =
      if k = i then (fun _ => false) else (fun j => decide (j = i)) := by
  by_cases Equal : k = i
  · subst k
    rw [if_pos rfl]
    change RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score Weights))
      (fun j => decide (j = i)) i = _
    rw [RLSLinear.UpdateAtOne Weights WeightPositive _ i (by simp)]
    funext j
    by_cases Same : j = i
    · subst j
      rw [OnebitMutationAt]
      simp
    · rw [OnebitMutationAway _ i j Same]
      simp [Same]
  · rw [if_neg Equal]
    exact RLSLinear.UpdateAtZero Weights WeightPositive _ k (by simp [Equal])

private theorem SingleOnePotentialDrift {n : ℕ} (PositiveLength : 0 < n) (i : Fin n)
    (V : Bits n → ℝ) (ZeroValue : V (fun _ => false) = 0) :
    (∫ y, V (fun j => decide (j = i)) - V y
      ∂(Step PositiveLength (fun j => decide (j = i))).toMeasure) =
      V (fun j => decide (j = i)) / (n : ℝ) := by
  let x : Bits n := fun j => decide (j = i)
  have Difference (k : Fin n) :
      V x - V (RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score Weights)) x k) =
        if k = i then V x else 0 := by
    have Update : RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score Weights)) x k =
        if k = i then (fun _ => false) else x := UpdateSingleOne i k
    rw [Update]
    by_cases Equal : k = i
    · simp only [if_pos Equal, ZeroValue, sub_zero]
    · simp only [if_neg Equal, sub_self]
  change (∫ y, V x - V y ∂(RLSLinear.Step PositiveLength Weights x).toMeasure) = V x / (n : ℝ)
  rw [RLSLinear.Step, RLSStepEqUniformUpdate]
  rw [← PMF.toMeasure_map (RLSUpdate (Problems.MinNotWorse (Problems.Linear.Score Weights)) x)
    (UniformBitIndex n PositiveLength) (measurable_of_finite _)]
  rw [integral_map_of_stronglyMeasurable (measurable_of_finite _)
    (measurable_of_finite (fun y : Bits n => V x - V y)).stronglyMeasurable,
    PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  simp_rw [Difference]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring
  · intro k _ Different
    rw [if_neg Different, mul_zero]
  · intro Absent
    exact False.elim (Absent (Finset.mem_univ i))

theorem SingleOneRescaledFitnessDrift {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) :
    (∫ y, FitnessBound (fun j => decide (j = i)) - FitnessBound y
      ∂(Step PositiveLength (fun j => decide (j = i))).toMeasure) =
      1 + (n - 1 - i.val : ℕ) * Real.log 2 := by
  rw [SingleOnePotentialDrift PositiveLength i FitnessBound InitialSuccessBounds.1]
  have Nonzero : Score (fun j => decide (j = i)) ≠ 0 := by
    rw [ScoreSingleOne]
    exact ne_of_gt (WeightPositive i)
  rw [FitnessBoundOfNonzero _ Nonzero, ScoreSingleOne, Weights, Real.log_pow]
  exact mul_div_cancel_left₀ _ (ne_of_gt (Nat.cast_pos.mpr PositiveLength))

theorem SingleOneRescaledCountDrift {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) :
    (∫ y, CountBound (fun j => decide (j = i)) - CountBound y
      ∂(Step PositiveLength (fun j => decide (j = i))).toMeasure) = 1 := by
  rw [SingleOnePotentialDrift PositiveLength i CountBound InitialSuccessBounds.2]
  have Nonzero : (OneMax (fun j => decide (j = i)) : ℝ) ≠ 0 := by
    rw [OneCountSingleOne]
    norm_num
  rw [CountBoundOfNonzero _ Nonzero, OneCountSingleOne]
  simp only [Nat.cast_one, Real.log_one, add_zero, mul_one]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr PositiveLength))

private theorem ConditionalDriftAtSingleOne {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (V : Bits n → ℝ) (i : Fin n) (d : ℝ)
    (Local : (∫ y, V (fun j => decide (j = i)) - V y
      ∂(Step PositiveLength (fun j => decide (j = i))).toMeasure) = d) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength) Initial,
      Path t = (fun j => decide (j = i)) →
      ((PathMeasure (Step PositiveLength) Initial)[fun Path => V (Path t) - V (Path (t + 1)) |
        Filtration.piLE (X := fun _ : ℕ => Bits n) t]) Path = d := by
  classical
  filter_upwards [PathMeasureFinitePotentialConditionalDrift (Step PositiveLength) Initial V
    (Finset.univ.image V) (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) t]
    with Path Equal
  intro CurrentState
  rw [Equal, CurrentState, Local]

/-- The CE uses full natural history and the antecedent is an actual state identity. -/
theorem SingleOneRescaledFitnessConditionalDrift {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) (i : Fin n) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength) Initial,
      Path t = (fun j => decide (j = i)) →
      ((PathMeasure (Step PositiveLength) Initial)[
        fun Path => FitnessBound (Path t) - FitnessBound (Path (t + 1)) |
        Filtration.piLE (X := fun _ : ℕ => Bits n) t]) Path =
          1 + (n - 1 - i.val : ℕ) * Real.log 2 :=
  ConditionalDriftAtSingleOne PositiveLength Initial FitnessBound i _
    (SingleOneRescaledFitnessDrift PositiveLength i) t

theorem SingleOneRescaledCountConditionalDrift {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) (i : Fin n) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength) Initial,
      Path t = (fun j => decide (j = i)) →
      ((PathMeasure (Step PositiveLength) Initial)[
        fun Path => CountBound (Path t) - CountBound (Path (t + 1)) |
        Filtration.piLE (X := fun _ : ℕ => Bits n) t]) Path = 1 :=
  ConditionalDriftAtSingleOne PositiveLength Initial CountBound i _
    (SingleOneRescaledCountDrift PositiveLength i) t

theorem LastBitRescaledDrifts (n : ℕ) :
    (∫ y, FitnessBound (fun j : Fin (n + 1) => decide (j = Fin.last n)) - FitnessBound y
      ∂(Step (Nat.succ_pos n) (fun j => decide (j = Fin.last n))).toMeasure) = 1 ∧
    (∫ y, CountBound (fun j : Fin (n + 1) => decide (j = Fin.last n)) - CountBound y
      ∂(Step (Nat.succ_pos n) (fun j => decide (j = Fin.last n))).toMeasure) = 1 := by
  constructor
  · rw [SingleOneRescaledFitnessDrift (Nat.succ_pos n) (Fin.last n)]
    simp
  · exact SingleOneRescaledCountDrift (Nat.succ_pos n) (Fin.last n)

theorem HighestBitRescaledDriftStrict (n : ℕ) :
    (∫ y, CountBound (fun j : Fin (n + 2) => decide (j = 0)) - CountBound y
      ∂(Step (by omega : 0 < n + 2) (fun j => decide (j = 0))).toMeasure) <
    (∫ y, FitnessBound (fun j : Fin (n + 2) => decide (j = 0)) - FitnessBound y
      ∂(Step (by omega : 0 < n + 2) (fun j => decide (j = 0))).toMeasure) := by
  rw [SingleOneRescaledCountDrift, SingleOneRescaledFitnessDrift]
  have ExponentPositive : 0 < (n + 2) - 1 - (0 : Fin (n + 2)).val := by simp
  have TermPositive := mul_pos (Nat.cast_pos.mpr ExponentPositive :
    (0 : ℝ) < ((n + 2) - 1 - (0 : Fin (n + 2)).val : ℕ))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  linarith

end
end ECTheoryLib.Analysis.RLSBinVal

