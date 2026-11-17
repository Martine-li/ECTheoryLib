import ECTheoryLib.Analysis.OneMinMax.NSGAII.CoverageState
import ECTheoryLib.Analysis.OneMinMax.Archive.Drift
import ECTheoryLib.Algorithms.PopulationSampling
import ECTheoryLib.Tools.Coverage.Batch

/-!
# Local generation drift for NSGA-II on OneMinMax

The archive analysis supplies a useful parent with mutation progress at least
Delta. Uniform occurrence sampling and an independent population-sized batch
retain at least half this expected progress. The actual crowding selection then
retains both old and newly produced values under the proved capacity condition.
Thus the harmonic deficit has generation drift at least Delta/2. The proof uses
the original list kernel and does not replace environmental selection by an archive.
-/
namespace ECTheoryLib.Analysis.NSGAIIOneMinMax
open MeasureTheory Probability Operators.Selection Operators.Sampling Tools.Coverage
noncomputable section

/-- Newly represented target weight in an offspring batch, counting each value once. -/
def BatchGain {n : ℕ} (Pool Offspring : List (Bits n)) : ℝ :=
  CoverageGain (Finset.range (n + 1)) (Observed Pool) (LineWeight n)
    (fun j => ∃ x ∈ Offspring, OneMax x = j)

theorem BatchGainNonnegative {n : ℕ} (Pool Offspring : List (Bits n)) : 0 ≤ BatchGain Pool Offspring :=
  CoverageGainNonnegative _ _ _ _ (fun j _ => (LineWeightPositive n j).le)

theorem BatchGainBound {n : ℕ} (Pool Offspring : List (Bits n)) :
    BatchGain Pool Offspring ≤ 2 * (harmonic (n + 1) : ℝ) :=
  (CoverageGainBound _ _ _ _ (fun j _ => (LineWeightPositive n j).le)).trans_eq (LineWeightTotal n)

/-- The single-sample gain is exactly the deterministic potential drop used in
the earlier archive proof. This bridge reuses its one-bit geometry unchanged. -/
theorem SingleGainEqArchive {n : ℕ} (Pool : List (Bits n)) (Nonempty : Pool ≠ []) (y : Bits n) :
    CoverageGain (Finset.range (n + 1)) (Observed Pool) (LineWeight n) (fun j => OneMax y = j) =
      OneMinMaxCoverage.Potential (AsArchive Pool Nonempty) -
        OneMinMaxCoverage.Potential (OneMinMaxCoverage.Update (AsArchive Pool Nonempty) y) := by
  rw [CoverageGainSingle]
  unfold OneMinMaxCoverage.Potential
  rw [OneMinMaxCoverage.ObservedUpdate, AsArchiveObserved]

/-- A full batch has expected new-value gain at least Delta/2. The only
mutation-specific input is the same exact-one-bit probability floor used by SEMO
and GSEMO; all other mutation outcomes may add further coverage. -/
theorem BatchGainLower {n : ℕ} (Mutation : Bits n → PMF (Bits n)) (Delta : ℝ)
    (NonnegativeDelta : 0 ≤ Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Pool : List (Bits n)) (Nonempty : Pool ≠ []) (Incomplete : ¬ Complete Pool) :
    Delta / 2 ≤ ∫ L, BatchGain Pool L
      ∂(IndependentSamples (PopulationOffspring Mutation Pool) Pool.length).toMeasure := by
  obtain ⟨x, Present, Progress⟩ := OneMinMaxCoverage.UsefulParent Mutation Delta NonnegativeDelta
    MutationFloor (AsArchive Pool Nonempty) Incomplete
  have InPool : x ∈ Pool := List.mem_toFinset.mp Present
  have BatchBound := CoverageBatchHalfReference (PopulationOffspring Mutation Pool) (Mutation x)
    Pool.length OneMax (Finset.range (n + 1)) (Observed Pool) (LineWeight n)
    (fun j _ => (LineWeightPositive n j).le)
    (fun j _ => PopulationOffspringEventRate Mutation Pool x InPool (fun y => OneMax y = j))
  have SingleEquality :
      (fun y => CoverageGain (Finset.range (n + 1)) (Observed Pool) (LineWeight n) (fun j => OneMax y = j)) =
      (fun y => OneMinMaxCoverage.Potential (AsArchive Pool Nonempty) -
        OneMinMaxCoverage.Potential (OneMinMaxCoverage.Update (AsArchive Pool Nonempty) y)) :=
    funext (SingleGainEqArchive Pool Nonempty)
  rw [SingleEquality] at BatchBound
  exact (div_le_div_of_nonneg_right Progress (by norm_num : (0 : ℝ) ≤ 2)).trans BatchBound

/-- Actual environmental selection converts every new offspring value into
potential decrease, because the capacity theorem retains the entire input value set. -/
theorem EnvironmentGainLower {n : ℕ} (Pool Offspring Result : List (Bits n))
    (Room : 4 * (n + 1) ≤ Pool.length)
    (Possible : Result ∈ (NSGAIIEnvironment Fitness Pool.length (Pool ++ Offspring)).support) :
    BatchGain Pool Offspring ≤ Potential Pool - Potential Result := by
  have Retained := EnvironmentObserved (Pool ++ Offspring) Result Pool.length Room Possible
  apply CoverageGainLeDecrease _ _ _ _ _ (fun j _ => (LineWeightPositive n j).le)
  · intro j Present
    obtain ⟨x, InPool, Same⟩ := (ObservedIff Pool j).mp Present
    exact Retained ((ObservedIff (Pool ++ Offspring) j).mpr ⟨x, List.mem_append_left _ InPool, Same⟩)
  · intro j _ Discovered
    obtain ⟨x, InBatch, Same⟩ := Discovered
    exact Retained ((ObservedIff (Pool ++ Offspring) j).mpr ⟨x, List.mem_append_right _ InBatch, Same⟩)

theorem PotentialNormBound {n : ℕ} (Pool : List (Bits n)) :
    ‖Potential Pool‖ ≤ 2 * (harmonic (n + 1) : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (PotentialNonnegative Pool)]
  exact PotentialBound Pool

theorem DecreaseNormBound {n : ℕ} (Pool Result : List (Bits n)) :
    ‖Potential Pool - Potential Result‖ ≤ 4 * (harmonic (n + 1) : ℝ) :=
  (norm_sub_le _ _).trans (by linarith [PotentialNormBound Pool, PotentialNormBound Result])

/-- Every incomplete population of capacity at least `4(n+1)` has expected
generation decrease at least Delta/2 under the original NSGA-II kernel. -/
theorem OneStepDriftLowerBound {n : ℕ} (Mutation : Bits n → PMF (Bits n)) (Delta : ℝ)
    (NonnegativeDelta : 0 ≤ Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Pool : List (Bits n)) (Room : 4 * (n + 1) ≤ Pool.length) (Incomplete : ¬ Complete Pool) :
    Delta / 2 ≤ ∫ Result, Potential Pool - Potential Result ∂(NSGAIIStep Mutation Fitness Pool).toMeasure := by
  have Nonempty : Pool ≠ [] := by intro Empty; simp only [Empty, List.length_nil] at Room; omega
  have NotEmpty : Pool.isEmpty = false := by
    cases Pool with
    | nil => exact False.elim (Nonempty rfl)
    | cons x Tail => rfl
  rw [NSGAIIStep, NotEmpty]
  simp only [Bool.false_eq_true, if_false]
  rw [PMFIntegralBindOfBounded _ _ _ (4 * (harmonic (n + 1) : ℝ)) (DecreaseNormBound Pool)]
  apply (BatchGainLower Mutation Delta NonnegativeDelta MutationFloor Pool Nonempty Incomplete).trans
  have BatchIntegrable : Integrable (BatchGain Pool)
      (IndependentSamples (PopulationOffspring Mutation Pool) Pool.length).toMeasure := by
    apply PMFIntegrableOfBounded _ _ (2 * (harmonic (n + 1) : ℝ))
    intro L
    rw [Real.norm_eq_abs, abs_of_nonneg (BatchGainNonnegative Pool L)]
    exact BatchGainBound Pool L
  have AverageBound (L : List (Bits n)) :
      ‖∫ Result, Potential Pool - Potential Result
        ∂(NSGAIIEnvironment Fitness Pool.length (Pool ++ L)).toMeasure‖ ≤ 4 * (harmonic (n + 1) : ℝ) := by
    have Bound := norm_integral_le_of_norm_le_const
      (μ := (NSGAIIEnvironment Fitness Pool.length (Pool ++ L)).toMeasure)
      (ae_of_all _ (DecreaseNormBound Pool))
    simpa only [probReal_univ, mul_one] using Bound
  apply integral_mono_ae BatchIntegrable (PMFIntegrableOfBounded _ _ _ AverageBound)
  apply ae_of_all
  intro L
  have AlmostSure := PMFAEOfSupport (NSGAIIEnvironment Fitness Pool.length (Pool ++ L))
    (fun Result => BatchGain Pool L ≤ Potential Pool - Potential Result)
    (fun Result Possible => EnvironmentGainLower Pool L Result Room Possible)
  have Average := integral_mono_ae (integrable_const (BatchGain Pool L))
    (PMFIntegrableOfBounded _ _ _ (DecreaseNormBound Pool)) AlmostSure
  simpa only [integral_const, probReal_univ, one_smul] using Average

end
end ECTheoryLib.Analysis.NSGAIIOneMinMax
