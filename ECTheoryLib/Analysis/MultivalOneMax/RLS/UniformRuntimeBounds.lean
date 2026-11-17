import ECTheoryLib.Analysis.MultivalOneMax.RLS.ExactRuntime
import ECTheoryLib.Analysis.MultivalOneMax.RLS.UniformInitialLaw
import ECTheoryLib.Probability.Processes.InitialMixture
import ECTheoryLib.Probability.Distributions.BinomialHarmonicExpectation

/-!
# Uniform-initialization runtime with an explicit constant error

Doerr, Doerr, and Koetzing (2018), Algorithmica 80:1732–1768, Theorem 6,
Section 4.1, pp. 1745–1746.
https://hpi.de/friedrich/docs/publications/2018/Algorithmica_d.pdf

The interval-distance objective and actual kernel are unchanged. Extended
trajectory total expectation mixes the fixed-state theorem, after which
finiteness permits conversion to reals. A reciprocal-moment argument gives
`H_n-1 ≤ E[H_K] ≤ H_n` and hence constants `C=1, N=1`, uniform in alphabet
size and target. This proof uses finite sums instead of a Chernoff bound.
-/

namespace ECTheoryLib.Analysis.RLSMultival

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Problems.MultivalOneMax
open ECTheoryLib.Probability ProbabilityTheory

noncomputable section

/-- Extended expected mutation iterations under uniform initialization and
the actual RLS path law; initialization is time zero. -/
def ExpectedUniformRuntime {n r : Nat} (PositiveLength : 0 < n) (AlphabetSize : 2 ≤ r)
    (Target : MultiValues n r) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength AlphabetSize Target) (fun x => x = Target)
    (MultivalRLSInit n r (by omega))

/-- Total expectation mixes the fixed-state formula without conditioning
away initially optimal states. -/
theorem UniformRuntimeMixture {n r : Nat} (PositiveLength : 0 < n) (AlphabetSize : 2 ≤ r)
    (Target : MultiValues n r) :
    ExpectedUniformRuntime PositiveLength AlphabetSize Target =
      ∫⁻ x, ExpectedRuntime PositiveLength AlphabetSize Target x
        ∂(MultivalRLSInit n r (by omega)).toMeasure := by
  exact ExpectedHittingTimeInitialMixture _ _ _

/-- Exact mixture formula `n(r-1)E[H_K]` in extended nonnegative reals. -/
theorem UniformRuntimeHarmonic {n r : Nat} (PositiveLength : 0 < n) (AlphabetSize : 2 ≤ r)
    (Target : MultiValues n r) :
    ExpectedUniformRuntime PositiveLength AlphabetSize Target =
      ENNReal.ofReal ((n : ℝ) * ((r-1 : Nat) : ℝ) *
        (∫ x, (harmonic (Hamming Target x) : ℝ)
          ∂(MultivalRLSInit n r (by omega)).toMeasure)) := by
  rw [UniformRuntimeMixture]
  simp_rw [FixedRuntimeExact PositiveLength AlphabetSize Target]
  have Nonnegative : ∀ x : MultiValues n r,
      0 ≤ (n : ℝ) * ((r-1 : Nat) : ℝ) * (harmonic (Hamming Target x) : ℝ) := by
    intro x
    exact mul_nonneg (by positivity) (Tools.Runtime.HarmonicNonnegative _)
  rw [← ofReal_integral_eq_lintegral_ofReal Integrable.of_finite (ae_of_all _ Nonnegative),
    integral_const_mul]

theorem UniformRuntimeFinite {n r : Nat} (PositiveLength : 0 < n) (AlphabetSize : 2 ≤ r)
    (Target : MultiValues n r) :
    ExpectedUniformRuntime PositiveLength AlphabetSize Target ≠ ⊤ := by
  rw [UniformRuntimeHarmonic]
  exact ENNReal.ofReal_ne_top

/-- Replace the actual initial-distance pushforward by its proved binomial law. -/
theorem UniformHarmonicMean {n r : Nat} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) :
    (∫ x, (harmonic (Hamming Target x) : ℝ)
      ∂(MultivalRLSInit n r PositiveAlphabet).toMeasure) =
      ∫ k, (harmonic k : ℝ) ∂binomial n (MismatchProbability r PositiveAlphabet) := by
  rw [← UniformHammingBinomial PositiveAlphabet Target,
    integral_map (measurable_of_finite _).aemeasurable (measurable_of_countable _).aestronglyMeasurable]

theorem UniformRuntimeExactReal {n r : Nat} (PositiveLength : 0 < n) (AlphabetSize : 2 ≤ r)
    (Target : MultiValues n r) :
    (ExpectedUniformRuntime PositiveLength AlphabetSize Target).toReal =
      (n : ℝ) * ((r-1 : Nat) : ℝ) *
        (∫ k, (harmonic k : ℝ) ∂binomial n (MismatchProbability r (by omega))) := by
  rw [UniformRuntimeHarmonic, UniformHarmonicMean, ENNReal.toReal_ofReal]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  exact Tools.Runtime.HarmonicNonnegative

/-- Uniform initialization hits a prescribed target with probability `r^(-n)`;
this mass remains included in the binomial mixture. -/
theorem UniformHammingZeroProbability {n r : Nat} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.real {x | Hamming Target x = 0} =
      (1 / (r : ℝ)) ^ n := by
  have Law := UniformHammingBinomial PositiveAlphabet Target
  have ZeroMass := congrArg (fun μ : Measure Nat => μ.real {0}) Law
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _),
    binomial_real_zero] at ZeroMass
  change (MultivalRLSInit n r PositiveAlphabet).toMeasure.real {x | Hamming Target x = 0} =
    (1 - (MismatchProbability r PositiveAlphabet : ℝ)) ^ n at ZeroMass
  simpa only [MismatchProbability, sub_sub_cancel] using ZeroMass

/-- The probability of zero runtime is `r^(-n)`, with no conditioning on
initial failure. -/
theorem UniformHittingTimeZeroProbability {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetSize : 2 ≤ r) (Target : MultiValues n r) :
    (PathMeasure (Step PositiveLength AlphabetSize Target)
      (MultivalRLSInit n r (by omega))).real
        {Path | FirstHittingTime (fun x => x = Target) Path = 0} = (1 / (r : ℝ))^n := by
  have ZeroEvent : {Path : Nat → MultiValues n r |
      FirstHittingTime (fun x => x = Target) Path = 0} =
      (fun Path => Path 0) ⁻¹' {x | Hamming Target x = 0} := by
    ext Path
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, FirstHittingTimeEqZeroIff,
      HammingEqZeroIffEq]
  rw [ZeroEvent, ← map_measureReal_apply (measurable_pi_apply 0)
    (Set.to_countable _).measurableSet, PathMeasureInitial]
  exact UniformHammingZeroProbability _ Target

theorem MismatchProbabilityAtLeastHalf {r : Nat} (AlphabetSize : 2 ≤ r) :
    (1/2 : ℝ) ≤ MismatchProbability r (by omega) := by
  change (1/2 : ℝ) ≤ 1 - 1 / (r : ℝ)
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast AlphabetSize
  have ReciprocalBound : 1 / (r : ℝ) ≤ 1/2 := by
    exact one_div_le_one_div_of_le (by norm_num) hr
  linarith

/-- Explicit form of the uniform-initialization estimate in Theorem 6 of
Doerr, Doerr, and Koetzing (2018): the normalized runtime differs from `log n`
by at most one, uniformly for positive length, alphabet size at least two,
and every target. Thus `C=1` and `N=1` suffice. -/
theorem UniformRuntimeLogError {n r : Nat} (PositiveLength : 0 < n) (AlphabetSize : 2 ≤ r)
    (Target : MultiValues n r) :
    |(ExpectedUniformRuntime PositiveLength AlphabetSize Target).toReal /
      ((n : ℝ) * ((r-1 : Nat) : ℝ)) - Real.log n| ≤ 1 := by
  have ScalePositive : 0 < (n : ℝ) * ((r-1 : Nat) : ℝ) := by
    exact mul_pos (Nat.cast_pos.mpr PositiveLength) (Nat.cast_pos.mpr (by omega))
  rw [UniformRuntimeExactReal, mul_div_cancel_left₀ _ (ne_of_gt ScalePositive)]
  exact BinomialHarmonicLogBound PositiveLength _ (MismatchProbabilityAtLeastHalf AlphabetSize)

/-- Quantified O(1) error with constants uniform over alphabet sizes
`r ≥ 2` and all targets, supplied by the explicit unit-error theorem. -/
theorem UniformRuntimeLeadingTerm :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : Nat, ∃ ThresholdPositive : 1 ≤ N,
      ∀ (n : Nat) (LargeEnough : N ≤ n) (r : Nat) (AlphabetSize : 2 ≤ r)
        (Target : MultiValues n r),
        |(ExpectedUniformRuntime (by omega) AlphabetSize Target).toReal /
          ((n : ℝ) * ((r-1 : Nat) : ℝ)) - Real.log n| ≤ C := by
  refine ⟨1, by norm_num, 1, by omega, ?_⟩
  intro n LargeEnough r AlphabetSize Target
  exact UniformRuntimeLogError (by omega) AlphabetSize Target

end
end ECTheoryLib.Analysis.RLSMultival
