import ECTheoryLib.Analysis.OneMinMax.GSEMO.RuntimeBounds
import ECTheoryLib.Operators.Selection.ArchiveParent
import ECTheoryLib.Operators.Mutation.OneBitBounds

/-!
# Coverage with an archive-dependent preferred parent

The policy selects uniformly with probability one half and otherwise selects a
preferred current member. The preference may use the entire archive; no equality
of drift between states sharing a scalar potential is required. The uniform
component preserves a parent floor of `1/[2(n+1)]` on valid OneMinMax archives.

The frozen coverage theorem is instantiated with both one-bit and standard-bit
mutation. Preference affects the actual kernel, while the common worst-case
guarantee costs a factor of two compared with the uniform-parent bound.
-/
namespace ECTheoryLib.Analysis.BiasedArchiveOneMinMax
open MeasureTheory ECTheoryLib.Probability OneMinMaxCoverage
noncomputable section

/-- Actual expected coverage time for the mixed parent policy and supplied mutation.
Time zero is the supplied initial archive distribution. -/
def ExpectedRuntime {n : Nat}
    (Preferred : (P : ParetoPopulation (Bits n)) → {x // x ∈ P.val})
    (Mutation : Bits n → PMF (Bits n)) (Initial : PMF (ParetoPopulation (Bits n))) : ENNReal :=
  ExpectedHittingTime (ArchiveSearchStep (HalfUniformArchiveParent Preferred) Mutation Dominates)
    Complete Initial

/-- The mixed policy retains probability at least `1/[2(n+1)]` for every
member of every valid current archive, regardless of the preference rule. -/
theorem ParentProbabilityFloor {n : Nat}
    (Preferred : (P : ParetoPopulation (Bits n)) → {x // x ∈ P.val})
    (P : ParetoPopulation (Bits n)) (IsValid : Valid P) (x : Bits n) (InP : x ∈ P.val) :
    1 / (2 * ((n : ℝ) + 1)) ≤ (HalfUniformArchiveParent Preferred P x).toReal := by
  have Mixed := ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (HalfUniformArchiveParentLower Preferred P x)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at Mixed
  calc
    1 / (2 * ((n : ℝ) + 1)) = (2 : ℝ)⁻¹ * (1 / ((n : ℝ) + 1)) := by
      simp only [one_div, mul_inv]
    _ ≤ (2 : ℝ)⁻¹ * (UniformParetoParent P x).toReal :=
      mul_le_mul_of_nonneg_left (UniformParentFloor P IsValid x InP) (by norm_num)
    _ ≤ _ := Mixed

/-- A mutation with exact-one-bit floor Delta has full-coverage bound
`4(n+1)H_(n+1)/Delta` under every such preferred-parent policy.
Initialization may be any valid nonempty archive distribution. -/
theorem RuntimeProbabilityBound {n : Nat}
    (Preferred : (P : ParetoPopulation (Bits n)) → {x // x ∈ P.val})
    (Mutation : Bits n → PMF (Bits n)) (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedRuntime Preferred Mutation Initial ≤
      ENNReal.ofReal (4 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ) / Delta) := by
  have Bound := OneMinMaxCoverage.RuntimeHarmonicBound
    (HalfUniformArchiveParent Preferred) Mutation (1 / (2 * ((n : ℝ) + 1))) Delta
    (by positivity) PositiveDelta (ParentProbabilityFloor Preferred)
    MutationFloor Initial InitiallyValid
  have Normalize : 2 * (harmonic (n + 1) : ℝ) /
      ((1 / (2 * ((n : ℝ) + 1))) * Delta) =
      4 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ) / Delta := by
    field_simp
    ring
  rw [Normalize] at Bound
  exact Bound

/-- One-bit mutation with the mixed parent policy has expected complete coverage
time at most `4 n (n+1) H_(n+1)` from the standard uniform singleton. -/
theorem OneBitRuntimeBound {n : Nat} (hn : 0 < n)
    (Preferred : (P : ParetoPopulation (Bits n)) → {x // x ∈ P.val}) :
    ExpectedRuntime Preferred (RandomOneBitMutation hn) (SEMOInit n) ≤
      ENNReal.ofReal (4 * (n : ℝ) * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) := by
  have Bound := RuntimeProbabilityBound Preferred (RandomOneBitMutation hn) (1 / (n : ℝ))
    (by positivity) (fun x i => (RandomOneBitProbabilityReal hn x i).ge)
    (SEMOInit n) (fun P Possible => SEMOInitValid Dominates P Possible)
  have Normalize : 4 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ) / (1 / (n : ℝ)) =
      4 * (n : ℝ) * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ) := by
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring
  rw [Normalize] at Bound
  exact Bound

/-- Standard bit mutation with the mixed parent policy has expected complete
coverage time at most `4 e n (n+1) H_(n+1)` from the standard singleton law. -/
theorem StandardBitRuntimeBound {n : Nat} (hn : 0 < n)
    (Preferred : (P : ParetoPopulation (Bits n)) → {x // x ∈ P.val}) :
    ExpectedRuntime Preferred (StandardBitMutation hn) (GSEMOInit n) ≤
      ENNReal.ofReal (4 * Real.exp 1 * (n : ℝ) * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) := by
  apply (RuntimeProbabilityBound Preferred (StandardBitMutation hn) (StandardOneBitProbability n)
    (StandardOneBitProbabilityPositive hn) (fun x i => (StandardBitMutationOneBitReal hn x i).ge)
    (GSEMOInit n) (fun P Possible => GSEMOInitValid Dominates P Possible)).trans
  apply ENNReal.ofReal_le_ofReal
  have HarmonicNonnegative : (0 : ℝ) ≤ (harmonic (n + 1) : ℝ) := by
    unfold harmonic
    positivity
  calc
    4 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ) / StandardOneBitProbability n =
        (4 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) * (1 / StandardOneBitProbability n) := by ring
    _ ≤ (4 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) * (Real.exp 1 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (StandardOneBitProbabilityInverseBound hn) (by positivity)
    _ = _ := by ring

end
end ECTheoryLib.Analysis.BiasedArchiveOneMinMax
