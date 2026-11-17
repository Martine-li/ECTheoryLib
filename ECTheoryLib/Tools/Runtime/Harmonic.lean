import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Tactic

/-!
# Harmonic progress certificates

Real-valued properties of mathlib's rational harmonic numbers. A strict decrease
of a positive natural level d pays at least 1/d; monotone levels have nonnegative
harmonic progress. These facts support fitness-dependent event counting without
requiring equality of the level's transition laws or a Markov scalar potential.
-/
namespace ECTheoryLib.Tools.Runtime

/-- Harmonic potential is nonnegative, including H_0 = 0. -/
theorem HarmonicNonnegative (d : ℕ) : 0 ≤ (harmonic d : ℝ) := by
  unfold harmonic
  positivity

/-- A positive index has positive real harmonic potential, via mathlib. -/
theorem HarmonicPositive {Count : Nat} (PositiveCount : 0 < Count) :
    0 < (harmonic Count : ℝ) := by
  exact_mod_cast (harmonic_pos (Nat.ne_of_gt PositiveCount))

/-- Harmonic potential is monotone in its natural index. -/
theorem HarmonicMonotone {a b : ℕ} (Bound : a ≤ b) :
    (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono Bound)
  intro k _InRange _Outside
  positivity

/-- Every strict decrease from level d lowers harmonic potential by at least
1/d. The premise implies d > 0, so the reciprocal has its usual meaning. -/
theorem HarmonicGap {a d : ℕ} (Strict : a < d) :
    1 / (d : ℝ) ≤ (harmonic d : ℝ) - (harmonic a : ℝ) := by
  have CastBound : ((a + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast Strict
  have Reciprocal := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℝ) < ((a + 1 : ℕ) : ℝ) by positivity) CastBound
  have Monotone := HarmonicMonotone Strict
  rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at Monotone
  simp only [one_div] at Reciprocal ⊢
  linarith

/-- If at least d distinct elementary outcomes strictly lower a positive level
d, while all elementary outcomes are nonincreasing, their total harmonic
progress is at least one. Outcome probabilities can be supplied separately. -/
theorem HarmonicProgressCount {ι : Type*} [Fintype ι] (r : ι → ℕ) (d : ℕ)
    (Good : ι → Prop) [DecidablePred Good] (Positive : 0 < d)
    (Monotone : ∀ i, r i ≤ d) (Strict : ∀ i, Good i → r i < d)
    (Count : d ≤ (Finset.univ.filter Good).card) :
    1 ≤ ∑ i, ((harmonic d : ℝ) - (harmonic (r i) : ℝ)) := by
  classical
  have Pointwise (i : ι) : (if Good i then 1 / (d : ℝ) else 0) ≤
      (harmonic d : ℝ) - (harmonic (r i) : ℝ) := by
    split_ifs with IsGood
    · exact HarmonicGap (Strict i IsGood)
    · exact sub_nonneg.mpr (HarmonicMonotone (Monotone i))
  have SumBound := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => Pointwise i)
  have IndicatorSum : (∑ i, if Good i then 1 / (d : ℝ) else 0) =
      ((Finset.univ.filter Good).card : ℝ) / d := by
    rw [← Finset.sum_filter]
    simp [div_eq_mul_inv]
  rw [IndicatorSum] at SumBound
  apply le_trans ?_ SumBound
  apply (le_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast Positive)).mpr
  simpa only [one_mul] using (show (d : ℝ) ≤ (Finset.univ.filter Good).card by
    exact_mod_cast Count)

end ECTheoryLib.Tools.Runtime
