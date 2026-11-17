import ECTheoryLib.Probability.Distributions.BinomialDomination
import ECTheoryLib.Probability.StochasticOrder.StochasticConditioning

/-!
# Conditional binomial stochastic comparison

Doerr, Lemma 1.8.9(c), p. 31, in Theory of Evolutionary Computation.
For 0 <= x <= n, conditional on a positive-probability event X >= x,
X <=st (X | X >= x) <=st X+x. The proof retains n=0, x=0 and p=0/1 whenever
the conditioning event is possible. Mathlib supplies binomial masses, support,
conditional measures and the choose-multiplication identity.

The upper comparison first bounds by x+Bin(n-x,p), then reuses the already
proved monotonicity in the number of trials. The intermediate law is an actual
shifted binomial measure, not an assumed coupling or a new axiom.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- A shifted binomial mass above its deterministic offset. -/
theorem ShiftedBinomialSingleton (n x k : ℕ) (p : I) (Above : x ≤ k) :
    ((binomial n p).map (fun j => j + x)).real {k} = (binomial n p).real {k - x} := by
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton k)]
  have Fiber : (fun j : ℕ => j + x) ⁻¹' {k} = {k - x} := by
    ext j
    simp only [mem_preimage, mem_singleton_iff]
    omega
  rw [Fiber]

/-- The shifted law gives zero mass below its deterministic offset. -/
theorem ShiftedBinomialSingletonBelow (n x k : ℕ) (p : I) (Below : k < x) :
    ((binomial n p).map (fun j => j + x)).real {k} = 0 := by
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton k)]
  have Fiber : (fun j : ℕ => j + x) ⁻¹' {k} = ∅ := by
    ext j
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    omega
  rw [Fiber, measureReal_empty]

/-- Forcing x successes weights each original binomial mass by its number of x-subsets. -/
theorem BinomialForcedSuccessMass (n x k : ℕ) (p : I)
    (Above : x ≤ k) (Below : k ≤ n) :
    ((n.choose x : ℝ) * (p : ℝ) ^ x) *
        ((binomial (n - x) p).map (fun j => j + x)).real {k} =
      (k.choose x : ℝ) * (binomial n p).real {k} := by
  rw [ShiftedBinomialSingleton _ _ _ _ Above, binomial_real_singleton, binomial_real_singleton]
  have ChooseIdentity : (n.choose x : ℝ) * ((n - x).choose (k - x) : ℝ) =
      (n.choose k : ℝ) * (k.choose x : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := n) Above).symm
  have FailureExponent : n - x - (k - x) = n - k := by omega
  have SuccessExponent : x + (k - x) = k := by omega
  rw [FailureExponent]
  calc
    ((n.choose x : ℝ) * (p : ℝ) ^ x) *
        (((n - x).choose (k - x) : ℝ) * (p : ℝ) ^ (k - x) * (1 - (p : ℝ)) ^ (n - k)) =
      ((n.choose x : ℝ) * ((n - x).choose (k - x) : ℝ)) *
        ((p : ℝ) ^ x * (p : ℝ) ^ (k - x)) * (1 - (p : ℝ)) ^ (n - k) := by ring
    _ = ((n.choose k : ℝ) * (k.choose x : ℝ)) *
        (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
      rw [ChooseIdentity, ← pow_add, SuccessExponent]
    _ = _ := by ring

/-- Conditioning on at least x successes is dominated by x forced successes and n-x fresh trials. -/
theorem ConditionalBinomialLEForced (n x : ℕ) (p : I) (Threshold : x ≤ n)
    (PositiveP : 0 < (p : ℝ)) (PositiveEvent : binomial n p (Ici x) ≠ 0) :
    StochasticDominated (cond (binomial n p) (Ici x))
      ((binomial (n - x) p).map (fun j => j + x)) := by
  classical
  let μ := binomial n p
  let ν := (binomial (n - x) p).map (fun j => j + x)
  let C : ℝ := (n.choose x : ℝ) * (p : ℝ) ^ x
  let D : ℝ := μ.real (Ici x)
  have PositiveC : 0 < C := by
    apply mul_pos
    · exact_mod_cast Nat.choose_pos Threshold
    · exact pow_pos PositiveP x
  have PositiveD : 0 < D := (ENNReal.toReal_pos PositiveEvent (measure_ne_top _ _))
  have ConditionalProbability : IsProbabilityMeasure (cond μ (Ici x)) :=
    cond_isProbabilityMeasure PositiveEvent
  have ShiftProbability : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have OriginalBound : ∀ᵐ j ∂μ, j ≤ n :=
    ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))
  have FirstSupport : ∀ᵐ j ∂cond μ (Ici x), j ∈ Finset.range (n + 1) := by
    have Bound : ∀ᵐ j ∂cond μ (Ici x), j ≤ n := cond_absolutelyContinuous.ae_le OriginalBound
    filter_upwards [Bound] with j Below
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le Below)
  have SecondSupport : ∀ᵐ j ∂ν, j ∈ Finset.range (n + 1) := by
    apply (ae_map_iff (measurable_of_countable (fun j : ℕ => j + x)).aemeasurable
      (Set.to_countable _).measurableSet).mpr
    have Bound : ∀ᵐ j ∂binomial (n - x) p, j ≤ n - x :=
      ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial (n - x) p))
    filter_upwards [Bound] with j Below
    apply Finset.mem_range.mpr
    omega
  have ShiftMass (k : ℕ) (Above : x ≤ k) (Below : k ≤ n) :
      ν.real {k} = ((k.choose x : ℝ) * μ.real {k}) / C := by
    apply (eq_div_iff PositiveC.ne').mpr
    rw [mul_comm]
    exact BinomialForcedSuccessMass n x k p Above Below
  apply StochasticDominatedOfFiniteLikelihoodRatio (cond μ (Ici x)) ν
    (Finset.range (n + 1)) FirstSupport SecondSupport
  intro i InRangeI j InRangeJ Ordered
  have BelowI : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp InRangeI)
  have BelowJ : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp InRangeJ)
  by_cases AboveI : x ≤ i
  · have AboveJ : x ≤ j := le_trans AboveI Ordered
    rw [ConditionalSingletonReal, ConditionalSingletonReal]
    simp only [mem_Ici, if_pos AboveI, if_pos AboveJ]
    rw [ShiftMass i AboveI BelowI, ShiftMass j AboveJ BelowJ]
    change (((i.choose x : ℝ) * μ.real {i}) / C) * (μ.real {j} / D) ≤
      (μ.real {i} / D) * (((j.choose x : ℝ) * μ.real {j}) / C)
    have ProductOrder : (i.choose x : ℝ) * (μ.real {i} * μ.real {j}) ≤
        (j.choose x : ℝ) * (μ.real {i} * μ.real {j}) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.choose_le_choose x Ordered
      · exact mul_nonneg measureReal_nonneg measureReal_nonneg
    have Divided := div_le_div_of_nonneg_right ProductOrder (mul_pos PositiveC PositiveD).le
    calc
      (((i.choose x : ℝ) * μ.real {i}) / C) * (μ.real {j} / D) =
          ((i.choose x : ℝ) * (μ.real {i} * μ.real {j})) / (C * D) := by ring
      _ ≤ ((j.choose x : ℝ) * (μ.real {i} * μ.real {j})) / (C * D) := Divided
      _ = (μ.real {i} / D) * (((j.choose x : ℝ) * μ.real {j}) / C) := by ring
  · have BelowThreshold : i < x := lt_of_not_ge AboveI
    have ZeroShift : ν.real {i} = 0 := ShiftedBinomialSingletonBelow (n - x) x i p BelowThreshold
    rw [ZeroShift, zero_mul]
    exact mul_nonneg measureReal_nonneg measureReal_nonneg

/-- Lemma 1.8.9(c): X is dominated by X conditioned on X>=x, which is dominated by X+x. -/
theorem ConditionalBinomialBounds (n x : ℕ) (p : I) (Threshold : x ≤ n)
    (PositiveEvent : binomial n p (Ici x) ≠ 0) :
    StochasticDominated (binomial n p) (cond (binomial n p) (Ici x)) ∧
      StochasticDominated (cond (binomial n p) (Ici x))
        ((binomial n p).map (fun j => j + x)) := by
  have OriginalBound : ∀ᵐ j ∂binomial n p, j ≤ n :=
    ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))
  have Support : ∀ᵐ j ∂binomial n p, j ∈ Finset.range (n + 1) := by
    filter_upwards [OriginalBound] with j Below
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le Below)
  constructor
  · exact StochasticDominatedFiniteUpperCondition (binomial n p) (Finset.range (n + 1))
      Support (Ici x) (isUpperSet_Ici x) PositiveEvent
  · by_cases ZeroThreshold : x = 0
    · subst x
      rw [show Ici (0 : ℕ) = univ from Ici_bot, cond_univ]
      simp only [Nat.add_zero]
      change StochasticDominated (binomial n p) ((binomial n p).map id)
      rw [Measure.map_id]
      exact StochasticDominatedRefl _
    · have PositiveP : 0 < (p : ℝ) := by
        by_contra NotPositive
        have ZeroReal : (p : ℝ) = 0 := le_antisymm (le_of_not_gt NotPositive) p.2.1
        have ZeroP : p = 0 := Subtype.ext ZeroReal
        subst p
        have ZeroLaw : binomial n 0 = Measure.dirac 0 := by
          rw [binomial, setBernoulli_zero, Measure.map_dirac' measurable_ncard]
          rw [Set.ncard_empty]
        apply PositiveEvent
        rw [ZeroLaw]
        have NotMember : (0 : ℕ) ∉ Ici x := by
          simp only [mem_Ici]
          omega
        rw [Measure.dirac_apply' 0 measurableSet_Ici, Set.indicator_of_notMem NotMember]
      have ToForced := ConditionalBinomialLEForced n x p Threshold PositiveP PositiveEvent
      have Remaining := BinomialStochasticDominated (n - x) n p p (Nat.sub_le n x) le_rfl
      exact StochasticDominatedTrans ToForced (StochasticDominatedNatAdd _ _ Remaining x)

/-- A positive success probability makes each binomial upper event up to n have positive probability. -/
theorem BinomialUpperTailPositive (n x : ℕ) (p : I) (Threshold : x ≤ n)
    (PositiveP : 0 < (p : ℝ)) : binomial n p (Ici x) ≠ 0 := by
  have PositiveSingleton : 0 < binomial n p {n} := by
    rw [binomial_singleton]
    simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, mul_one]
    exact ENNReal.ofReal_pos.mpr (pow_pos PositiveP n)
  apply ne_of_gt
  apply lt_of_lt_of_le PositiveSingleton
  apply measure_mono
  exact Set.singleton_subset_iff.mpr Threshold

end
end ECTheoryLib.Probability
