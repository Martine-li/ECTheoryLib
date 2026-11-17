import ECTheoryLib.Probability.Distributions.GeometricWaiting
import ECTheoryLib.Probability.StochasticOrder.StochasticDomination
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-!
# Geometric tails and the corrected parameter order

Doerr, Lemma 1.8.9(d), p. 31, has its domination direction reversed. For
0 < p <= q <= 1 the waiting time with parameter q is stochastically smaller.
The counterexample to the printed direction is retained in the external tests.

Mathlib counts failures from zero; the book counts trials from one. Both the
natural-valued and extended-natural-valued shifted laws are provided. The latter
can be compared to actual hitting times without discarding nontermination.
The artificial Mathlib zero-parameter convention is excluded.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- Lower tail for Mathlib failure counts, derived from its singleton masses. -/
theorem GeometricFailureLowerTail (p : I) (Positive : 0 < (p : ℝ)) (k : ℕ) :
    (geometricMeasure p).real (Iio k) = 1 - (1 - (p : ℝ)) ^ k := by
  have Nonzero : p ≠ 0 := by
    intro Zero
    have CoeZero : (p : ℝ) = 0 := congrArg Subtype.val Zero
    linarith
  induction k with
  | zero => simp
  | succ k InductionHypothesis =>
      have IntervalEq : Iio (k + 1) = Iio k ∪ {k} := by
        ext j
        simp only [mem_Iio, mem_union, mem_singleton_iff]
        omega
      have DisjointEvents : Disjoint (Iio k) ({k} : Set ℕ) := by
        apply Set.disjoint_left.mpr
        intro j Below Equal
        simp only [mem_Iio] at Below
        simp only [mem_singleton_iff] at Equal
        omega
      rw [IntervalEq, measureReal_union DisjointEvents (measurableSet_singleton k),
        InductionHypothesis, geometricMeasure_real_singleton Nonzero, pow_succ]
      ring

/-- Exact strict tail for the book convention: trials include the first success. -/
theorem GeometricWaitingTail (p : I) (Positive : 0 < (p : ℝ)) (k : ℕ) :
    ((geometricMeasure p).map Nat.succ).real (Ioi k) = (1 - (p : ℝ)) ^ k := by
  rw [map_measureReal_apply (measurable_of_countable Nat.succ) measurableSet_Ioi]
  have EventEq : Nat.succ ⁻¹' Ioi k = (Iio k)ᶜ := by
    ext j
    simp only [mem_preimage, mem_Ioi, mem_compl_iff, mem_Iio]
    omega
  rw [EventEq, probReal_compl_eq_one_sub measurableSet_Iio, GeometricFailureLowerTail]
  ring
  exact Positive

/-- Corrected Lemma 1.8.9(d): higher success probability gives a smaller waiting law. -/
theorem GeometricWaitingStochasticAntitone (p q : I)
    (PositiveP : 0 < (p : ℝ)) (Parameters : p ≤ q) :
    StochasticDominated ((geometricMeasure q).map Nat.succ)
      ((geometricMeasure p).map Nat.succ) := by
  have PositiveQ : 0 < (q : ℝ) := lt_of_lt_of_le PositiveP Parameters
  have ProbabilityLaw (r : I) : IsProbabilityMeasure ((geometricMeasure r).map Nat.succ) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable Nat.succ).aemeasurable
  apply (StochasticDominatedIffStrictTail _ _).mpr
  intro k
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((geometricMeasure q).map Nat.succ).real (Ioi k) ≤
    ((geometricMeasure p).map Nat.succ).real (Ioi k)
  rw [GeometricWaitingTail q PositiveQ, GeometricWaitingTail p PositiveP]
  exact pow_le_pow_left₀ (sub_nonneg.mpr q.2.2)
    (sub_le_sub_left (show (p : ℝ) ≤ (q : ℝ) from Parameters) 1) k

/-- The same strict tail with the shifted law embedded into extended naturals. -/
theorem GeometricWaitingExtendedTail (p : I) (Positive : 0 < (p : ℝ)) (k : ℕ) :
    ((geometricMeasure p).map (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))).real
      (Ioi (k : WithTop ℕ)) = (1 - (p : ℝ)) ^ k := by
  rw [map_measureReal_apply (measurable_of_countable _) measurableSet_Ioi]
  have EventEq : (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ)) ⁻¹' Ioi (k : WithTop ℕ) =
      Nat.succ ⁻¹' Ioi k := by
    ext j
    simp only [mem_preimage, mem_Ioi, Nat.succ_eq_add_one]
    norm_cast
  rw [EventEq, ← map_measureReal_apply (measurable_of_countable Nat.succ) measurableSet_Ioi]
  exact GeometricWaitingTail p Positive k

/-- Corrected parameter order on extended naturals; no conversion of infinity to zero. -/
theorem GeometricWaitingExtendedStochasticAntitone (p q : I)
    (PositiveP : 0 < (p : ℝ)) (Parameters : p ≤ q) :
    StochasticDominated
      ((geometricMeasure q).map (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ)))
      ((geometricMeasure p).map (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))) := by
  have PositiveQ : 0 < (q : ℝ) := lt_of_lt_of_le PositiveP Parameters
  have ProbabilityLaw (r : I) : IsProbabilityMeasure
      ((geometricMeasure r).map (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply (StochasticDominatedIffStrictTail _ _).mpr
  intro a
  cases a using WithTop.recTopCoe with
  | top => simp only [Ioi_top, measure_empty, le_refl]
  | coe k =>
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
      change ((geometricMeasure q).map (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))).real
          (Ioi (k : WithTop ℕ)) ≤
        ((geometricMeasure p).map (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))).real
          (Ioi (k : WithTop ℕ))
      rw [GeometricWaitingExtendedTail q PositiveQ, GeometricWaitingExtendedTail p PositiveP]
      exact pow_le_pow_left₀ (sub_nonneg.mpr q.2.2)
        (sub_le_sub_left (show (p : ℝ) ≤ (q : ℝ) from Parameters) 1) k

end
end ECTheoryLib.Probability

