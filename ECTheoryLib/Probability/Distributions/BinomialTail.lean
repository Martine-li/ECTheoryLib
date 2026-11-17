import ECTheoryLib.Probability.Distributions.BinomialConditioning

/-!
# Combinatorial binomial tail bounds

Book Theorem 1.10.37 follows from the binomial choose moment and Mathlib's
Markov inequality. All natural thresholds and probability endpoints are retained.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- The factorial moment in binomial-coefficient normalization. -/
theorem BinomialChooseMoment (n k : ℕ) (p : I) :
    (∫ j, (j.choose k : ℝ) ∂binomial n p) = (n.choose k : ℝ) * (p : ℝ) ^ k := by
  -- Normalize the shifted binomial law using the already proved mass identity.
  by_cases Threshold : k ≤ n
  · let ν := (binomial (n - k) p).map (fun j => j + k)
    have Probabilityν : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_map (measurable_of_countable (fun j : ℕ => j + k)).aemeasurable
    have Support : ∀ᵐ j ∂ν, j ∈ Finset.Iic n := by
      apply (ae_map_iff (measurable_of_countable (fun j : ℕ => j + k)).aemeasurable
        (Set.to_countable _).measurableSet).mpr
      filter_upwards [ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial (n - k) p))] with j Bound
      change j ≤ n - k at Bound
      rw [Finset.mem_Iic]
      omega
    have Total : (∑ j ∈ Finset.Iic n, ν.real {j}) = 1 := by
      rw [sum_measureReal_singleton, measureReal_def]
      have Full : ν (↑(Finset.Iic n) : Set ℕ) = 1 := by
        calc
          ν (↑(Finset.Iic n) : Set ℕ) = ν ((↑(Finset.Iic n) : Set ℕ) ∩ univ) := by
            rw [inter_univ]
          _ = ν univ := Measure.measure_inter_eq_of_ae Support
          _ = 1 := measure_univ
      rw [Full, ENNReal.toReal_one]
    rw [integral_binomial]
    calc
      (∑ j ∈ Finset.Iic n,
          ((n.choose j : ℝ) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ (n - j)) • (j.choose k : ℝ)) =
          ∑ j ∈ Finset.Iic n, ((n.choose k : ℝ) * (p : ℝ) ^ k) * ν.real {j} := by
        apply Finset.sum_congr rfl
        intro j Member
        have Below : j ≤ n := Finset.mem_Iic.mp Member
        by_cases Above : k ≤ j
        · have Mass := BinomialForcedSuccessMass n k j p Above Below
          rw [binomial_real_singleton] at Mass
          change _ * (j.choose k : ℝ) = _
          calc
            _ = (j.choose k : ℝ) * ((n.choose j : ℝ) * (p : ℝ) ^ j *
                (1 - (p : ℝ)) ^ (n - j)) := by ring
            _ = _ := Mass.symm
        · have TooSmall : j < k := Nat.lt_of_not_ge Above
          rw [Nat.choose_eq_zero_of_lt TooSmall, Nat.cast_zero, smul_zero,
            ShiftedBinomialSingletonBelow (n - k) k j p TooSmall, mul_zero]
      _ = ((n.choose k : ℝ) * (p : ℝ) ^ k) * ∑ j ∈ Finset.Iic n, ν.real {j} := by
        rw [Finset.mul_sum]
      _ = (n.choose k : ℝ) * (p : ℝ) ^ k := by rw [Total, mul_one]
  · have TooLarge : n < k := Nat.lt_of_not_ge Threshold
    rw [Nat.choose_eq_zero_of_lt TooLarge, Nat.cast_zero, zero_mul]
    have ZeroAE : (fun j => (j.choose k : ℝ)) =ᵐ[binomial n p] (fun _ => 0) := by
      filter_upwards [ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))] with j Below
      change j ≤ n at Below
      rw [Nat.choose_eq_zero_of_lt (lt_of_le_of_lt Below TooLarge), Nat.cast_zero]
    rw [integral_congr_ae ZeroAE, integral_zero]

/-- Book 1.10.37, also valid above the support where both sides vanish. -/
theorem BinomialChooseUpperTail (n k : ℕ) (p : I) :
    (binomial n p).real (Ici k) ≤ (n.choose k : ℝ) * (p : ℝ) ^ k := by
  -- At least k successes is equivalent to choose(X,k) being at least one.
  have Nonnegative : 0 ≤ᵐ[binomial n p] (fun j => (j.choose k : ℝ)) :=
    ae_of_all _ (fun j => Nat.cast_nonneg _)
  have Markov := mul_meas_ge_le_integral_of_nonneg Nonnegative
    (integrable_binomial (fun j => (j.choose k : ℝ))) 1
  have EventEq : {j : ℕ | (1 : ℝ) ≤ (j.choose k : ℝ)} = Ici k := by
    ext j
    change (1 : ℝ) ≤ (j.choose k : ℝ) ↔ k ≤ j
    rw [Nat.one_le_cast, Nat.one_le_iff_ne_zero, Nat.choose_ne_zero_iff]
  rw [one_mul, EventEq, BinomialChooseMoment] at Markov
  exact Markov

theorem BinomialChooseUpperTailENNReal (n k : ℕ) (p : I) :
    binomial n p (Ici k) ≤ ENNReal.ofReal ((n.choose k : ℝ) * (p : ℝ) ^ k) := by
  calc
    binomial n p (Ici k) = ENNReal.ofReal ((binomial n p).real (Ici k)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (BinomialChooseUpperTail n k p)

theorem BinomialRealChooseUpperTail (n k : ℕ) (p : I) :
    ((binomial n p).map (Nat.cast : ℕ → ℝ)).real (Ici (k : ℝ)) ≤
      (n.choose k : ℝ) * (p : ℝ) ^ k := by
  rw [map_measureReal_apply (measurable_of_countable (Nat.cast : ℕ → ℝ)) measurableSet_Ici]
  have EventEq : (Nat.cast : ℕ → ℝ) ⁻¹' Ici (k : ℝ) = Ici k := by
    ext j
    simp only [mem_preimage, mem_Ici, Nat.cast_le]
  rw [EventEq]
  exact BinomialChooseUpperTail n k p

theorem BinomialChooseUpperTailOfLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (n k : ℕ) (p : I)
    (Law : HasLaw X (binomial n p) P) :
    P {ω | k ≤ X ω} ≤ ENNReal.ofReal ((n.choose k : ℝ) * (p : ℝ) ^ k) := by
  rw [Law.measure_eq (p := fun j => k ≤ j) measurableSet_Ici]
  exact BinomialChooseUpperTailENNReal n k p

end
end ECTheoryLib.Probability

