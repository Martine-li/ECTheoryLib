import ECTheoryLib.Probability.Moments.ExponentialTailExpectation

namespace ECTheoryLib.Probability

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Book 1.6.2(b) with an explicit natural center. Only the finite positive
integer offset window is required; the natural type retains nonnegativity. -/
theorem ExpectedNatGeOfExponentialLowerTail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Nat) (B : Nat) (α β : ℝ)
    (YMeasurable : Measurable Y)
    (YIntegrable : Integrable (fun ω => (Y ω : ℝ)) μ)
    (PositiveAlpha : 0 < α) (PositiveBeta : 0 < β)
    (Tail : ∀ k : Nat, 0 < k → k ≤ B →
      μ {ω | Y ω ≤ B - k} ≤ ENNReal.ofReal (α * Real.exp (-(k : ℝ) / β))) :
    (B : ℝ) - α * β ≤ ∫ ω, (Y ω : ℝ) ∂μ := by
  let Z : Ω → Int := fun ω => (B : Int) - (Y ω : Int)
  have ZMeasurable : Measurable Z :=
    (measurable_of_countable (fun y : Nat => (B : Int) - (y : Int))).comp YMeasurable
  have ZIntegrable : Integrable (fun ω => (Z ω : ℝ)) μ := by
    apply ((integrable_const (μ := μ) (B : ℝ)).sub YIntegrable).congr
    filter_upwards [] with ω
    change (B : ℝ) - (Y ω : ℝ) = (Z ω : ℝ)
    simp only [Z, Int.cast_sub, Int.cast_natCast]
  have ZTail : ∀ k : Nat, 0 < k →
      μ {ω | ((0 + k : Nat) : Int) ≤ Z ω} ≤
        ENNReal.ofReal (α * Real.exp (-(k : ℝ) / β)) := by
    intro k PositiveK
    by_cases InWindow : k ≤ B
    · have Event : {ω | ((0 + k : Nat) : Int) ≤ Z ω} = {ω | Y ω ≤ B - k} := by
        ext ω
        change ((0 + k : Nat) : Int) ≤ (B : Int) - (Y ω : Int) ↔ Y ω ≤ B - k
        simp only [Nat.zero_add]
        omega
      rw [Event]
      exact Tail k PositiveK InWindow
    · have Empty : {ω | ((0 + k : Nat) : Int) ≤ Z ω} = ∅ := by
        ext ω
        change (((0 + k : Nat) : Int) ≤ (B : Int) - (Y ω : Int)) ↔ False
        simp only [Nat.zero_add, iff_false]
        intro Impossible
        have Nonnegative : (0 : Int) ≤ (Y ω : Int) := Int.natCast_nonneg _
        have Larger : (B : Int) < (k : Int) := by exact_mod_cast (lt_of_not_ge InWindow)
        omega
      rw [Empty, measure_empty]
      exact zero_le
  have Bound := ExpectedIntLeOfExponentialTail μ Z 0 α β ZMeasurable ZIntegrable
    PositiveAlpha PositiveBeta ZTail
  simp only [Z, Int.cast_sub, Int.cast_natCast, Nat.cast_zero, zero_add] at Bound
  rw [integral_sub (integrable_const _) YIntegrable] at Bound
  simp only [integral_const, probReal_univ, one_smul] at Bound
  linarith

/-- The finite-window lower bound also applies to extended-natural variables.
Truncation preserves infinity correctly and removes any finite-mean premise. -/
theorem ExpectedWithTopNatGeOfExponentialLowerTail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Ω → WithTop Nat) (B : Nat) (α β : ℝ)
    (TimeMeasurable : Measurable τ)
    (PositiveAlpha : 0 < α) (PositiveBeta : 0 < β)
    (Tail : ∀ k : Nat, 0 < k → k ≤ B →
      μ {ω | τ ω ≤ ((B - k : Nat) : WithTop Nat)} ≤
        ENNReal.ofReal (α * Real.exp (-(k : ℝ) / β))) :
    ENNReal.ofReal ((B : ℝ) - α * β) ≤ ∫⁻ ω, ENat.toENNReal (τ ω) ∂μ := by
  let Y : Ω → Nat := fun ω => ENat.toNat (min (τ ω : ENat) (B : ENat))
  have YCast (ω : Ω) : (Y ω : ENat) = min (τ ω : ENat) (B : ENat) :=
    ENat.natCast_toNat (ne_top_of_le_ne_top (by simp : (B : ENat) ≠ ⊤)
      (min_le_right (τ ω) (B : ENat)))
  have YLeB (ω : Ω) : Y ω ≤ B :=
    ENat.toNat_le_of_le_natCast (min_le_right _ _)
  have YMeasurable : Measurable Y :=
    (measurable_of_countable (fun t : WithTop Nat => ENat.toNat (min (t : ENat) (B : ENat)))).comp
      TimeMeasurable
  have YIntegrable : Integrable (fun ω => (Y ω : ℝ)) μ := by
    have RealMeasurable : Measurable (fun ω => (Y ω : ℝ)) :=
      (measurable_of_countable (fun y : Nat => (y : ℝ))).comp YMeasurable
    apply Integrable.of_bound RealMeasurable.aestronglyMeasurable (B : ℝ)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast YLeB ω
  have YTail : ∀ k : Nat, 0 < k → k ≤ B →
      μ {ω | Y ω ≤ B - k} ≤ ENNReal.ofReal (α * Real.exp (-(k : ℝ) / β)) := by
    intro k PositiveK InWindow
    have Event : {ω | Y ω ≤ B - k} = {ω | τ ω ≤ ((B - k : Nat) : WithTop Nat)} := by
      ext ω
      change Y ω ≤ B - k ↔ τ ω ≤ ((B - k : Nat) : WithTop Nat)
      rw [← ENat.natCast_le_natCast]
      change (Y ω : ENat) ≤ ((B - k : Nat) : ENat) ↔
        (τ ω : ENat) ≤ ((B - k : Nat) : ENat)
      rw [YCast]
      change min (τ ω : ENat) (B : ENat) ≤ ((B - k : Nat) : ENat) ↔
        (τ ω : ENat) ≤ ((B - k : Nat) : ENat)
      have TooSmall : ¬ (B : ENat) ≤ ((B - k : Nat) : ENat) := by
        rw [ENat.natCast_le_natCast]
        omega
      constructor
      · intro Below
        exact ((min_le_iff (α := ENat)).mp Below).resolve_right TooSmall
      · intro Below
        exact (min_le_left (τ ω : ENat) (B : ENat)).trans Below
    rw [Event]
    exact Tail k PositiveK InWindow
  have Bound := ExpectedNatGeOfExponentialLowerTail μ Y B α β YMeasurable YIntegrable
    PositiveAlpha PositiveBeta YTail
  calc
    ENNReal.ofReal ((B : ℝ) - α * β) ≤ ENNReal.ofReal (∫ ω, (Y ω : ℝ) ∂μ) :=
      ENNReal.ofReal_le_ofReal Bound
    _ = ∫⁻ ω, ENNReal.ofReal (Y ω : ℝ) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal YIntegrable
        (ae_of_all _ (fun ω => Nat.cast_nonneg (Y ω)))
    _ ≤ ∫⁻ ω, ENat.toENNReal (τ ω) ∂μ := by
      apply lintegral_mono
      intro ω
      change ENNReal.ofReal (Y ω : ℝ) ≤ ENat.toENNReal (τ ω : ENat)
      rw [ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, YCast]
      exact ENat.toENNReal_mono (min_le_left _ _)

end
end ECTheoryLib.Probability

