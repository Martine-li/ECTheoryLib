import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Logarithmic thresholds for power-tail bounds

Book Lemma 1.10.2 uses a nested logarithmic quotient. Its denominator vanishes
at the interior input t = exp(e). We prove the displayed expression on exactly
its positive-denominator domain and provide an explicit single-point correction
e^2 on the full original domain t >= exp(exp(1/e)). Both sides of the singular
input remain included. The total-division value is not a valid bound there.

These scalar results reuse Mathlib real logarithms, powers and order laws;
no mutation or probability model is assumed. The source discrepancy is documented
in docs/reports/source-audits/book-1102-1103-20261022.md.
-/

namespace ECTheoryLib.Probability.PowerTailThreshold
noncomputable section

/-- Nested-log denominator in the displayed formula of book Lemma 1.10.2. -/
def logDenominator (t : ℝ) : ℝ :=
  Real.log (Real.log t / (Real.exp 1 * Real.log (Real.log t)))

/-- Displayed quotient, using Lean total division. At the singular input this is zero, so use `repairedThreshold` for a bound on the full source domain. -/
def displayedThreshold (t : ℝ) : ℝ := Real.log t / logDenominator t

/-- The original displayed formula is valid when its logarithmic denominator is positive. -/
theorem displayedThreshold_bound_of_denominator_pos (t : ℝ)
    (OriginalRange : Real.exp (Real.exp (1 / Real.exp 1)) ≤ t)
    (PositiveD :
      0 < Real.log (Real.log t / (Real.exp 1 * Real.log (Real.log t)))) :
    let δ : ℝ :=
      Real.log t / Real.log (Real.log t / (Real.exp 1 * Real.log (Real.log t)))
    (Real.exp 1 / δ) ^ δ ≤ 1 / t := by
  let e : ℝ := Real.exp 1
  let u : ℝ := Real.log t
  let s : ℝ := Real.log u
  let D : ℝ := Real.log (u / (e * s))
  let δ : ℝ := u / D
  change (e / δ) ^ δ ≤ 1 / t

  -- Use the original range twice, before introducing logarithmic identities.
  have he : 0 < e := Real.exp_pos 1
  have ht : 0 < t :=
    (Real.exp_pos (Real.exp (1 / e))).trans_le OriginalRange
  have huLower : Real.exp (1 / e) ≤ u :=
    (Real.le_log_iff_exp_le ht).2 OriginalRange
  have hu : 0 < u := (Real.exp_pos (1 / e)).trans_le huLower
  have hsLower : 1 / e ≤ s :=
    (Real.le_log_iff_exp_le hu).2 huLower
  have hs : 0 < s := (div_pos zero_lt_one he).trans_le hsLower
  have hes : 0 < e * s := mul_pos he hs
  have hesLower : 1 ≤ e * s := by
    have h : 1 ≤ s * e := (div_le_iff₀ he).1 hsLower
    simpa only [mul_comm] using h
  have hD : 0 < D := PositiveD
  have hδ : 0 < δ := div_pos hu hD

  -- D = s - log(e*s) ≤ s, so its logarithm can be compared with log s.
  have hDExpand : D = s - Real.log (e * s) :=
    Real.log_div hu.ne' hes.ne'
  have hDLe : D ≤ s := by
    have hNonnegative : 0 ≤ Real.log (e * s) := Real.log_nonneg hesLower
    linarith [hDExpand]
  have hLogDLe : Real.log D ≤ Real.log s := Real.log_le_log hD hDLe
  have hLogE : Real.log e = 1 := Real.log_exp 1
  have hDFormula : D = s - 1 - Real.log s := by
    rw [hDExpand, Real.log_mul he.ne' hs.ne', hLogE]
    ring
  have hLogDelta : Real.log δ = s - Real.log D :=
    Real.log_div hu.ne' hD.ne'
  have hLogBase : Real.log (e / δ) ≤ -D := by
    rw [Real.log_div he.ne' hδ.ne', hLogE, hLogDelta]
    linarith [hDFormula, hLogDLe]

  -- Multiplication uses δ > 0, and cancellation uses the explicit D > 0.
  have hCancel : δ * D = u := div_mul_cancel₀ u hD.ne'
  have hTilt : δ * Real.log (e / δ) ≤ -u := by
    calc
      δ * Real.log (e / δ) ≤ δ * (-D) :=
        mul_le_mul_of_nonneg_left hLogBase hδ.le
      _ = -(δ * D) := by ring
      _ = -u := by rw [hCancel]

  -- Mathlib already supplies the real-power/log equivalence for positive bases.
  apply (Real.rpow_le_iff_le_log (div_pos he hδ) (div_pos zero_lt_one ht)).2
  calc
    δ * Real.log (e / δ) ≤ -u := hTilt
    _ = Real.log (1 / t) := by
      change -Real.log t = Real.log (1 / t)
      rw [one_div, Real.log_inv]

/-- Within the original closed domain, positivity excludes exactly the internal singular input; both sides of that input remain included. -/
theorem denominator_pos_iff_ne_singularity (t : ℝ)
    (OriginalRange : Real.exp (Real.exp (1 / Real.exp 1)) ≤ t) :
    (0 < Real.log (Real.log t / (Real.exp 1 * Real.log (Real.log t)))) ↔
      t ≠ Real.exp (Real.exp 1) := by
  constructor
  · intro hD hEq
    have hZero :
        Real.log (Real.log t / (Real.exp 1 * Real.log (Real.log t))) = 0 := by
      rw [hEq]
      simp only [Real.log_exp, mul_one, div_self (Real.exp_pos 1).ne', Real.log_one]
    exact (lt_irrefl (0 : ℝ)) (hZero ▸ hD)
  · intro hNe
    let e : ℝ := Real.exp 1
    let u : ℝ := Real.log t
    let s : ℝ := Real.log u
    have he : 0 < e := Real.exp_pos 1
    have ht : 0 < t :=
      (Real.exp_pos (Real.exp (1 / e))).trans_le OriginalRange
    have huLower : Real.exp (1 / e) ≤ u :=
      (Real.le_log_iff_exp_le ht).2 OriginalRange
    have hu : 0 < u := (Real.exp_pos (1 / e)).trans_le huLower
    have hsLower : 1 / e ≤ s :=
      (Real.le_log_iff_exp_le hu).2 huLower
    have hs : 0 < s := (div_pos zero_lt_one he).trans_le hsLower
    have hsNe : s ≠ 1 := by
      intro hsEq
      have huEq : u = Real.exp 1 := by
        calc
          u = Real.exp s := (Real.exp_log hu).symm
          _ = Real.exp 1 := congrArg Real.exp hsEq
      apply hNe
      calc
        t = Real.exp u := (Real.exp_log ht).symm
        _ = Real.exp (Real.exp 1) := congrArg Real.exp huEq
    have hStrict : Real.log s < s - 1 := Real.log_lt_sub_one_of_pos hs hsNe
    have hLogE : Real.log e = 1 := Real.log_exp 1
    change 0 < Real.log (u / (e * s))
    rw [Real.log_div hu.ne' (mul_pos he hs).ne', Real.log_mul he.ne' hs.ne', hLogE]
    change 0 < s - (1 + Real.log s)
    linarith

/-- The undefined point is inside the source domain, not an excluded endpoint. -/
theorem singularity_mem_original_domain :
    Real.exp (Real.exp (1 / Real.exp 1)) ≤ Real.exp (Real.exp 1) := by
  apply Real.exp_le_exp.mpr
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  simpa only [one_mul] using Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)

/-- The displayed denominator vanishes at the internal singular point. -/
theorem logDenominator_at_singularity : logDenominator (Real.exp (Real.exp 1)) = 0 := by
  simp only [logDenominator, Real.log_exp, mul_one,
    div_self (Real.exp_pos 1).ne', Real.log_one]

/-- Lean total division assigns zero to the undefined displayed quotient. -/
theorem displayedThreshold_at_singularity : displayedThreshold (Real.exp (Real.exp 1)) = 0 := by
  simp only [displayedThreshold, logDenominator_at_singularity, div_zero]

/-- The explicitly chosen replacement e squared satisfies the required scalar bound. -/
theorem replacement_at_singularity :
    (Real.exp 1 / (Real.exp 1) ^ (2 : ℕ)) ^ ((Real.exp 1) ^ (2 : ℕ)) ≤
      1 / Real.exp (Real.exp 1) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he_one : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have he_square : 0 < (Real.exp 1) ^ (2 : ℕ) := pow_pos he _
  apply (Real.rpow_le_iff_le_log (div_pos he he_square)
    (div_pos (by norm_num) (Real.exp_pos _))).mpr
  rw [Real.log_div he.ne' he_square.ne', Real.log_pow, Real.log_exp,
    one_div, Real.log_inv, Real.log_exp]
  norm_num

/-- The displayed threshold with the single undefined input exp(e) replaced by e squared. This is an explicit correction, not a continuous extension claimed by the source. -/
def repairedThreshold (t : ℝ) : ℝ :=
  if t = Real.exp (Real.exp 1) then (Real.exp 1) ^ (2 : ℕ) else displayedThreshold t

/-- Away from the singular input, retain the exact displayed expression. -/
theorem repairedThreshold_agrees (t : ℝ) (h : t ≠ Real.exp (Real.exp 1)) :
    repairedThreshold t = displayedThreshold t := by
  simp only [repairedThreshold, if_neg h]

/-- The explicitly corrected scalar bound on the entire original closed domain. -/
theorem repairedThreshold_bound (t : ℝ)
    (OriginalRange : Real.exp (Real.exp (1 / Real.exp 1)) ≤ t) :
    (Real.exp 1 / repairedThreshold t) ^ repairedThreshold t ≤ 1 / t := by
  by_cases h : t = Real.exp (Real.exp 1)
  · subst t
    simpa [repairedThreshold] using replacement_at_singularity
  · have hD := (denominator_pos_iff_ne_singularity t OriginalRange).mpr h
    simpa only [repairedThreshold, if_neg h, displayedThreshold, logDenominator] using
      displayedThreshold_bound_of_denominator_pos t OriginalRange hD

/-- The corrected threshold is positive throughout the original domain. -/
theorem repairedThreshold_positive (t : ℝ)
    (OriginalRange : Real.exp (Real.exp (1 / Real.exp 1)) ≤ t) :
    0 < repairedThreshold t := by
  by_cases h : t = Real.exp (Real.exp 1)
  · simp only [repairedThreshold, if_pos h]
    exact pow_pos (Real.exp_pos 1) _
  · have ht : 0 < t := (Real.exp_pos _).trans_le OriginalRange
    have hu : 0 < Real.log t :=
      (Real.exp_pos _).trans_le ((Real.le_log_iff_exp_le ht).mpr OriginalRange)
    have hD := (denominator_pos_iff_ne_singularity t OriginalRange).mpr h
    simp only [repairedThreshold, if_neg h, displayedThreshold]
    exact div_pos hu hD

/-- The corrected threshold lies strictly beyond e throughout the original domain. -/
theorem repairedThreshold_gt_exp_one (t : ℝ)
    (OriginalRange : Real.exp (Real.exp (1 / Real.exp 1)) ≤ t) :
    Real.exp 1 < repairedThreshold t := by
  have hδ := repairedThreshold_positive t OriginalRange
  have htOne : 1 < t :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).trans_le OriginalRange
  have ht : 0 < t := zero_lt_one.trans htOne
  have hInverse : 1 / t < (1 : ℝ) := (div_lt_one ht).mpr htOne
  have hBound := repairedThreshold_bound t OriginalRange
  have hRatio : Real.exp 1 / repairedThreshold t < 1 := by
    by_contra h
    have hPower := Real.one_le_rpow (le_of_not_gt h) hδ.le
    linarith
  exact (div_lt_one hδ).mp hRatio

/-- For thresholds beyond e, increasing the threshold decreases the power-tail expression. -/
theorem powerThreshold_antitone {δ k : ℝ}
    (ThresholdBeyondE : Real.exp 1 ≤ δ) (LargerThreshold : δ ≤ k) :
    (Real.exp 1 / k) ^ k ≤ (Real.exp 1 / δ) ^ δ := by
  have hδ : 0 < δ := (Real.exp_pos 1).trans_le ThresholdBeyondE
  have hk : 0 < k := hδ.trans_le LargerThreshold
  have hBase : Real.exp 1 / k ≤ Real.exp 1 / δ :=
    div_le_div_of_nonneg_left (Real.exp_pos 1).le hδ LargerThreshold
  calc
    (Real.exp 1 / k) ^ k ≤ (Real.exp 1 / δ) ^ k :=
      Real.rpow_le_rpow (div_pos (Real.exp_pos 1) hk).le hBase hk.le
    _ ≤ (Real.exp 1 / δ) ^ δ :=
      Real.rpow_le_rpow_of_exponent_ge (div_pos (Real.exp_pos 1) hδ)
        ((div_le_one hδ).mpr ThresholdBeyondE) LargerThreshold

/-- The same bound holds for every real threshold at least the corrected threshold. -/
theorem repairedThreshold_larger_bound (t k : ℝ)
    (OriginalRange : Real.exp (Real.exp (1 / Real.exp 1)) ≤ t)
    (LargerThreshold : repairedThreshold t ≤ k) :
    (Real.exp 1 / k) ^ k ≤ 1 / t :=
  (powerThreshold_antitone (repairedThreshold_gt_exp_one t OriginalRange).le
    LargerThreshold).trans (repairedThreshold_bound t OriginalRange)

end
end ECTheoryLib.Probability.PowerTailThreshold
