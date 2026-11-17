import ECTheoryLib.Probability.HittingTimes.StoppedHitting
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# First-hitting upper barriers for nonnegative supermartingales

Reuse Mathlib optional stopping and Markov; no finite range or jump bound.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Optional stopping is reused from Mathlib, through negation. -/
theorem SupermartingaleStoppedAtFirstHit (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (Super : Supermartingale X F μ) (Goal : ℝ → Prop)
    (MeasurableGoal : MeasurableSet {x | Goal x}) :
    Supermartingale (StopAtFirstHit Goal X) F μ := by
  have Stop := Super.stronglyAdapted.adapted.isStoppingTime_hittingAfter
    (n := 0) MeasurableGoal
  have Neg := (Super.neg.stoppedProcess Stop).neg
  have Equal : -stoppedProcess (-X) (hittingAfter X {x | Goal x} 0) =
      stoppedProcess X (hittingAfter X {x | Goal x} 0) := by
    funext t ω
    exact neg_neg _
  rw [Equal] at Neg
  change Supermartingale (stoppedProcess X (hittingAfter X {x | Goal x} 0)) F μ
  exact Neg

/-- A nonnegative supermartingale hits an upper barrier by time t with
probability at most its initial mean divided by the barrier. No finite range,
bounded jumps, absorption or finite hitting expectation is assumed. -/
theorem NonnegativeSupermartingaleHittingBound (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (Super : Supermartingale X F μ)
    (Nonnegative : ∀ t, ∀ᵐ ω ∂μ, 0≤X t ω) (a : ℝ) (Positive : 0<a) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => a≤s) (fun j => X j ω)≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂μ)/a) := by
  let Y := StopAtFirstHit (fun s : ℝ => a≤s) X
  have SuperY : Supermartingale Y F μ :=
    SupermartingaleStoppedAtFirstHit μ X F Super _ measurableSet_Ici
  have NonnegativeY : ∀ᵐ ω ∂μ, 0≤Y t ω := by
    filter_upwards [ae_all_iff.mpr Nonnegative] with ω All
    exact All _
  have Mean : (∫ ω, Y t ω ∂μ)≤∫ ω, X 0 ω ∂μ := by
    have Bound := SuperY.setIntegral_le (Nat.zero_le t) MeasurableSet.univ
    simpa only [setIntegral_univ,Y,StopAtFirstHitInitial] using Bound
  have Scaled : Integrable (fun ω => Y t ω/a) μ := (SuperY.integrable t).div_const a
  have Markov : μ {ω | a≤Y t ω}≤ENNReal.ofReal ((∫ ω, Y t ω ∂μ)/a) := by
    have Bound := Scaled.measure_le_integral (s := {ω | a≤Y t ω})
      (NonnegativeY.mono (fun _ h => div_nonneg h Positive.le))
      (fun ω h => (le_div_iff₀ Positive).mpr (by simpa using h))
    simpa only [integral_div] using Bound
  have Events : {ω | FirstHittingTime (fun s : ℝ => a≤s) (fun j => X j ω)≤(t : WithTop ℕ)} =
      {ω | a≤Y t ω} := by
    ext ω
    exact (StopAtFirstHitGoalIff _ X t ω).symm
  rw [Events]
  exact Markov.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right Mean Positive.le))

end
end ECTheoryLib.Probability
