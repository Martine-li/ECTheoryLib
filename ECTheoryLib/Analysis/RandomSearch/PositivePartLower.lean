import ECTheoryLib.Tools.Runtime.Multiplicative.PositivePartLower
import ECTheoryLib.Analysis.RandomSearch.CountableExactRuntime

/-! A genuine three-state independent random search with positive rebounds
and goal restarts. The actual samples have probabilities1/16,1/16,14/16. -/
namespace ECTheoryLib.Analysis.RandomSearch.Rebounds
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

def Samples : PMF (Fin 3) :=
  PMF.ofFintype (fun s => if s.val = 0 then (1/16 : ENNReal)
    else if s.val = 1 then 1/16 else 14/16) (by
      norm_num [Fin.sum_univ_succ]
      rw [← one_div (16 : ENNReal), ← ENNReal.add_div, ← ENNReal.add_div]
      simpa only [show (1 : ENNReal)+14 = 15 by norm_num,
        show (1 : ENNReal)+15 = 16 by norm_num] using
        (ENNReal.div_self (a := (16 : ENNReal)) (by norm_num) (by norm_num)))

def Step : Transition (Fin 3) := IndependentRandomSearchStep Samples

def ExpectedRuntime (Initial : PMF (Fin 3)) : ENNReal :=
  ExpectedHittingTime Step (fun s => s.val = 0) Initial

theorem StepProbability (s y : Fin 3) :
    Step s y = if y.val = 0 then (1/16 : ENNReal) else if y.val = 1 then 1/16 else 14/16 := by
  simp [Step, IndependentRandomSearchStep, Samples, PMF.ofFintype_apply]

theorem SamplesIntegral (f : Fin 3 → ℝ) :
    (∫ y, f y ∂Samples.toMeasure) = (f 0+f 1+14*f 2)/16 := by
  rw [PMF.integral_eq_sum]
  norm_num [Samples, PMF.ofFintype_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem SamplesEventProbability (A : Set (Fin 3)) :
    Samples.toMeasure.real A = ((A.indicator (fun _ => (1 : ℝ))) 0+
      (A.indicator (fun _ => (1 : ℝ))) 1+14*(A.indicator (fun _ => (1 : ℝ))) 2)/16 := by
  classical
  have Formula := SamplesIntegral (A.indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const _ (Set.to_countable _).measurableSet, smul_eq_mul, mul_one] at Formula
  exact Formula

private theorem Values (s : Fin 3) : (s.val : ℝ) ∈ ({0,1,2} : Finset ℝ) := by
  fin_cases s <;> norm_num

private theorem Lower : ∀ s ∈ ({0,1,2} : Finset ℝ), s = 0 ∨ 1 ≤ s := by
  intro s Member
  simp only [Finset.mem_insert, Finset.mem_singleton] at Member
  rcases Member with rfl | rfl | rfl <;> norm_num

/-- The actual law satisfies every reference-level bound, not just its
diagonal, and is independent of the previous search state. -/
theorem ReferenceMean (r : ℝ) (InS : r ∈ ({0,1,2} : Finset ℝ)) :
    (∫ y, max (r-(y.val : ℝ)) 0 ∂Samples.toMeasure) ≤ r/2 := by
  rw [SamplesIntegral]
  simp only [Finset.mem_insert, Finset.mem_singleton] at InS
  rcases InS with rfl | rfl | rfl <;> norm_num

theorem LocalPositivePartDrift (s : Fin 3) :
    (∫ y, max ((s.val : ℝ)-(y.val : ℝ)) 0 ∂(Step s).toMeasure) ≤ (s.val : ℝ)/2 :=
  ReferenceMean (s.val : ℝ) (Values s)

theorem LocalHalfJumpProbability (s : Fin 3) (Nonzero : s.val ≠ 0) :
    (Step s).toMeasure.real {y | (1/2 : ℝ)*(s.val : ℝ) ≤ (s.val : ℝ)-(y.val : ℝ)} ≤
      (1/4 : ℝ)/(1+Real.log (s.val : ℝ)) := by
  change Samples.toMeasure.real {y | (1/2 : ℝ)*(s.val : ℝ) ≤ (s.val : ℝ)-(y.val : ℝ)} ≤ _
  rw [SamplesEventProbability]
  fin_cases s
  · norm_num at Nonzero
  · norm_num [Set.indicator_apply]
  · norm_num [Set.indicator_apply]
    have NonnegativeLog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have UpperLog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    apply (le_div_iff₀ (by linarith : 0 < 1+Real.log 2)).mpr
    nlinarith

/-- Every source reference level is verified on the full original history.
The future sample law is the actual constant random-search kernel. -/
theorem ReferenceOnPaths (Initial : PMF (Fin 3)) (t : ℕ) (r : ℝ)
    (InS : r ∈ ({0,1,2} : Finset ℝ)) :
    ∀ᵐ Path ∂PathMeasure Step Initial,
      ((PathMeasure Step Initial)[fun P => max (r-((P (t+1)).val : ℝ)) 0 |
        Filtration.piLE (X := fun _ : ℕ => Fin 3) t]) Path ≤ r/2 := by
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → Fin 3) → ℝ := fun j Path => (Path j).val
  have AdaptedX : Adapted (Filtration.piLE (X := fun _ : ℕ => Fin 3)) X :=
    CountablePathPotentialAdapted (fun s : Fin 3 => (s.val : ℝ))
  have ObservationIntegrable : Integrable (fun Path => max (r-X (t+1) Path) 0) μ :=
    FiniteStateCompositionIntegrable μ (X (t+1)) {0,1,2} (fun s => max (r-s) 0)
      (show Measurable (X (t+1)) from AdaptedX.measurable) (fun Path => Values (Path (t+1)))
  have Conditional := PathMeasureStateConditionalExpectationOfIntegrable Step Initial t
    (fun (_x y : Fin 3) => max (r-(y.val : ℝ)) 0) ObservationIntegrable
  filter_upwards [Conditional] with Path Equal
  rw [Equal]
  exact ReferenceMean r InS

theorem HalfJumpOnPaths (Initial : PMF (Fin 3)) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure Step Initial, (Path t).val ≠ 0 →
      ((PathMeasure Step Initial)[(RelativeDecreaseEvent
        (fun j P => ((P j).val : ℝ)) (1/2) t).indicator (fun _ => (1 : ℝ)) |
        Filtration.piLE (X := fun _ : ℕ => Fin 3) t]) Path ≤
          (1/4 : ℝ)/(1+Real.log ((Path t).val : ℝ)) := by
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → Fin 3) → ℝ := fun j Path => (Path j).val
  have AdaptedX : Adapted (Filtration.piLE (X := fun _ : ℕ => Fin 3)) X :=
    CountablePathPotentialAdapted (fun s : Fin 3 => (s.val : ℝ))
  let f := fun (x y : Fin 3) => if (1/2 : ℝ)*(x.val : ℝ) ≤ (x.val : ℝ)-(y.val : ℝ)
    then (1 : ℝ) else 0
  have Formula : (RelativeDecreaseEvent X (1/2) t).indicator (fun _ => (1 : ℝ)) =
      (fun Path => f (Path t) (Path (t+1))) := by
    funext Path
    simp [RelativeDecreaseEvent, Set.indicator_apply, f, X]
  have ObservationIntegrable : Integrable (fun Path => f (Path t) (Path (t+1))) μ := by
    rw [← Formula]
    exact (integrable_const 1).indicator
      (RelativeDecreaseEventMeasurable X (1/2) t (fun _ => AdaptedX.measurable))
  have Conditional := PathMeasureStateConditionalExpectationOfIntegrable Step Initial t f ObservationIntegrable
  rw [Formula]
  filter_upwards [Conditional] with Path Equal
  intro Active
  rw [Equal]
  have Integral : (∫ y, f (Path t) y ∂(Step (Path t)).toMeasure) =
      (Step (Path t)).toMeasure.real {y | (1/2 : ℝ)*((Path t).val : ℝ) ≤
        ((Path t).val : ℝ)-(y.val : ℝ)} := by
    change (∫ y, ({y | (1/2 : ℝ)*((Path t).val : ℝ) ≤ ((Path t).val : ℝ)-(y.val : ℝ)}).indicator
      (fun _ => (1 : ℝ)) y ∂(Step (Path t)).toMeasure) = _
    rw [integral_indicator_const _ (Set.to_countable _).measurableSet, smul_eq_mul, mul_one]
  rw [Integral]
  exact LocalHalfJumpProbability (Path t) Active

/-- A substantive actual client of the source reference-level corollary.
Both positive rebounds and restarts after zero remain in the original law. -/
theorem RuntimeLower (Initial : PMF (Fin 3)) :
    ENNReal.ofReal ((2/3 : ℝ)*(∫ s, MultiplicativeDriftPotential 1 1 (s.val : ℝ)
      ∂Initial.toMeasure)) ≤ ExpectedRuntime Initial := by
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → Fin 3) → ℝ := fun t Path => (Path t).val
  have AdaptedX : Adapted (Filtration.piLE (X := fun _ : ℕ => Fin 3)) X :=
    CountablePathPotentialAdapted (fun s : Fin 3 => (s.val : ℝ))
  have Bound := MultiplicativeDriftLowerBoundOfReferenceLevels μ X
    (Filtration.piLE (X := fun _ : ℕ => Fin 3)) AdaptedX {0,1,2} 1 (1/2) (1/2)
    (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Lower
    (fun _ Path => Values (Path _)) (by
      intro t r InS _
      filter_upwards [ReferenceOnPaths Initial t r InS] with Path Bound
      intro _ _
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using Bound) (by
      intro t
      filter_upwards [HalfJumpOnPaths Initial t] with Path Bound
      intro Active
      change ((Path t).val : ℝ) ≠ 0 at Active
      have NatNonzero : (Path t).val ≠ 0 := Nat.cast_ne_zero.mp Active
      simpa only [div_one, show (1/2 : ℝ)*(1/2) = 1/4 by norm_num] using Bound NatNonzero)
  unfold ExpectedRuntime
  rw [ExpectedHittingTimeEqExpectedZero Step Initial (fun s : Fin 3 => (s.val : ℝ))
    (fun s => s.val = 0) (fun _ => by simp)]
  unfold ExpectedValue at Bound
  rw [PathMeasureInitialIntegral Step Initial (fun s : Fin 3 =>
    MultiplicativeDriftPotential 1 1 (s.val : ℝ))] at Bound
  have Coefficient (m : ℝ) : (((1 : ℝ)-1/2)/(1+1/2))*(m/(1/2)) = (2/3)*m := by ring
  simpa only [Coefficient] using Bound

theorem SuccessProbability : Samples.toMeasure.real {s | s.val = 0} = (1/16 : ℝ) := by
  rw [SamplesEventProbability]
  have ZeroMember : (0 : Fin 3) ∈ {s : Fin 3 | s.val = 0} := by decide
  have OneOutside : (1 : Fin 3) ∉ {s : Fin 3 | s.val = 0} := by decide
  have TwoOutside : (2 : Fin 3) ∉ {s : Fin 3 | s.val = 0} := by decide
  simp only [Set.indicator_of_mem ZeroMember, Set.indicator_of_notMem OneOutside,
    Set.indicator_of_notMem TwoOutside]
  norm_num

/-- The existing exact random-search analysis independently gives mean16
from either positive state, on this same kernel and first-hit convention. -/
theorem FixedPositiveRuntimeExact (s : Fin 3) (Nonzero : s.val ≠ 0) :
    ExpectedRuntime (PMF.pure s) = 16 := by
  have Equal := RandomSearch.CountableFixedRuntimeExact Samples (fun y : Fin 3 => y.val = 0)
    s Nonzero (by rw [SuccessProbability]; norm_num)
  rw [SuccessProbability] at Equal
  have Constant : ENNReal.ofReal (1/(1/16 : ℝ)) = (16 : ENNReal) := by norm_num
  rw [Constant] at Equal
  exact Equal

theorem AtGoalRuntime : ExpectedRuntime (PMF.pure (0 : Fin 3)) = 0 :=
  ExpectedHittingTimeOfPureTarget Step (fun s => s.val = 0) 0 (by norm_num)

theorem UpwardProbability : (Step 1).toMeasure.real {y | 1 < y.val} = (14/16 : ℝ) := by
  change Samples.toMeasure.real {y | 1 < y.val} = _
  rw [SamplesEventProbability]
  norm_num [Set.indicator_apply]

theorem GoalRestartProbability : (Step 0).toMeasure.real {y | 0 < y.val} = (15/16 : ℝ) := by
  change Samples.toMeasure.real {y | 0 < y.val} = _
  rw [SamplesEventProbability]
  have ZeroOutside : (0 : Fin 3) ∉ {s : Fin 3 | 0 < s.val} := by decide
  have OneMember : (1 : Fin 3) ∈ {s : Fin 3 | 0 < s.val} := by decide
  have TwoMember : (2 : Fin 3) ∈ {s : Fin 3 | 0 < s.val} := by decide
  simp only [Set.indicator_of_notMem ZeroOutside, Set.indicator_of_mem OneMember,
    Set.indicator_of_mem TwoMember]
  norm_num

end
end ECTheoryLib.Analysis.RandomSearch.Rebounds

