import ECTheoryLib.Probability.Processes.ConditionalDrift
import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic

/-! Finite counterexamples separating exponential-tail hypotheses, strictness, and moment direction. See docs/SOURCE_NOTES.md or docs/COVERAGE.md for source relations. -/




open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open scoped unitInterval
noncomputable section
namespace AdditiveTailSourceAudit

def Half : I := ⟨1/2, by norm_num, by norm_num⟩
def Coin : Measure Bool := bernoulliMeasure true false Half
instance : IsProbabilityMeasure Coin := inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure true false Half))

-- One random decision: either hit zero at time one, or remain at one forever.
def Process (t : ℕ) (b : Bool) : ℝ := if t=0 then 1 else if b then 0 else 1

def History : Filtration ℕ (inferInstance : MeasurableSpace Bool) where
  seq t := if t=0 then ⊥ else inferInstance
  mono' := by
    intro i j Before
    by_cases Zero : i=0
    · simp only [Zero]
      exact bot_le
    · have Nonzero : j ≠ 0 := by omega
      simp only [if_neg Zero, if_neg Nonzero, le_refl]
  le' := by intro t; split; exact bot_le; exact le_rfl

theorem AdaptedProcess : Adapted History Process := by
  intro t
  by_cases Zero : t=0
  · subst t
    change @Measurable Bool ℝ ⊥ _ (fun _ => (1 : ℝ))
    exact measurable_const
  · change @Measurable Bool ℝ (if t=0 then ⊥ else inferInstance) _ (Process t)
    rw [if_neg Zero]
    exact measurable_of_countable _

theorem Values (t : ℕ) (b : Bool) : Process t b ∈ ({0,1} : Finset ℝ) := by
  cases b <;> by_cases Zero : t=0 <;> simp [Process, Zero]

theorem Absorbing : ZeroIsAbsorbing Coin Process := by
  intro t
  apply ae_of_all
  intro b Zero
  cases b
  · simp [Process] at Zero
  · norm_num [Process]

theorem Initial (b : Bool) : Process 0 b=1 := rfl

theorem DriftUpper (t : ℕ) : ∀ᵐ b ∂Coin,
    (Coin[fun b => Process t b-Process (t+1) b | History t]) b ≤ (1 : ℝ)/2 := by
  by_cases Zero : t=0
  · subst t
    change ∀ᵐ b ∂Coin, (Coin[fun b => Process 0 b-Process 1 b | ⊥]) b ≤ (1 : ℝ)/2
    rw [condExp_bot]
    have Mean : (∫ b, Process 0 b-Process 1 b ∂Coin)=(1 : ℝ)/2 := by
      unfold Coin
      rw [integral_bernoulliMeasure]
      norm_num [Process, Half]
    rw [Mean]
    exact ae_of_all _ (fun _ => le_rfl)
  · have Difference : (fun b => Process t b-Process (t+1) b)=(fun _ : Bool => (0 : ℝ)) := by
      funext b
      simp only [Process, if_neg Zero, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte, sub_self]
    rw [Difference, condExp_const (History.le t) (0 : ℝ)]
    exact ae_of_all _ (fun _ => by norm_num)

theorem JumpBound (t : ℕ) (b : Bool) : |Process (t+1) b-Process t b| ≤ 1 := by
  cases b <;> by_cases Zero : t=0 <;> norm_num [Process, Zero]

-- The book's integer strict-tail condition admits every positive eta here.
theorem ConditionalJumpTail (t j : ℕ) (η : ℝ) (Positive : 0 < η) :
    ∀ᵐ b ∂Coin,
      (Coin[({b | (j : ℝ) < |Process (t+1) b-Process t b|}).indicator (fun _ => (1 : ℝ)) | History t]) b ≤
        1/(1+η)^j := by
  by_cases Zero : j=0
  · subst j
    let A : Set Bool := {b | (0 : ℝ) < |Process (t+1) b-Process t b|}
    have Bounded : A.indicator (fun _ => (1 : ℝ)) ≤ᵐ[Coin] (fun _ => 1) :=
      ae_of_all _ (fun b => by by_cases In : b ∈ A; rw [Set.indicator_of_mem In]; rw [Set.indicator_of_notMem In]; norm_num)
    have Comparison := condExp_mono (m := History t)
      ((integrable_const (1 : ℝ)).indicator (Set.to_countable A).measurableSet) (integrable_const (1 : ℝ)) Bounded
    rw [condExp_const (History.le t) (1 : ℝ)] at Comparison
    filter_upwards [Comparison] with b Bound
    norm_num only [Nat.cast_zero, pow_zero, div_one]
    exact Bound
  · have OneLe : (1 : ℝ) ≤ j := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero Zero)
    have Empty : {b | (j : ℝ) < |Process (t+1) b-Process t b|}=(∅ : Set Bool) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b TooLarge
      exact (not_lt_of_ge (le_trans (JumpBound t b) OneLe)) TooLarge
    rw [Empty, Set.indicator_empty, condExp_const (History.le t) (0 : ℝ)]
    exact ae_of_all _ (fun _ => div_nonneg zero_le_one (pow_nonneg (by linarith) j))

theorem HitByOne : Coin.real {b | ZeroHittingTime Process b ≤ (1 : WithTop ℕ)}=(1 : ℝ)/2 := by
  have Event : {b | ZeroHittingTime Process b ≤ (1 : WithTop ℕ)}=({true} : Set Bool) := by
    ext b
    change (ZeroHittingTime Process b ≤ (1 : WithTop ℕ)) ↔ b=true
    rw [show ZeroHittingTime Process b ≤ (1 : WithTop ℕ) ↔ ∃ s ≤ 1, Process s b=0 from
      FirstHittingTimeLeIff (fun x : ℝ => x=0) (fun s => Process s b) 1]
    cases b
    · simp [Process]
    · constructor
      · intro _; rfl
      · intro _; exact ⟨1, le_rfl, by norm_num [Process]⟩
  rw [Event]
  unfold Coin
  rw [bernoulliMeasure_real_apply_of_mem_of_notMem Half (by simp) (by simp) (by decide)]
  rfl

-- s0=1, delta=1/2, x=1/2 give threshold one; eta=32, r=1 give exp(-2).
theorem PrintedLowerTailFails :
    ¬ Coin.real {b | ZeroHittingTime Process b ≤ (1 : WithTop ℕ)} ≤
      Real.exp (-((32 : ℝ)*(1/2)/8)*min 1 (32^2*(1/2)*(1/2)/(32*1*1))) := by
  rw [HitByOne]
  have Exponent : -((32 : ℝ)*(1/2)/8)*min 1 (32^2*(1/2)*(1/2)/(32*1*1)) = -2 := by norm_num
  rw [Exponent]
  have ExpLower : (2 : ℝ) < Real.exp 2 := by
    have Lower := Real.add_one_le_exp (2 : ℝ)
    linarith
  have Bound : Real.exp (-2 : ℝ) < (1 : ℝ)/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) ExpLower
  exact not_le.mpr Bound

end AdditiveTailSourceAudit

namespace GeneralTailSourceAudit

def Process (t : ℕ) (_b : Bool) : ℝ := if t=0 then 1 else 0
def History : Filtration ℕ (inferInstance : MeasurableSpace Bool) := ⊥

theorem AdaptedProcess : Adapted History Process := fun _ => measurable_const

theorem Values (t : ℕ) (b : Bool) : Process t b ∈ ({0,1} : Finset ℝ) := by
  by_cases Zero : t=0
  · simp only [Process, if_pos Zero, Finset.mem_insert, Finset.mem_singleton, or_true]
  · simp only [Process, if_neg Zero, Finset.mem_insert, Finset.mem_singleton, true_or]

theorem Absorbing : ZeroIsAbsorbing AdditiveTailSourceAudit.Coin Process := by
  intro t
  exact ae_of_all _ (fun _ _ => by simp [Process])

-- With a=0, g=id, lambda=1, beta=1, the printed >= premise holds everywhere.
theorem PrintedLowerMomentCondition (t : ℕ) : ∀ᵐ b ∂AdditiveTailSourceAudit.Coin,
    (1 : ℝ) ≤
      (AdditiveTailSourceAudit.Coin[fun b => Real.exp (Process t b-Process (t+1) b) | History t]) b := by
  have Constant : (fun b => Real.exp (Process t b-Process (t+1) b))=
      (fun _ : Bool => Real.exp (if t=0 then 1 else 0)) := by
    funext b
    simp only [Process, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, sub_zero]
  rw [Constant, condExp_const (History.le t)]
  apply ae_of_all
  intro _
  apply Real.one_le_exp_iff.mpr
  split
  · exact zero_le_one
  · exact le_rfl

theorem HitBeforeTwo :
    AdditiveTailSourceAudit.Coin.real {b | ZeroHittingTime Process b < (2 : WithTop ℕ)}=1 := by
  have Event : {b | ZeroHittingTime Process b < (2 : WithTop ℕ)}=Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    have ByOne : ZeroHittingTime Process b ≤ (1 : WithTop ℕ) :=
      (FirstHittingTimeLeIff (fun x : ℝ => x=0) (fun s => Process s b) 1).mpr
        ⟨1, le_rfl, by norm_num [Process]⟩
    exact lt_of_le_of_lt ByOne (by norm_num)
  rw [Event, measureReal_def, measure_univ, ENNReal.toReal_one]

theorem PrintedLowerTailFails :
    ¬ AdditiveTailSourceAudit.Coin.real {b | ZeroHittingTime Process b < (2 : WithTop ℕ)} ≤
      (∏ _r ∈ Finset.range 2, (1 : ℝ))*Real.exp (-(1 : ℝ)) := by
  rw [HitBeforeTwo]
  simp only [Finset.prod_const_one, one_mul]
  exact not_le.mpr (Real.exp_lt_one_iff.mpr (by norm_num))

-- The weak g(s)>=g(a) requirement also invalidates the strict sign in part (a).
theorem FlatPotentialMomentCondition (t : ℕ) : ∀ᵐ b ∂AdditiveTailSourceAudit.Coin,
    (AdditiveTailSourceAudit.Coin[fun _ : Bool => Real.exp (-((0 : ℝ)-0)) | History t]) b ≤ 1 := by
  rw [condExp_const (History.le t)]
  exact ae_of_all _ (fun _ => by norm_num)

theorem PrintedStrictUpperTailFails :
    ¬ AdditiveTailSourceAudit.Coin.real {b | (1 : WithTop ℕ) <
      ZeroHittingTime (fun _t (_b : Bool) => (1 : ℝ)) b} <
        (∏ _r ∈ Finset.range 1, (1 : ℝ))*Real.exp ((0 : ℝ)-0) := by
  have NeverHit (b : Bool) : ZeroHittingTime (fun _t (_b : Bool) => (1 : ℝ)) b=⊤ :=
    (FirstHittingTimeEqTopIff (fun s : ℝ => s=0) (fun _ => (1 : ℝ))).mpr (fun _ => one_ne_zero)
  have Event : {b | (1 : WithTop ℕ) < ZeroHittingTime (fun _t (_b : Bool) => (1 : ℝ)) b}=Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    change (1 : WithTop ℕ) < ZeroHittingTime (fun _t (_b : Bool) => (1 : ℝ)) b
    rw [NeverHit]
    exact WithTop.coe_lt_top 1
  rw [Event, measureReal_def, measure_univ, ENNReal.toReal_one]
  norm_num

end GeneralTailSourceAudit
end
