import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.HasLaw

/-!
# Bounded differences for independent coordinates

Doerr Theorem1.10.27: pointwise coordinate widths give both closed tails about
the actual expectation, with exponent -2*d^2/sum(c_i^2). Coordinates may have
arbitrary measurable spaces and need not have identical laws. The proof derives
integrability from bounded oscillation, reuses Mathlib Hoeffding and Fubini,
and transports the exact product-law MGF to the actual independent variables.

No StandardBorel hypothesis is needed. Nonnegative widths and an empty family
are allowed; total real division gives the weak bound1 at zero total width.
Future-coordinate average conditions from Theorem1.10.28 are a separate result.
-/


namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
noncomputable section

private theorem coordinateOscillationLeSum {ι : Type*} [Fintype ι]
    {A : ι → Type*} (f : (∀ i, A i) → ℝ) (c : ι → ℝ≥0)
    (Coordinate : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (c i : ℝ))
    (x y : ∀ i, A i) : |f x - f y| ≤ ∑ i, (c i : ℝ) := by
  classical
  let mixed (s : Finset ι) : ∀ i, A i := fun i => if i ∈ s then x i else y i
  have Bound (s : Finset ι) : |f (mixed s) - f y| ≤ ∑ i ∈ s, (c i : ℝ) := by
    induction s using Finset.induction with
    | empty => simp only [mixed, Finset.notMem_empty, if_false, sub_self, abs_zero,
        Finset.sum_empty, le_refl]
    | @insert i s Outside Induction =>
      have Step : |f (mixed (insert i s)) - f (mixed s)| ≤ (c i : ℝ) := by
        apply Coordinate i
        intro j Different
        simp only [mixed, Finset.mem_insert, Different, false_or]
      calc
        |f (mixed (insert i s)) - f y| ≤
            |f (mixed (insert i s)) - f (mixed s)| + |f (mixed s) - f y| :=
          abs_sub_le _ _ _
        _ ≤ (c i : ℝ) + ∑ j ∈ s, (c j : ℝ) := add_le_add Step Induction
        _ = ∑ j ∈ insert i s, (c j : ℝ) := by rw [Finset.sum_insert Outside]
  simpa only [mixed, Finset.mem_univ, if_true] using Bound Finset.univ

/-- A pointwise oscillation bound gives Hoeffding's exact width parameter. -/
theorem SubGaussianOfOscillation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (c : ℝ≥0)
    (Observable : AEMeasurable X P)
    (Oscillation : ∀ x y, |X x - X y| ≤ (c : ℝ)) :
    HasSubgaussianMGF (fun x => X x - ∫ y, X y ∂P) (c ^ 2 / 4) P := by
  classical
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
  have BoundedBelow : BddBelow (Set.range X) := by
    refine ⟨X x₀ - c, ?_⟩
    rintro _ ⟨y, rfl⟩
    have Bound := (abs_le.mp (Oscillation x₀ y)).2
    linarith
  let a : ℝ := sInf (Set.range X)
  have InInterval (x : Ω) : X x ∈ Icc a (a + c) := by
    refine ⟨csInf_le BoundedBelow ⟨x, rfl⟩, ?_⟩
    have Lower : X x - c ≤ a := by
      apply le_csInf (s := Set.range X) ⟨X x₀, ⟨x₀, rfl⟩⟩
      rintro _ ⟨y, rfl⟩
      have Bound := (abs_le.mp (Oscillation x y)).2
      linarith
    linarith
  have Parameter : ((‖(a + (c : ℝ)) - a‖₊ / 2) ^ 2 : ℝ≥0) = c ^ 2 / 4 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg c.coe_nonneg]
    ring
  have Bound := hasSubgaussianMGF_of_mem_Icc Observable (Filter.Eventually.of_forall InInterval)
  rw [Parameter] at Bound
  exact Bound

end
end ECTheoryLib.Probability




namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

private theorem subGaussianProdOfSections {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) (Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : A × B → ℝ) (a b : ℝ≥0)
    (FiniteMean : Integrable f (P.prod Q))
    (FiniteExp : ∀ t : ℝ, Integrable
      (fun z => Real.exp (t * (f z - ∫ w, f w ∂P.prod Q))) (P.prod Q))
    (Sections : ∀ y, HasSubgaussianMGF
      (fun x => f (x, y) - ∫ w, f (w, y) ∂P) a P)
    (Average : HasSubgaussianMGF
      (fun y => (∫ x, f (x, y) ∂P) - ∫ v, ∫ x, f (x, v) ∂P ∂Q) b Q) :
    HasSubgaussianMGF (fun z => f z - ∫ w, f w ∂P.prod Q) (a + b) (P.prod Q) := by
  refine ⟨FiniteExp, ?_⟩
  intro t
  let g : B → ℝ := fun y => ∫ x, f (x, y) ∂P
  have Mean : (∫ w, f w ∂P.prod Q) = ∫ y, g y ∂Q :=
    integral_prod_symm f FiniteMean
  have Factor (y : B) :
      (∫ x, Real.exp (t * (f (x, y) - ∫ w, f w ∂P.prod Q)) ∂P) =
        Real.exp (t * (g y - ∫ v, g v ∂Q)) *
          mgf (fun x => f (x, y) - g y) P t := by
    rw [mgf, ← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only
    rw [Mean, ← Real.exp_add]
    congr 1
    ring
  have Majorant : Integrable
      (fun y => Real.exp ((a : ℝ) * t ^ 2 / 2) *
        Real.exp (t * (g y - ∫ v, g v ∂Q))) Q :=
    (Average.integrable_exp_mul t).const_mul _
  calc
    mgf (fun z => f z - ∫ w, f w ∂P.prod Q) (P.prod Q) t =
        ∫ y, Real.exp (t * (g y - ∫ v, g v ∂Q)) *
          mgf (fun x => f (x, y) - g y) P t ∂Q := by
      rw [mgf, integral_prod_symm _ (FiniteExp t)]
      exact integral_congr_ae (Filter.Eventually.of_forall Factor)
    _ ≤ ∫ y, Real.exp ((a : ℝ) * t ^ 2 / 2) *
        Real.exp (t * (g y - ∫ v, g v ∂Q)) ∂Q := by
      apply integral_mono_of_nonneg
      · apply Filter.Eventually.of_forall
        intro y
        exact mul_nonneg (Real.exp_nonneg _) (integral_nonneg (fun _ => Real.exp_nonneg _))
      · exact Majorant
      · apply Filter.Eventually.of_forall
        intro y
        exact (mul_le_mul_of_nonneg_left ((Sections y).mgf_le t)
          (Real.exp_nonneg (t * (g y - ∫ v, g v ∂Q)))).trans_eq (mul_comm _ _)
    _ = Real.exp ((a : ℝ) * t ^ 2 / 2) * mgf (fun y => g y - ∫ v, g v ∂Q) Q t := by
      rw [integral_const_mul]
      rfl
    _ ≤ Real.exp ((a : ℝ) * t ^ 2 / 2) * Real.exp ((b : ℝ) * t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Average.mgf_le t) (Real.exp_nonneg _)
    _ = Real.exp (((a + b : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
      rw [← Real.exp_add, NNReal.coe_add]
      congr 1
      ring

end
end ECTheoryLib.Probability




namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
universe u

private theorem boundedDifferencesProduct (n : ℕ) :
    ∀ (A : Fin n → Type u) [∀ i, MeasurableSpace (A i)]
      (μ : ∀ i, Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)]
      (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0),
      Measurable f →
      (∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (c i : ℝ)) →
      HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Measure.pi μ)
        ((∑ i, c i ^ 2) / 4) (Measure.pi μ) := by
  induction n with
  | zero =>
    intro A _ μ _ f c Observable _
    have Oscillation (x y : ∀ i, A i) : |f x - f y| ≤ (0 : ℝ≥0) := by
      rw [Subsingleton.elim x y]
      simp
    simpa using SubGaussianOfOscillation (Measure.pi μ) f 0 Observable.aemeasurable Oscillation
  | succ n Induction =>
    intro A _ μ _ f c Observable Coordinate
    let i₀ : Fin (n + 1) := 0
    let B : Fin n → Type u := fun j => A (i₀.succAbove j)
    let ν : ∀ j, Measure (B j) := fun j => μ (i₀.succAbove j)
    let Q := Measure.pi ν
    let e := MeasurableEquiv.piFinSuccAbove A i₀
    let F : A i₀ × (∀ j, B j) → ℝ := fun z => f (e.symm z)
    have ObservableF : Measurable F := Observable.comp e.symm.measurable
    have AllOscillation (x y : ∀ i, A i) : |f x - f y| ≤ ((∑ i, c i : ℝ≥0) : ℝ) := by
      simpa only [NNReal.coe_sum] using coordinateOscillationLeSum f c Coordinate x y
    have Rough := SubGaussianOfOscillation ((μ i₀).prod Q) F (∑ i, c i)
      ObservableF.aemeasurable (fun x y => AllOscillation (e.symm x) (e.symm y))
    have FiniteMean : Integrable F ((μ i₀).prod Q) := by
      exact (Rough.integrable.add (integrable_const (∫ z, F z ∂(μ i₀).prod Q))).congr
        (Filter.Eventually.of_forall (fun z => by simp only [Pi.add_apply, sub_add_cancel]))
    have AtFirst (x : A i₀) (y : ∀ j, B j) : e.symm (x, y) i₀ = x := by
      change i₀.insertNth x y i₀ = x
      exact Fin.insertNth_apply_same _ _ _
    have AtRest (x : A i₀) (y : ∀ j, B j) (j : Fin n) :
        e.symm (x, y) (i₀.succAbove j) = y j := by
      change i₀.insertNth x y (i₀.succAbove j) = y j
      exact Fin.insertNth_apply_succAbove _ _ _ _
    have SectionOscillation (y : ∀ j, B j) (x z : A i₀) :
        |F (x, y) - F (z, y)| ≤ (c i₀ : ℝ) := by
      apply Coordinate i₀
      intro j Different
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq Different
      rw [AtRest, AtRest]
    have Sections (y : ∀ j, B j) :
        HasSubgaussianMGF (fun x => F (x, y) - ∫ z, F (z, y) ∂μ i₀)
          (c i₀ ^ 2 / 4) (μ i₀) :=
      SubGaussianOfOscillation (μ i₀) (fun x => F (x, y)) (c i₀)
        (ObservableF.comp (measurable_id.prodMk measurable_const)).aemeasurable
        (SectionOscillation y)
    have FiniteSection (y : ∀ j, B j) : Integrable (fun x => F (x, y)) (μ i₀) := by
      exact ((Sections y).integrable.add (integrable_const (∫ z, F (z, y) ∂μ i₀))).congr
        (Filter.Eventually.of_forall (fun x => by simp only [Pi.add_apply, sub_add_cancel]))
    let g : (∀ j, B j) → ℝ := fun y => ∫ x, F (x, y) ∂μ i₀
    have ObservableG : Measurable g :=
      ObservableF.stronglyMeasurable.integral_prod_left'.measurable
    have CoordinateG (i : Fin n) (y z : ∀ j, B j)
        (Same : ∀ j, j ≠ i → y j = z j) : |g y - g z| ≤ (c (i₀.succAbove i) : ℝ) := by
      have Difference (x : A i₀) : |F (x, y) - F (x, z)| ≤ (c (i₀.succAbove i) : ℝ) := by
        apply Coordinate (i₀.succAbove i)
        intro j Different
        by_cases First : j = i₀
        · subst j
          rw [AtFirst, AtFirst]
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq First
          rw [AtRest, AtRest]
          apply Same k
          intro Equal
          subst k
          exact Different rfl
      dsimp only [g]
      rw [← integral_sub (FiniteSection y) (FiniteSection z)]
      have Bound := norm_integral_le_of_norm_le_const
        (μ := μ i₀) (f := fun x => F (x, y) - F (x, z))
        (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using Difference x))
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using Bound
    have Average := Induction B ν g (fun j => c (i₀.succAbove j)) ObservableG CoordinateG
    have Product := subGaussianProdOfSections (μ i₀) Q F
      (c i₀ ^ 2 / 4) ((∑ j, c (i₀.succAbove j) ^ 2) / 4)
      FiniteMean Rough.integrable_exp_mul Sections Average
    have Split := measurePreserving_piFinSuccAbove μ i₀
    have Mean : (∫ z, F z ∂(μ i₀).prod Q) = ∫ x, f x ∂Measure.pi μ :=
      Split.symm.integral_comp' f
    have Mapped : HasSubgaussianMGF
        (fun z => F z - ∫ w, F w ∂(μ i₀).prod Q)
        (c i₀ ^ 2 / 4 + (∑ j, c (i₀.succAbove j) ^ 2) / 4)
        ((Measure.pi μ).map e) := by
      rw [Split.map_eq]
      exact Product
    have Transfer := HasSubgaussianMGF.of_map e.measurable.aemeasurable Mapped
    have Parameter : c i₀ ^ 2 / 4 + (∑ j, c (i₀.succAbove j) ^ 2) / 4 =
        (∑ i, c i ^ 2) / 4 := by
      rw [Fin.sum_univ_succ]
      simp only [i₀, Fin.zero_succAbove, add_div]
    simpa only [Function.comp_def, F, e.symm_apply_apply, Mean, Parameter] using Transfer

end
end ECTheoryLib.Probability




namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

/-- A coordinate-bounded function of an independent family has the exact width MGF. -/
theorem IndependentBoundedDifferencesSubGaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (X : ∀ i, Ω → A i)
    (ObservableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0) (ObservableF : Measurable f)
    (Coordinate : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (c i : ℝ)) :
    HasSubgaussianMGF
      (fun ω => f (fun i => X i ω) - ∫ w, f (fun i => X i w) ∂P)
      ((∑ i, c i ^ 2) / 4) P := by
  let μ : ∀ i, Measure (A i) := fun i => P.map (X i)
  have Probability (i : Fin n) : IsProbabilityMeasure (μ i) :=
    Measure.isProbabilityMeasure_map (ObservableX i)
  let : ∀ i, IsProbabilityMeasure (μ i) := Probability
  have Joint : HasLaw (fun ω i => X i ω) (Measure.pi μ) P :=
    Independent.hasLaw_pi (fun i => ⟨ObservableX i, rfl⟩)
  have Product := boundedDifferencesProduct n A μ f c ObservableF Coordinate
  have Mapped : HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Measure.pi μ)
      ((∑ i, c i ^ 2) / 4) (P.map (fun ω i => X i ω)) := by
    rw [Joint.map_eq]
    exact Product
  have Transfer := HasSubgaussianMGF.of_map Joint.aemeasurable Mapped
  have Mean := Joint.integral_comp ObservableF.aestronglyMeasurable
  rw [← Mean] at Transfer
  exact Transfer

private theorem quarterVarianceTailExponent (c : ℝ≥0) (d : ℝ) :
    -d ^ 2 / (2 * ((c / 4 : ℝ≥0) : ℝ)) = -2 * d ^ 2 / (c : ℝ) := by
  simp only [NNReal.coe_div, NNReal.coe_ofNat]
  rw [show (2 : ℝ) * ((c : ℝ) / 4) = (c : ℝ) / 2 by ring, div_div_eq_mul_div]
  ring

/-- Theorem1.10.27 upper closed tail, allowing zero widths and an empty family. -/
theorem IndependentBoundedDifferencesUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (X : ∀ i, Ω → A i)
    (ObservableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0) (ObservableF : Measurable f)
    (Coordinate : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (c i : ℝ))
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    P.real {ω | (∫ w, f (fun i => X i w) ∂P) + threshold ≤ f (fun i => X i ω)} ≤
      Real.exp (-2 * threshold ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  have Bound := (IndependentBoundedDifferencesSubGaussian P X ObservableX Independent f c
    ObservableF Coordinate).measure_ge_le Nonnegative
  have Event : {ω | threshold ≤ f (fun i => X i ω) - ∫ w, f (fun i => X i w) ∂P} =
      {ω | (∫ w, f (fun i => X i w) ∂P) + threshold ≤ f (fun i => X i ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  rw [Event, quarterVarianceTailExponent] at Bound
  simpa only [NNReal.coe_sum, NNReal.coe_pow] using Bound

/-- The lower closed tail follows by negating the same centered MGF. -/
theorem IndependentBoundedDifferencesLowerTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (X : ∀ i, Ω → A i)
    (ObservableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0) (ObservableF : Measurable f)
    (Coordinate : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (c i : ℝ))
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    P.real {ω | f (fun i => X i ω) ≤ (∫ w, f (fun i => X i w) ∂P) - threshold} ≤
      Real.exp (-2 * threshold ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  have Bound := (IndependentBoundedDifferencesSubGaussian P X ObservableX Independent f c
    ObservableF Coordinate).neg.measure_ge_le Nonnegative
  have Event : {ω | threshold ≤ -(f (fun i => X i ω) - ∫ w, f (fun i => X i w) ∂P)} =
      {ω | f (fun i => X i ω) ≤ (∫ w, f (fun i => X i w) ∂P) - threshold} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  change P.real {ω | threshold ≤ -(f (fun i => X i ω) - ∫ w, f (fun i => X i w) ∂P)} ≤ _ at Bound
  rw [Event, quarterVarianceTailExponent] at Bound
  simpa only [NNReal.coe_sum, NNReal.coe_pow] using Bound

end
end ECTheoryLib.Probability



/-!
## Bounded conditional expectations (Doerr Theorem 1.10.28)

The following separate result bounds genuine averages over future coordinates
after every deterministic prefix, including null prefixes. It uses the original
independent law, arbitrary measurable coordinate spaces and the actual mean.
The centered MGF parameter is sum(c_i^2)/4; both closed tails have exponent
-2*d^2/sum(c_i^2). Integrability, including every fixed-prefix section, is derived.
Nonnegative widths and empty families extend the source's positive widths;
total division gives the weak bound 1 at zero total width. No StandardBorel,
finite-state or caller integrability hypothesis is imposed. The existing
private product-MGF assembly is reused without changing its proof or visibility.
-/



namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Average the future coordinates after a fixed prefix of length k. -/
def FutureCoordinateMean {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (μ : ∀ i, Measure (A i))
    (f : (∀ i, A i) → ℝ) (k : ℕ) (x : ∀ i, A i) : ℝ :=
  ∫ y, f (fun i => if i.val < k then x i else y i) ∂Measure.pi μ

theorem FutureCoordinateMeanZero {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (μ : ∀ i, Measure (A i))
    (f : (∀ i, A i) → ℝ) (x : ∀ i, A i) :
    FutureCoordinateMean μ f 0 x = ∫ y, f y ∂Measure.pi μ := by
  simp [FutureCoordinateMean]

theorem FutureCoordinateMeanAtEnd {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (μ : ∀ i, Measure (A i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, A i) → ℝ) (x : ∀ i, A i) :
    FutureCoordinateMean μ f n x = f x := by
  simp [FutureCoordinateMean]

theorem FutureCoordinateMeanPrefix {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (μ : ∀ i, Measure (A i))
    (f : (∀ i, A i) → ℝ) (k : ℕ) (x y : ∀ i, A i)
    (SamePrefix : ∀ i, i.val < k → x i = y i) :
    FutureCoordinateMean μ f k x = FutureCoordinateMean μ f k y := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  apply congrArg f
  funext i
  by_cases Before : i.val < k
  · simp only [if_pos Before, SamePrefix i Before]
  · simp only [if_neg Before]

theorem FutureCoordinateMeanMeasurable {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (μ : ∀ i, Measure (A i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, A i) → ℝ) (Observable : Measurable f) (k : ℕ) :
    Measurable (FutureCoordinateMean μ f k) := by
  have Mask : Measurable (fun p : (∀ i, A i) × (∀ i, A i) =>
      f (fun i => if i.val < k then p.1 i else p.2 i)) := by
    apply Observable.comp
    apply measurable_pi_lambda
    intro i
    by_cases Before : i.val < k
    · simp only [if_pos Before]
      exact (measurable_pi_apply i).comp measurable_fst
    · simp only [if_neg Before]
      exact (measurable_pi_apply i).comp measurable_snd
  exact Mask.stronglyMeasurable.integral_prod_right'.measurable

private theorem tailProductLaw {n : ℕ} {A : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (A i)] (μ : ∀ i, Measure (A i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    HasLaw (fun x (i : Fin n) => x i.succ)
      (Measure.pi (fun i : Fin n => μ i.succ)) (Measure.pi μ) := by
  have Independent := (iIndepFun_pi (μ := μ) (fun _ => aemeasurable_id)).precomp
    (g := fun i : Fin n => i.succ) (Fin.succ_injective n)
  exact Independent.hasLaw_pi (fun i => (measurePreserving_eval μ i.succ).hasLaw)

/-- Dropping the fixed head preserves the actual future average, not just an a.e. version. -/
theorem FutureCoordinateMeanCons {n : ℕ} {A : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (A i)] (μ : ∀ i, Measure (A i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, A i) → ℝ) (Observable : Measurable f)
    (a : A 0) (k : ℕ) (x : ∀ i : Fin n, A i.succ) :
    FutureCoordinateMean μ f (k + 1) (Fin.cons a x) =
      FutureCoordinateMean (fun i : Fin n => μ i.succ)
        (fun y => f (Fin.cons a y)) k x := by
  let g : (∀ i : Fin n, A i.succ) → ℝ :=
    fun y => f (Fin.cons a (fun i => if i.val < k then x i else y i))
  have ObservableG : Measurable g := by
    apply Observable.comp
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_const
    · by_cases Before : j.val < k
      · simpa only [Fin.cons_succ, if_pos Before] using
          (measurable_const : Measurable (fun _ : ∀ i : Fin n, A i.succ => x j))
      · simpa only [Fin.cons_succ, if_neg Before] using measurable_pi_apply j
  have Transfer := (tailProductLaw μ).integral_comp ObservableG.aestronglyMeasurable
  change (∫ y, f (fun i => if i.val < k + 1 then (Fin.cons a x) i else y i) ∂Measure.pi μ) =
    ∫ y, g y ∂Measure.pi (fun i : Fin n => μ i.succ)
  rw [← Transfer]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [Function.comp_def, g]
  apply congrArg f
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.val_succ, Nat.add_lt_add_iff_right, Fin.cons_succ]

/-- The product average equals the actual independent future-coordinate integral.
This change of variables alone does not assert integrability of the sections. -/
theorem FutureCoordinateMeanEqIndependentIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (X : ∀ i, Ω → A i)
    (ObservableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (f : (∀ i, A i) → ℝ) (ObservableF : Measurable f)
    (k : ℕ) (x : ∀ i, A i) :
    FutureCoordinateMean (fun i => P.map (X i)) f k x =
      ∫ ω, f (fun i => if i.val < k then x i else X i ω) ∂P := by
  have Joint : HasLaw (fun ω i => X i ω) (Measure.pi (fun i => P.map (X i))) P :=
    Independent.hasLaw_pi (fun i => ⟨ObservableX i, rfl⟩)
  have Mask : Measurable (fun y : ∀ i, A i =>
      f (fun i => if i.val < k then x i else y i)) := by
    apply ObservableF.comp
    apply measurable_pi_lambda
    intro i
    by_cases Before : i.val < k
    · simp only [if_pos Before]
      exact measurable_const
    · simp only [if_neg Before]
      exact measurable_pi_apply i
  exact (Joint.integral_comp Mask.aestronglyMeasurable).symm

end
end ECTheoryLib.Probability





namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

private theorem integrableOfOscillation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (c : ℝ≥0)
    (Observable : AEMeasurable f P)
    (Oscillation : ∀ x y, |f x - f y| ≤ (c : ℝ)) : Integrable f P := by
  have Bound := SubGaussianOfOscillation P f c Observable Oscillation
  exact (Bound.integrable.add (integrable_const (∫ y, f y ∂P))).congr
    (Filter.Eventually.of_forall (fun x => by simp only [Pi.add_apply, sub_add_cancel]))

private theorem distanceFromMeanOfOscillation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (c : ℝ≥0)
    (Observable : AEMeasurable f P)
    (Oscillation : ∀ x y, |f x - f y| ≤ (c : ℝ)) (x : Ω) :
    |f x - ∫ y, f y ∂P| ≤ (c : ℝ) := by
  have FiniteMean := integrableOfOscillation P f c Observable Oscillation
  have Bound := norm_integral_le_of_norm_le_const
    (μ := P) (f := fun y => f x - f y)
    (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs] using Oscillation x y))
  rw [integral_sub (integrable_const (f x)) FiniteMean, integral_const,
    probReal_univ, one_smul] at Bound
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using Bound

end
end ECTheoryLib.Probability




namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
universe u

private theorem boundedConditionalExpectationsProduct (n : ℕ) :
    ∀ (A : Fin n → Type u) [∀ i, MeasurableSpace (A i)]
      (μ : ∀ i, Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)]
      (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0),
      Measurable f →
      (∀ i x y, (∀ j, j.val < i.val → x j = y j) →
        |FutureCoordinateMean μ f (i.val + 1) x -
          FutureCoordinateMean μ f (i.val + 1) y| ≤ (c i : ℝ)) →
      HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Measure.pi μ)
        ((∑ i, c i ^ 2) / 4) (Measure.pi μ) ∧
      (∀ x, |f x - ∫ y, f y ∂Measure.pi μ| ≤ ∑ i, (c i : ℝ)) := by
  induction n with
  | zero =>
    intro A _ μ _ f c Observable _
    have Oscillation (x y : ∀ i, A i) : |f x - f y| ≤ (0 : ℝ≥0) := by
      rw [Subsingleton.elim x y]
      simp
    refine ⟨?_, ?_⟩
    · simpa using SubGaussianOfOscillation (Measure.pi μ) f 0
        Observable.aemeasurable Oscillation
    · intro x
      simpa using distanceFromMeanOfOscillation (Measure.pi μ) f 0
        Observable.aemeasurable Oscillation x
  | succ n Induction =>
    intro A _ μ _ f c Observable Coordinate
    let B : Fin n → Type u := fun j => A j.succ
    let ν : ∀ j, Measure (B j) := fun j => μ j.succ
    let Q := Measure.pi ν
    let F : (∀ j, B j) × A 0 → ℝ := fun z => f (Fin.cons z.2 z.1)
    have ObservableF : Measurable F := by
      apply Observable.comp
      apply measurable_pi_lambda
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_snd
      · exact (measurable_pi_apply j).comp measurable_fst
    have Section (a : A 0) := by
      apply Induction B ν (fun y => f (Fin.cons a y)) (fun j => c j.succ)
      · exact ObservableF.comp (measurable_id.prodMk measurable_const)
      · intro i x y Same
        rw [← FutureCoordinateMeanCons μ f Observable a (i.val + 1) x,
          ← FutureCoordinateMeanCons μ f Observable a (i.val + 1) y]
        apply Coordinate i.succ
        intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · intro _
          rfl
        · intro Before
          exact Same k (by simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using Before)
    let g : A 0 → ℝ := fun a => ∫ y, F (y, a) ∂Q
    have ObservableG : Measurable g :=
      ObservableF.stronglyMeasurable.integral_prod_left'.measurable
    have OscillationG (a b : A 0) : |g a - g b| ≤ (c 0 : ℝ) := by
      obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure Q
      have Bound := Coordinate 0 (Fin.cons a x) (Fin.cons b x)
        (fun j Before => by exact False.elim (Nat.not_lt_zero _ Before))
      simpa only [FutureCoordinateMeanCons μ f Observable,
        FutureCoordinateMeanZero, Fin.val_zero, zero_add, g, F, Q, ν] using Bound
    have Average := SubGaussianOfOscillation (μ 0) g (c 0)
      ObservableG.aemeasurable OscillationG
    have AverageDistance := distanceFromMeanOfOscillation (μ 0) g (c 0)
      ObservableG.aemeasurable OscillationG
    have AllOscillation (x y : (∀ j, B j) × A 0) :
        |F x - F y| ≤ ((2 * ∑ j : Fin n, c j.succ + c 0 : ℝ≥0) : ℝ) := by
      have Left := (Section x.2).2 x.1
      have Right := (Section y.2).2 y.1
      have Middle := OscillationG x.2 y.2
      change |F x - g x.2| ≤ _ at Left
      change |F y - g y.2| ≤ _ at Right
      rcases abs_le.mp Left with ⟨L₁, L₂⟩
      rcases abs_le.mp Right with ⟨R₁, R₂⟩
      rcases abs_le.mp Middle with ⟨M₁, M₂⟩
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_sum]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have Rough := SubGaussianOfOscillation (Q.prod (μ 0)) F
      (2 * ∑ j : Fin n, c j.succ + c 0) ObservableF.aemeasurable AllOscillation
    have FiniteMean := integrableOfOscillation (Q.prod (μ 0)) F
      (2 * ∑ j : Fin n, c j.succ + c 0) ObservableF.aemeasurable AllOscillation
    have Product := subGaussianProdOfSections Q (μ 0) F
      ((∑ j : Fin n, c j.succ ^ 2) / 4) (c 0 ^ 2 / 4) FiniteMean
      Rough.integrable_exp_mul (fun a => (Section a).1) Average
    have ProductMean : (∫ z, F z ∂Q.prod (μ 0)) = ∫ a, g a ∂μ 0 :=
      integral_prod_symm F FiniteMean
    have Split : MeasurePreserving
        (fun x : ∀ i, A i => ((fun j : Fin n => x j.succ), x 0))
        (Measure.pi μ) (Q.prod (μ 0)) := by
      have Head := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
      change MeasurePreserving
        (fun x : ∀ i, A i => (x 0, fun j : Fin n => x ((0 : Fin (n + 1)).succAbove j)))
        (Measure.pi μ)
        ((μ 0).prod (Measure.pi (fun j : Fin n => μ ((0 : Fin (n + 1)).succAbove j)))) at Head
      simp only [Fin.succAbove_zero] at Head
      exact (Measure.measurePreserving_swap (μ := μ 0) (ν := Q)).comp Head
    have Reconstruct (x : ∀ i, A i) : F ((fun j => x j.succ), x 0) = f x := by
      exact congrArg f (Fin.cons_self_tail x)
    have Mean : (∫ z, F z ∂Q.prod (μ 0)) = ∫ x, f x ∂Measure.pi μ := by
      have Transfer := Split.hasLaw.integral_comp ObservableF.aestronglyMeasurable
      simpa only [Function.comp_def, Reconstruct] using Transfer.symm
    have Mapped : HasSubgaussianMGF (fun z => F z - ∫ w, F w ∂Q.prod (μ 0))
        ((∑ j : Fin n, c j.succ ^ 2) / 4 + c 0 ^ 2 / 4)
        ((Measure.pi μ).map (fun x => ((fun j : Fin n => x j.succ), x 0))) := by
      rw [Split.map_eq]
      exact Product
    have Transfer := HasSubgaussianMGF.of_map Split.measurable.aemeasurable Mapped
    have Parameter : (∑ j : Fin n, c j.succ ^ 2) / 4 + c 0 ^ 2 / 4 =
        (∑ i, c i ^ 2) / 4 := by
      rw [Fin.sum_univ_succ, add_div, add_comm]
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_def, Reconstruct, Mean, Parameter] using Transfer
    · intro x
      have Tail := (Section (x 0)).2 (fun j => x j.succ)
      change |F ((fun j => x j.succ), x 0) - g (x 0)| ≤ _ at Tail
      rw [Reconstruct] at Tail
      have Head := AverageDistance (x 0)
      rw [← ProductMean, Mean] at Head
      calc
        |f x - ∫ y, f y ∂Measure.pi μ| ≤
            |f x - g (x 0)| + |g (x 0) - ∫ y, f y ∂Measure.pi μ| := abs_sub_le _ _ _
        _ ≤ (∑ j : Fin n, (c j.succ : ℝ)) + c 0 := add_le_add Tail Head
        _ = ∑ i, (c i : ℝ) := by rw [Fin.sum_univ_succ, add_comm]

end
end ECTheoryLib.Probability


namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

/-- Genuine future-average widths give the exact centered MGF for independent coordinates. -/
theorem IndependentBoundedConditionalExpectationsSubGaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (X : ∀ i, Ω → A i)
    (ObservableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0) (ObservableF : Measurable f)
    (Coordinate : ∀ i x y, (∀ j, j.val < i.val → x j = y j) →
      |FutureCoordinateMean (fun j => P.map (X j)) f (i.val + 1) x -
        FutureCoordinateMean (fun j => P.map (X j)) f (i.val + 1) y| ≤ (c i : ℝ)) :
    HasSubgaussianMGF
      (fun ω => f (fun i => X i ω) - ∫ w, f (fun i => X i w) ∂P)
      ((∑ i, c i ^ 2) / 4) P := by
  let μ : ∀ i, Measure (A i) := fun i => P.map (X i)
  have Probability (i : Fin n) : IsProbabilityMeasure (μ i) :=
    Measure.isProbabilityMeasure_map (ObservableX i)
  let : ∀ i, IsProbabilityMeasure (μ i) := Probability
  have Joint : HasLaw (fun ω i => X i ω) (Measure.pi μ) P :=
    Independent.hasLaw_pi (fun i => ⟨ObservableX i, rfl⟩)
  have Product := (boundedConditionalExpectationsProduct n A μ f c ObservableF Coordinate).1
  have Mapped : HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Measure.pi μ)
      ((∑ i, c i ^ 2) / 4) (P.map (fun ω i => X i ω)) := by
    rw [Joint.map_eq]
    exact Product
  have Transfer := HasSubgaussianMGF.of_map Joint.aemeasurable Mapped
  have Mean := Joint.integral_comp ObservableF.aestronglyMeasurable
  rw [← Mean] at Transfer
  exact Transfer

/-- Theorem1.10.28 upper closed tail, allowing zero widths and an empty family. -/
theorem IndependentBoundedConditionalExpectationsUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (X : ∀ i, Ω → A i)
    (ObservableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0) (ObservableF : Measurable f)
    (Coordinate : ∀ i x y, (∀ j, j.val < i.val → x j = y j) →
      |FutureCoordinateMean (fun j => P.map (X j)) f (i.val + 1) x -
        FutureCoordinateMean (fun j => P.map (X j)) f (i.val + 1) y| ≤ (c i : ℝ))
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    P.real {ω | (∫ w, f (fun i => X i w) ∂P) + threshold ≤ f (fun i => X i ω)} ≤
      Real.exp (-2 * threshold ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  have Bound := (IndependentBoundedConditionalExpectationsSubGaussian P X ObservableX Independent f c
    ObservableF Coordinate).measure_ge_le Nonnegative
  have Event : {ω | threshold ≤ f (fun i => X i ω) - ∫ w, f (fun i => X i w) ∂P} =
      {ω | (∫ w, f (fun i => X i w) ∂P) + threshold ≤ f (fun i => X i ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  rw [Event, quarterVarianceTailExponent] at Bound
  simpa only [NNReal.coe_sum, NNReal.coe_pow] using Bound

/-- The lower closed tail follows by negating the same centered MGF. -/
theorem IndependentBoundedConditionalExpectationsLowerTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (X : ∀ i, Ω → A i)
    (ObservableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0) (ObservableF : Measurable f)
    (Coordinate : ∀ i x y, (∀ j, j.val < i.val → x j = y j) →
      |FutureCoordinateMean (fun j => P.map (X j)) f (i.val + 1) x -
        FutureCoordinateMean (fun j => P.map (X j)) f (i.val + 1) y| ≤ (c i : ℝ))
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    P.real {ω | f (fun i => X i ω) ≤ (∫ w, f (fun i => X i w) ∂P) - threshold} ≤
      Real.exp (-2 * threshold ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  have Bound := (IndependentBoundedConditionalExpectationsSubGaussian P X ObservableX Independent f c
    ObservableF Coordinate).neg.measure_ge_le Nonnegative
  have Event : {ω | threshold ≤ -(f (fun i => X i ω) - ∫ w, f (fun i => X i w) ∂P)} =
      {ω | f (fun i => X i ω) ≤ (∫ w, f (fun i => X i w) ∂P) - threshold} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  change P.real {ω | threshold ≤ -(f (fun i => X i ω) - ∫ w, f (fun i => X i w) ∂P)} ≤ _ at Bound
  rw [Event, quarterVarianceTailExponent] at Bound
  simpa only [NNReal.coe_sum, NNReal.coe_pow] using Bound

end
end ECTheoryLib.Probability





namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

theorem IndependentBoundedConditionalExpectationsSectionsIntegrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} {A : Fin n → Type*}
    [∀ i, MeasurableSpace (A i)] (X : ∀ i, Ω → A i)
    (ObservableX : ∀ i, AEMeasurable (X i) P) (Independent : iIndepFun X P)
    (f : (∀ i, A i) → ℝ) (c : Fin n → ℝ≥0) (ObservableF : Measurable f)
    (Coordinate : ∀ i x y, (∀ j, j.val < i.val → x j = y j) →
      |FutureCoordinateMean (fun j => P.map (X j)) f (i.val + 1) x -
        FutureCoordinateMean (fun j => P.map (X j)) f (i.val + 1) y| ≤ (c i : ℝ))
    (k : ℕ) (x : ∀ i, A i) :
    Integrable (fun ω => f (fun i => if i.val < k then x i else X i ω)) P := by
  let μ : ∀ i, Measure (A i) := fun i => P.map (X i)
  have Probability (i : Fin n) : IsProbabilityMeasure (μ i) :=
    Measure.isProbabilityMeasure_map (ObservableX i)
  let : ∀ i, IsProbabilityMeasure (μ i) := Probability
  have Joint : HasLaw (fun ω i => X i ω) (Measure.pi μ) P :=
    Independent.hasLaw_pi (fun i => ⟨ObservableX i, rfl⟩)
  have Product := boundedConditionalExpectationsProduct n A μ f c ObservableF Coordinate
  let h : (∀ i, A i) → ℝ := fun y => f (fun i => if i.val < k then x i else y i)
  have ObservableH : Measurable h := by
    apply ObservableF.comp
    apply measurable_pi_lambda
    intro i
    by_cases Before : i.val < k
    · simp only [if_pos Before]
      exact measurable_const
    · simp only [if_neg Before]
      exact measurable_pi_apply i
  have Dominated (y : ∀ i, A i) : ‖h y‖ ≤
      (∑ i, (c i : ℝ)) + |∫ z, f z ∂Measure.pi μ| := by
    have Bound := Product.2 (fun i => if i.val < k then x i else y i)
    change |h y - ∫ z, f z ∂Measure.pi μ| ≤ _ at Bound
    rw [Real.norm_eq_abs]
    calc
      |h y| ≤ |h y - ∫ z, f z ∂Measure.pi μ| + |∫ z, f z ∂Measure.pi μ| := by
        simpa only [sub_zero] using abs_sub_le (h y) (∫ z, f z ∂Measure.pi μ) 0
      _ ≤ _ := add_le_add Bound le_rfl
  have Finite : Integrable h (Measure.pi μ) :=
    (integrable_const ((∑ i, (c i : ℝ)) + |∫ z, f z ∂Measure.pi μ|)).mono'
      ObservableH.aestronglyMeasurable (Filter.Eventually.of_forall Dominated)
  have Mapped : Integrable h (P.map (fun ω i => X i ω)) := by
    rw [Joint.map_eq]
    exact Finite
  exact Mapped.comp_aemeasurable Joint.aemeasurable

end
end ECTheoryLib.Probability

