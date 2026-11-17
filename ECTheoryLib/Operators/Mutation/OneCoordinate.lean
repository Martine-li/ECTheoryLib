import ECTheoryLib.SearchSpaces.MultiValue
import Mathlib.Data.Fintype.Card
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Uniform replacement of one coordinate

A complete choice consists of a coordinate and a replacement different from its
current value. Uniform sampling of the `n(r-1)` choices is equivalent to uniform
coordinate selection followed by uniform selection among its `r-1` alternatives.
Sampling requires positive length and at least two alphabet values.
-/

open MeasureTheory
open scoped ENNReal

namespace ECTheoryLib

/-- A coordinate together with a replacement distinct from its current value. -/
abbrev CoordinateChoice {n r : Nat} (State : MultiValues n r) :=
  (i : Fin n) × {v : Fin r // v ≠ State i}

/-- The finite dependent choice space has the discrete measurable structure. -/
instance CoordinateChoiceDiscrete {n r : Nat} (State : MultiValues n r) :
    DiscreteMeasurableSpace (CoordinateChoice State) where
  forall_measurableSet s := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro i
    exact (Set.to_countable ((Sigma.mk i) ⁻¹' s)).measurableSet

/-- Exactly `r-1` alphabet values differ from a fixed current value. -/
theorem OtherCoordinateValuesCard {r : Nat} (Current : Fin r) :
    Fintype.card {v : Fin r // v ≠ Current} = r - 1 := by
  rw [Fintype.card_subtype_compl (fun v : Fin r => v = Current)]
  rw [Fintype.card_fin, Fintype.card_subtype_eq]

/-- There are `n(r-1)` complete coordinate-and-replacement choices. -/
theorem CoordinateChoiceCard {n r : Nat} (State : MultiValues n r) :
    Fintype.card (CoordinateChoice State) = n * (r - 1) := by
  unfold CoordinateChoice
  rw [Fintype.card_sigma]
  simp only [OtherCoordinateValuesCard, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rfl

/-- Positive length and at least two alphabet values provide a legal replacement. -/
theorem CoordinateChoiceNonempty {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetAtLeastTwo : 2 ≤ r) (State : MultiValues n r) :
    Nonempty (CoordinateChoice State) := by
  apply Fintype.card_pos_iff.mp
  rw [CoordinateChoiceCard]
  exact Nat.mul_pos PositiveLength (by omega)

/-- Replace the chosen coordinate by the specified different value. -/
def OneCoordinateMutation {n r : Nat} (State : MultiValues n r)
    (Choice : CoordinateChoice State) : MultiValues n r :=
  Function.update State Choice.1 Choice.2.val

/-- The chosen coordinate receives the replacement value. -/
theorem OneCoordinateMutationAtChoice {n r : Nat} (State : MultiValues n r)
    (Choice : CoordinateChoice State) :
    OneCoordinateMutation State Choice Choice.1 = Choice.2.val := by
  exact Function.update_self Choice.1 Choice.2.val State

/-- Every unchosen coordinate is unchanged. -/
theorem OneCoordinateMutationAway {n r : Nat} (State : MultiValues n r)
    (Choice : CoordinateChoice State) (j : Fin n) (Different : j ≠ Choice.1) :
    OneCoordinateMutation State Choice j = State j := by
  exact Function.update_of_ne Different Choice.2.val State

noncomputable section

/-- Uniform sampling of complete legal coordinate-and-replacement choices. -/
def UniformCoordinateChoice {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetAtLeastTwo : 2 ≤ r) (State : MultiValues n r) :
    PMF (CoordinateChoice State) := by
  letI : Nonempty (CoordinateChoice State) :=
    CoordinateChoiceNonempty PositiveLength AlphabetAtLeastTwo State
  exact PMF.uniformOfFintype (CoordinateChoice State)

/-- Every complete choice has probability `1/(n(r-1))`. -/
@[simp] theorem UniformCoordinateChoiceProbability {n r : Nat}
    (PositiveLength : 0 < n) (AlphabetAtLeastTwo : 2 ≤ r)
    (State : MultiValues n r) (Choice : CoordinateChoice State) :
    UniformCoordinateChoice PositiveLength AlphabetAtLeastTwo State Choice =
      ((n * (r - 1) : Nat) : ENNReal)⁻¹ := by
  let : Nonempty (CoordinateChoice State) := ⟨Choice⟩
  unfold UniformCoordinateChoice
  rw [PMF.uniformOfFintype_apply, CoordinateChoiceCard]

/-- Joint choice probabilities factor into the uniform coordinate probability
and the uniform probability of a different replacement value. -/
theorem UniformCoordinateChoiceProbabilityFactorized {n r : Nat}
    (PositiveLength : 0 < n) (AlphabetAtLeastTwo : 2 ≤ r)
    (State : MultiValues n r) (Choice : CoordinateChoice State) :
    UniformCoordinateChoice PositiveLength AlphabetAtLeastTwo State Choice =
      (n : ENNReal)⁻¹ * ((r - 1 : Nat) : ENNReal)⁻¹ := by
  rw [UniformCoordinateChoiceProbability, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]

/-- Integration over the uniform choice law equals the equally weighted finite sum. -/
theorem UniformCoordinateChoiceIntegral {n r : Nat}
    (PositiveLength : 0 < n) (AlphabetAtLeastTwo : 2 ≤ r)
    (State : MultiValues n r) (f : CoordinateChoice State → ℝ) :
    (∫ Choice, f Choice ∂(UniformCoordinateChoice PositiveLength
      AlphabetAtLeastTwo State).toMeasure) =
      (1 / ((n * (r - 1) : Nat) : ℝ)) * ∑ Choice, f Choice := by
  rw [PMF.integral_eq_sum]
  simp only [UniformCoordinateChoiceProbability, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]
  rw [one_div]

end
end ECTheoryLib
