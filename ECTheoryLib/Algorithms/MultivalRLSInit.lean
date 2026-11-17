import ECTheoryLib.Algorithms.MultivalRLS
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Uniform initialization of multi-valued RLS

For a nonempty alphabet, initialize uniformly among all `r^n` vectors. The product
measure theorem identifies this law with independent uniform coordinates, including
the length-zero case. Initialization is independent of later mutation choices.
-/

namespace ECTheoryLib

open MeasureTheory

noncomputable section

/-- Uniform time-zero sampling among all `r^n` vectors. -/
def MultivalRLSInit (n r : Nat) (PositiveAlphabet : 0 < r) : PMF (MultiValues n r) :=
  letI := MultiValuesNonempty n r PositiveAlphabet
  PMF.uniformOfFintype (MultiValues n r)

theorem MultivalRLSInitProbability {n r : Nat} (PositiveAlphabet : 0 < r)
    (State : MultiValues n r) :
    MultivalRLSInit n r PositiveAlphabet State = ((r : ENNReal) ^ n)⁻¹ := by
  simp only [MultivalRLSInit, PMF.uniformOfFintype_apply, MultiValuesCard, Nat.cast_pow]

/-- Uniform sampling of one value from a nonempty alphabet. -/
def UniformValue (r : Nat) (PositiveAlphabet : 0 < r) : PMF (Fin r) :=
  letI : NeZero r := ⟨Nat.ne_of_gt PositiveAlphabet⟩
  PMF.uniformOfFintype (Fin r)

theorem UniformValueProbability {r : Nat} (PositiveAlphabet : 0 < r) (v : Fin r) :
    UniformValue r PositiveAlphabet v = (r : ENNReal)⁻¹ := by
  simp only [UniformValue, PMF.uniformOfFintype_apply, Fintype.card_fin]

/-- Uniform whole-vector initialization equals the product of uniform coordinate laws. -/
theorem MultivalRLSInitProduct (n r : Nat) (PositiveAlphabet : 0 < r) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure =
      Measure.pi (fun _ : Fin n => (UniformValue r PositiveAlphabet).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.pi_singleton]
  simp only [MultivalRLSInitProbability, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _), UniformValueProbability,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.inv_pow]

end
end ECTheoryLib

