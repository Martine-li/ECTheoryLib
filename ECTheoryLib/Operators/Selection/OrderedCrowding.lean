import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Tactic

/-!
# Crowding contributions on an ordered objective sequence

An objective contribution is infinite at the first and last positions, and is
the normalized neighboring gap internally. For a nondecreasing objective
sequence, every contribution is nonnegative. Only the first and last occurrence
of each distinct objective value can have positive contribution; every value
has at least one such occurrence. These statements retain repeated values.

This isolates the ordered-block argument used in Zheng and Doerr (2023),
arXiv:2112.08581v7, Lemma 1. A constant objective has zero internal contribution
under total rational division, while boundary contributions remain infinite.
-/
namespace ECTheoryLib.Operators.Selection
noncomputable section

/-- Contribution at a sequence position. Values outside 0,...,Length-1 do not
matter when Position is valid. Boundary positions have infinite contribution. -/
def OrderedCrowding (Length : ℕ) (Value : ℕ → ℚ) (Position : ℕ) : WithTop ℚ :=
  if Position = 0 ∨ Position + 1 ≥ Length then ⊤
  else ((Value (Position + 1) - Value (Position - 1)) /
    (Value (Length - 1) - Value 0) : ℚ)

/-- Objective values are nondecreasing on the valid positions only. -/
def OrderedValues (Length : ℕ) (Value : ℕ → ℚ) : Prop :=
  ∀ a b, a ≤ b → b < Length → Value a ≤ Value b

/-- All normalized gaps in a sorted objective are nonnegative, even when the
entire objective range is zero. -/
theorem OrderedCrowdingNonnegative {Length : ℕ} {Value : ℕ → ℚ}
    (Ordered : OrderedValues Length Value) (i : ℕ) :
    0 ≤ OrderedCrowding Length Value i := by
  unfold OrderedCrowding
  split_ifs with Boundary
  · exact le_top
  · apply WithTop.coe_le_coe.mpr
    exact div_nonneg (sub_nonneg.mpr (Ordered _ _ (by omega) (by omega)))
      (sub_nonneg.mpr (Ordered _ _ (by omega) (by omega)))

/-- An occurrence strictly inside the block of equal objective values has zero
contribution, independent of the other objective or the survivor tie permutation. -/
theorem OrderedCrowdingZeroBetween {Length : ℕ} {Value : ℕ → ℚ}
    (Ordered : OrderedValues Length Value) {a i b : ℕ}
    (Left : a < i) (Right : i < b) (Last : b < Length)
    (SameLeft : Value a = Value i) (SameRight : Value b = Value i) :
    OrderedCrowding Length Value i = 0 := by
  have Previous : Value (i - 1) = Value i := by
    have Lower := Ordered a (i - 1) (by omega) (by omega)
    have Upper := Ordered (i - 1) i (by omega) (by omega)
    linarith
  have Next : Value (i + 1) = Value i := by
    have Lower := Ordered i (i + 1) (by omega) (by omega)
    have Upper := Ordered (i + 1) b (by omega) Last
    linarith
  unfold OrderedCrowding
  rw [if_neg (by omega), Previous, Next, sub_self, zero_div]
  rfl

/-- The first occurrence of every represented value has positive contribution.
If it is not a sequence boundary, a strict left gap makes the normalized ratio
positive; that same gap also proves the objective range is nonzero. -/
theorem OrderedCrowdingPositiveFirst {Length : ℕ} {Value : ℕ → ℚ}
    (Ordered : OrderedValues Length Value) (i : ℕ) (Valid : i < Length)
    (First : ∀ j < i, Value j ≠ Value i) : 0 < OrderedCrowding Length Value i := by
  unfold OrderedCrowding
  split_ifs with Boundary
  · exact WithTop.coe_lt_top 0
  · have PreviousLe := Ordered (i - 1) i (by omega) Valid
    have PreviousStrict : Value (i - 1) < Value i :=
      lt_of_le_of_ne PreviousLe (First (i - 1) (by omega))
    have NextLe := Ordered i (i + 1) (by omega) (by omega)
    have FirstLe := Ordered 0 (i - 1) (by omega) (by omega)
    have LastLe := Ordered i (Length - 1) (by omega) (by omega)
    apply WithTop.coe_lt_coe.mpr
    exact div_pos (by linarith) (by linarith)

/-- All distinct objective values appearing in the finite sequence. -/
def OrderedDistinctValues (Length : ℕ) (Value : ℕ → ℚ) : Finset ℚ :=
  (Finset.range Length).image Value

/-- Positions with a specified objective value. -/
def OrderedValuePositions (Length : ℕ) (Value : ℕ → ℚ) (q : ℚ) : Finset ℕ :=
  (Finset.range Length).filter (fun i => Value i = q)

/-- Every represented value has at least one position. -/
theorem OrderedValuePositionsNonempty (Length : ℕ) (Value : ℕ → ℚ)
    (q : {q // q ∈ OrderedDistinctValues Length Value}) :
    (OrderedValuePositions Length Value q.val).Nonempty := by
  obtain ⟨i, InRange, Equal⟩ := Finset.mem_image.mp q.property
  exact ⟨i, Finset.mem_filter.mpr ⟨InRange, Equal⟩⟩

/-- First occurrence of a represented objective value. -/
def OrderedFirstPosition (Length : ℕ) (Value : ℕ → ℚ)
    (q : {q // q ∈ OrderedDistinctValues Length Value}) : ℕ :=
  (OrderedValuePositions Length Value q.val).min' (OrderedValuePositionsNonempty Length Value q)

/-- Last occurrence of a represented objective value. -/
def OrderedLastPosition (Length : ℕ) (Value : ℕ → ℚ)
    (q : {q // q ∈ OrderedDistinctValues Length Value}) : ℕ :=
  (OrderedValuePositions Length Value q.val).max' (OrderedValuePositionsNonempty Length Value q)

/-- Candidate positive positions: first and last occurrences of each represented value. -/
def OrderedBoundaryPositions (Length : ℕ) (Value : ℕ → ℚ) : Finset ℕ :=
  ((OrderedDistinctValues Length Value).attach.image (OrderedFirstPosition Length Value)) ∪
    ((OrderedDistinctValues Length Value).attach.image (OrderedLastPosition Length Value))

/-- There are at most two candidate positive positions per distinct objective value. -/
theorem OrderedBoundaryCard (Length : ℕ) (Value : ℕ → ℚ) :
    (OrderedBoundaryPositions Length Value).card ≤ 2 * (OrderedDistinctValues Length Value).card := by
  apply (Finset.card_union_le _ _).trans
  have First := Finset.card_image_le (s := (OrderedDistinctValues Length Value).attach)
    (f := OrderedFirstPosition Length Value)
  have Last := Finset.card_image_le (s := (OrderedDistinctValues Length Value).attach)
    (f := OrderedLastPosition Length Value)
  simp only [Finset.card_attach] at First Last
  omega

/-- Every positive contribution occurs at a represented value's first or last
position. Interior equal-value occurrences contribute zero and cannot be selected
as positive-distance witnesses by this argument. -/
theorem OrderedCrowdingPositiveBoundary {Length : ℕ} {Value : ℕ → ℚ}
    (Ordered : OrderedValues Length Value) (i : ℕ) (Valid : i < Length)
    (Positive : 0 < OrderedCrowding Length Value i) :
    i ∈ OrderedBoundaryPositions Length Value := by
  let q : {q // q ∈ OrderedDistinctValues Length Value} :=
    ⟨Value i, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr Valid, rfl⟩⟩
  have AtPosition : i ∈ OrderedValuePositions Length Value q.val :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr Valid, rfl⟩
  have FirstMember := Finset.min'_mem (OrderedValuePositions Length Value q.val)
    (OrderedValuePositionsNonempty Length Value q)
  have LastMember := Finset.max'_mem (OrderedValuePositions Length Value q.val)
    (OrderedValuePositionsNonempty Length Value q)
  have FirstLe : OrderedFirstPosition Length Value q ≤ i :=
    Finset.min'_le _ _ AtPosition
  have LastLe : i ≤ OrderedLastPosition Length Value q := Finset.le_max' _ _ AtPosition
  by_cases First : i = OrderedFirstPosition Length Value q
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, First.symm⟩
  by_cases Last : i = OrderedLastPosition Length Value q
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, Last.symm⟩
  have FirstInfo := Finset.mem_filter.mp FirstMember
  have LastInfo := Finset.mem_filter.mp LastMember
  have Zero := OrderedCrowdingZeroBetween Ordered
    (lt_of_le_of_ne FirstLe (Ne.symm First)) (lt_of_le_of_ne LastLe Last)
    (Finset.mem_range.mp LastInfo.1) FirstInfo.2 LastInfo.2
  exact False.elim (Positive.ne' Zero)

/-- Every represented value has a valid positive-contribution occurrence. -/
theorem OrderedValuePositiveWitness {Length : ℕ} {Value : ℕ → ℚ}
    (Ordered : OrderedValues Length Value)
    (q : {q // q ∈ OrderedDistinctValues Length Value}) :
    ∃ i < Length, Value i = q.val ∧ 0 < OrderedCrowding Length Value i := by
  let i := OrderedFirstPosition Length Value q
  have Member := Finset.min'_mem (OrderedValuePositions Length Value q.val)
    (OrderedValuePositionsNonempty Length Value q)
  have Info := Finset.mem_filter.mp Member
  refine ⟨i, Finset.mem_range.mp Info.1, Info.2, ?_⟩
  apply OrderedCrowdingPositiveFirst Ordered i (Finset.mem_range.mp Info.1)
  intro j Earlier Equal
  have JMember : j ∈ OrderedValuePositions Length Value q.val :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans Earlier (Finset.mem_range.mp Info.1)),
      Equal.trans Info.2⟩
  have Lower : i ≤ j := Finset.min'_le _ _ JMember
  omega

end
end ECTheoryLib.Operators.Selection
