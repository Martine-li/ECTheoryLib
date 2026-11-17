import ECTheoryLib.Operators.Selection.CrowdingDistance
import Mathlib.Data.List.MinMax
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Linarith

/-!
# Exact NSGA-III normalization with historical state

Source: Wietheger–Doerr, arXiv:2211.08202, Algorithm 2 and its preceding prose,
the revised Blank–Deb–Roy normalization.  Shared library objectives are maximized,
so normalization first negates each coordinate to use the paper's minimization
orientation. Historical ideal minima, worst maxima and previous extreme vectors
are explicit state. ASF ties use first occurrence order, as the source leaves
that tie rule unspecified.

Hyperplane coefficients are computed over rational numbers by adjugate/determinant,
not by a supplied normalization callback. Invalid intercepts use first-front
coordinate maxima; near-zero gaps use maxima over the retained fronts. A constant
coordinate is normalized to zero. Both numerical thresholds are explicit inputs.
The apparent reversed validity conditional in the PDF pseudocode is interpreted
according to the surrounding prose: positive intercepts within the historical
worst bounds are valid.
-/

namespace ECTheoryLib.Operators.Selection

/-- A finite rational objective vector used for exact normalization arithmetic. -/
abbrev ObjectiveVector (m : Nat) := Fin m → ℚ

/-- Positive rational thresholds: ASFEpsilon weights nonselected objectives in achievement scalarization, and NadirEpsilon controls intercept validity and near-zero normalization gaps. -/
structure NSGAIIINormalizationParameters where
  ASFEpsilon : ℚ
  NadirEpsilon : ℚ
  ASFPositive : 0 < ASFEpsilon
  NadirPositive : 0 < NadirEpsilon

/-- Default positive thresholds, both equal to one millionth. Alternative thresholds can be supplied explicitly. -/
def DefaultNSGAIIINormalizationParameters : NSGAIIINormalizationParameters where
  ASFEpsilon := 1 / 1000000
  NadirEpsilon := 1 / 1000000
  ASFPositive := by norm_num
  NadirPositive := by norm_num

/-- Historical coordinate minima (Ideal), maxima (Worst), and previously selected extreme vectors, in minimization orientation. The fields themselves impose no reachability invariant. -/
structure NSGAIIIHistory (m : Nat) where
  Ideal : ObjectiveVector m
  Worst : ObjectiveVector m
  Extremes : List (ObjectiveVector m)

/-- Negate every maximization objective to obtain the minimization orientation used by normalization. -/
def MinimizationVector {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (x : α) : ObjectiveVector m := fun i => -Fitness x i

/-- Coordinatewise envelope, seeded by an actually observed vector at initialization. -/
def CoordinateMinimum {m : Nat} (Seed : ObjectiveVector m) :
    List (ObjectiveVector m) → ObjectiveVector m
  | [] => Seed
  | v :: Rest => CoordinateMinimum (fun i => min (Seed i) (v i)) Rest

/-- Coordinatewise maximum of the seed and all supplied vectors; the empty list returns the seed. -/
def CoordinateMaximum {m : Nat} (Seed : ObjectiveVector m) :
    List (ObjectiveVector m) → ObjectiveVector m
  | [] => Seed
  | v :: Rest => CoordinateMaximum (fun i => max (Seed i) (v i)) Rest

theorem CoordinateMinimumLeSeed {m : Nat} (Seed : ObjectiveVector m)
    (Vectors : List (ObjectiveVector m)) (i : Fin m) :
    CoordinateMinimum Seed Vectors i ≤ Seed i := by
  induction Vectors generalizing Seed with
  | nil => exact le_rfl
  | cons v Rest Previous =>
      exact (Previous (fun j => min (Seed j) (v j))).trans (min_le_left _ _)

theorem CoordinateMaximumGeSeed {m : Nat} (Seed : ObjectiveVector m)
    (Vectors : List (ObjectiveVector m)) (i : Fin m) :
    Seed i ≤ CoordinateMaximum Seed Vectors i := by
  induction Vectors generalizing Seed with
  | nil => exact le_rfl
  | cons v Rest Previous =>
      exact (le_max_left _ _).trans (Previous (fun j => max (Seed j) (v j)))

theorem CoordinateMinimumLeMember {m : Nat} (Seed : ObjectiveVector m)
    (Vectors : List (ObjectiveVector m)) (v : ObjectiveVector m)
    (InVectors : v ∈ Vectors) (i : Fin m) : CoordinateMinimum Seed Vectors i ≤ v i := by
  induction Vectors generalizing Seed with
  | nil => exact False.elim (List.not_mem_nil InVectors)
  | cons w Rest Previous =>
      obtain AtHead | InRest := List.mem_cons.mp InVectors
      · rw [AtHead]
        exact (CoordinateMinimumLeSeed (fun j => min (Seed j) (w j)) Rest i).trans
          (min_le_right _ _)
      · exact Previous (fun j => min (Seed j) (w j)) InRest

theorem CoordinateMaximumGeMember {m : Nat} (Seed : ObjectiveVector m)
    (Vectors : List (ObjectiveVector m)) (v : ObjectiveVector m)
    (InVectors : v ∈ Vectors) (i : Fin m) : v i ≤ CoordinateMaximum Seed Vectors i := by
  induction Vectors generalizing Seed with
  | nil => exact False.elim (List.not_mem_nil InVectors)
  | cons w Rest Previous =>
      obtain AtHead | InRest := List.mem_cons.mp InVectors
      · rw [AtHead]
        exact (le_max_right _ _).trans
          (CoordinateMaximumGeSeed (fun j => max (Seed j) (w j)) Rest i)
      · exact Previous (fun j => max (Seed j) (w j)) InRest

/-- Use the first observed vector as the coordinate-envelope seed, or the zero vector when the list is empty. -/
def ObjectiveSeed {m : Nat} (Vectors : List (ObjectiveVector m)) : ObjectiveVector m :=
  Vectors.head?.getD (fun _ => 0)

/-- Initialize ideal and worst coordinates from the current population in minimization orientation, with no previous extreme vectors. An empty population uses the zero seed. -/
def NSGAIIIInitialHistory {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) : NSGAIIIHistory m :=
  let Vectors := Pool.map (MinimizationVector Fitness)
  { Ideal := CoordinateMinimum (ObjectiveSeed Vectors) Vectors
    Worst := CoordinateMaximum (ObjectiveSeed Vectors) Vectors
    Extremes := [] }

/-- Every generated objective is observed, including offspring later discarded. -/
def NSGAIIIObserve {m : Nat} (History : NSGAIIIHistory m)
    (Observed : List (ObjectiveVector m)) : NSGAIIIHistory m :=
  { Ideal := CoordinateMinimum History.Ideal Observed
    Worst := CoordinateMaximum History.Worst Observed
    Extremes := History.Extremes }

theorem NSGAIIIObserveIdeal {m : Nat} (History : NSGAIIIHistory m)
    (Observed : List (ObjectiveVector m)) (i : Fin m) :
    (NSGAIIIObserve History Observed).Ideal i ≤ History.Ideal i := by
  exact CoordinateMinimumLeSeed _ _ i

theorem NSGAIIIObserveWorst {m : Nat} (History : NSGAIIIHistory m)
    (Observed : List (ObjectiveVector m)) (i : Fin m) :
    History.Worst i ≤ (NSGAIIIObserve History Observed).Worst i := by
  exact CoordinateMaximumGeSeed _ _ i

/-- Maximum weighted deviation from the ideal point, folded with lower bound zero. The selected objective has weight one and other coordinates have the positive ASF epsilon. -/
def AchievementScalarization {m : Nat} (Parameters : NSGAIIINormalizationParameters)
    (Ideal : ObjectiveVector m) (Objective : Fin m) (v : ObjectiveVector m) : ℚ :=
  (List.ofFn (fun i : Fin m =>
    (v i - Ideal i) / (if i = Objective then 1 else Parameters.ASFEpsilon))).foldl max 0

/-- For each objective, minimize achievement scalarization over retained vectors and previous extremes. Ties use the first occurrence; an empty candidate list uses the retained-vector seed. -/
def NSGAIIIExtremeVectors {m : Nat} (Parameters : NSGAIIINormalizationParameters)
    (History : NSGAIIIHistory m) (Retained : List (ObjectiveVector m)) :
    Fin m → ObjectiveVector m := fun i =>
  ((Retained ++ History.Extremes).argmin (AchievementScalarization Parameters History.Ideal i)).getD
    (ObjectiveSeed Retained)

/-- Matrix of extreme vectors translated by the ideal point, with one selected extreme per row. -/
def NSGAIIIExtremeMatrix {m : Nat} (Ideal : ObjectiveVector m)
    (Extreme : Fin m → ObjectiveVector m) : Matrix (Fin m) (Fin m) ℚ :=
  fun i j => Extreme i j - Ideal j

/-- Adjugate/determinant formula for the hyperplane coefficients. It solves M*c=1 when the determinant is nonzero; valid nonzero coefficients give translated intercepts 1/c_i. Singular inputs use total rational division and are rejected by NSGAIIIHyperplaneValid. -/
def NSGAIIIHyperplaneCoefficients {m : Nat} (M : Matrix (Fin m) (Fin m) ℚ) :
    ObjectiveVector m := fun i => (∑ j : Fin m, Matrix.adjugate M i j) / Matrix.det M

/-- Candidate nadir obtained by adding reciprocal hyperplane coefficients to the ideal point. The total rational formula is used only as a valid intercept construction after NSGAIIIHyperplaneValid is checked. -/
def NSGAIIIHyperplaneNadir {m : Nat} (Ideal : ObjectiveVector m)
    (M : Matrix (Fin m) (Fin m) ℚ) : ObjectiveVector m :=
  fun i => Ideal i + 1 / NSGAIIIHyperplaneCoefficients M i

/-- Require an invertible extreme matrix, nonzero coefficients, translated intercepts at least NadirEpsilon, and a candidate nadir within historical worst coordinates. -/
def NSGAIIIHyperplaneValid {m : Nat} (Parameters : NSGAIIINormalizationParameters)
    (History : NSGAIIIHistory m) (M : Matrix (Fin m) (Fin m) ℚ) : Prop :=
  Matrix.det M ≠ 0 ∧ ∀ i : Fin m,
    NSGAIIIHyperplaneCoefficients M i ≠ 0 ∧
    Parameters.NadirEpsilon ≤ 1 / NSGAIIIHyperplaneCoefficients M i ∧
    NSGAIIIHyperplaneNadir History.Ideal M i ≤ History.Worst i

instance {m : Nat} (Parameters : NSGAIIINormalizationParameters)
    (History : NSGAIIIHistory m) (M : Matrix (Fin m) (Fin m) ℚ) :
    Decidable (NSGAIIIHyperplaneValid Parameters History M) := by
  unfold NSGAIIIHyperplaneValid
  infer_instance

/-- Updated historical state together with the nadir used for the current normalization. The nadir may come from valid hyperplane intercepts or the documented fallback. -/
structure NSGAIIINormalizationResult (m : Nat) where
  History : NSGAIIIHistory m
  Nadir : ObjectiveVector m

/-- Actual revised normalization. `Retained` is all complete fronts plus the
splitting front; `FirstFront` is the first nondominated front. -/
def NSGAIIINormalize {m : Nat} (Parameters : NSGAIIINormalizationParameters)
    (History : NSGAIIIHistory m) (Observed Retained FirstFront : List (ObjectiveVector m)) :
    NSGAIIINormalizationResult m :=
  let Updated := NSGAIIIObserve History Observed
  let Extreme := NSGAIIIExtremeVectors Parameters Updated Retained
  let M := NSGAIIIExtremeMatrix Updated.Ideal Extreme
  let CandidateNadir :=
    if NSGAIIIHyperplaneValid Parameters Updated M then NSGAIIIHyperplaneNadir Updated.Ideal M
    else CoordinateMaximum (ObjectiveSeed FirstFront) FirstFront
  let RetainedMaximum := CoordinateMaximum (ObjectiveSeed Retained) Retained
  { History := { Updated with Extremes := List.ofFn Extreme }
    Nadir := fun i =>
      if CandidateNadir i < Updated.Ideal i + Parameters.NadirEpsilon then RetainedMaximum i
      else CandidateNadir i }

/-- Translate by the historical ideal and divide by the nadir gap coordinatewise. A zero gap yields zero, explicitly handling constant objective coordinates. -/
def NSGAIIINormalizedVector {m : Nat} (Normalization : NSGAIIINormalizationResult m)
    (v : ObjectiveVector m) : ObjectiveVector m := fun i =>
  if Normalization.Nadir i = Normalization.History.Ideal i then 0
  else (v i - Normalization.History.Ideal i) /
    (Normalization.Nadir i - Normalization.History.Ideal i)

theorem NSGAIIINormalizeIdeal {m : Nat} (Parameters : NSGAIIINormalizationParameters)
    (History : NSGAIIIHistory m) (Observed Retained FirstFront : List (ObjectiveVector m))
    (i : Fin m) :
    (NSGAIIINormalize Parameters History Observed Retained FirstFront).History.Ideal i ≤
      History.Ideal i := by
  exact NSGAIIIObserveIdeal History Observed i

theorem NSGAIIINormalizeWorst {m : Nat} (Parameters : NSGAIIINormalizationParameters)
    (History : NSGAIIIHistory m) (Observed Retained FirstFront : List (ObjectiveVector m))
    (i : Fin m) : History.Worst i ≤
    (NSGAIIINormalize Parameters History Observed Retained FirstFront).History.Worst i := by
  exact NSGAIIIObserveWorst History Observed i

theorem NSGAIIINormalizeExtremeCount {m : Nat} (Parameters : NSGAIIINormalizationParameters)
    (History : NSGAIIIHistory m) (Observed Retained FirstFront : List (ObjectiveVector m)) :
    (NSGAIIINormalize Parameters History Observed Retained FirstFront).History.Extremes.length = m := by
  exact List.length_ofFn

end ECTheoryLib.Operators.Selection
