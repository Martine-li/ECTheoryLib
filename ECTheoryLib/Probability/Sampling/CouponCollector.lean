import ECTheoryLib.Probability.HittingTimes.Expectation
import Mathlib.Probability.Distributions.Uniform

/-!
# Uniform coupon collection with replacement

A Boolean record retains previously collected coupons. Each transition
records a fresh uniform coupon. The empty universe is already complete.
-/

namespace ECTheoryLib.Probability.CouponCollector
open MeasureTheory
noncomputable section

/-- A true coordinate records that its coupon has already been collected. -/
abbrev State (n : ℕ) := Fin n → Bool

def Empty (n : ℕ) : State n := fun _ => false

def Complete {n : ℕ} (x : State n) : Prop := ∀ i, x i=true

/-- Drawing a previously collected coupon leaves the record unchanged. -/
def Collect {n : ℕ} (x : State n) (i : Fin n) : State n :=
  fun j => if j=i then true else x j

@[simp] theorem CollectAt {n : ℕ} (x : State n) (i : Fin n) : Collect x i i=true := by
  simp [Collect]

theorem CollectAway {n : ℕ} (x : State n) (i j : Fin n) (Different : j≠i) : Collect x i j=x j := by
  simp [Collect,Different]

/-- A fresh uniform coupon is recorded at each transition. With no coupon
types the unique state stays fixed and is already complete. -/
def Step (n : ℕ) : Transition (State n) := fun x => by
  classical
  by_cases Positive : 0<n
  · let : Nonempty (Fin n) := ⟨⟨0,Positive⟩⟩
    exact (PMF.uniformOfFintype (Fin n)).map (Collect x)
  · exact PMF.pure x

def ExpectedDraws (n : ℕ) : ENNReal := ExpectedHittingTime (Step n) Complete (PMF.pure (Empty n))

end
end ECTheoryLib.Probability.CouponCollector
